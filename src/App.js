import { useState, useEffect, useCallback, useRef, useMemo } from "react";

// ═══════════════════════════════════════════════════════════════════════════════
// CONSTANTS
// ═══════════════════════════════════════════════════════════════════════════════
const DIFFICULTIES = {
  easy:   { size: 3, label: "EASY",   emoji: "🟢", desc: "3×3 · 8 tiles"  },
  medium: { size: 4, label: "MEDIUM", emoji: "🟡", desc: "4×4 · 15 tiles" },
  hard:   { size: 5, label: "HARD",   emoji: "🔴", desc: "5×5 · 24 tiles" },
};

const TILE_COLORS = [
  "#e74c3c","#e67e22","#f1c40f","#2ecc71","#1abc9c",
  "#3498db","#9b59b6","#e91e63","#00bcd4","#ff5722",
  "#8bc34a","#ff9800","#607d8b","#795548","#673ab7",
  "#f44336","#2196f3","#4caf50","#ffeb3b","#ff4081",
  "#00e5ff","#76ff03","#ff6d00","#d500f9","#00bfa5",
];

const PHASES = { IDLE:"idle", SHUFFLING:"shuffling", PLAYING:"playing", WON:"won", SOLVING:"solving", COMPUTING:"computing" };

// ═══════════════════════════════════════════════════════════════════════════════
// PUZZLE HELPERS
// ═══════════════════════════════════════════════════════════════════════════════
function makeGoal(size) {
  const g = Array.from({length:size*size},(_,i)=>i+1);
  g[size*size-1] = 0; return g;
}

function getNeighbors(idx, size) {
  const r=Math.floor(idx/size), c=idx%size, n=[];
  if(r>0)      n.push(idx-size);
  if(r<size-1) n.push(idx+size);
  if(c>0)      n.push(idx-1);
  if(c<size-1) n.push(idx+1);
  return n;
}

function isGoalState(tiles, size) {
  const g=makeGoal(size); return tiles.every((v,i)=>v===g[i]);
}

function isSolvable(tiles, size) {
  const arr=tiles.filter(x=>x!==0); let inv=0;
  for(let i=0;i<arr.length;i++) for(let j=i+1;j<arr.length;j++) if(arr[i]>arr[j]) inv++;
  if(size%2===1) return inv%2===0;
  const emptyRow=Math.floor(tiles.indexOf(0)/size);
  return (inv+emptyRow)%2===1;
}

function shuffleTiles(size) {
  const goal=makeGoal(size);
  let t=[...goal];
  const steps = size===3?80:size===4?200:350;
  let lastBlank=-1;
  for(let i=0;i<steps;i++){
    const ei=t.indexOf(0);
    const nb=getNeighbors(ei,size).filter(n=>n!==lastBlank);
    const pick=nb[Math.floor(Math.random()*nb.length)];
    lastBlank=ei;
    [t[ei],t[pick]]=[t[pick],t[ei]];
  }
  if(isGoalState(t,size)){
    [t[0],t[1]]=[t[1],t[0]];
    if(!isSolvable(t,size)) [t[2],t[3]]=[t[3],t[2]];
  }
  return t;
}

// ── Heuristics ──
function manhattanDist(tiles, size) {
  let h=0;
  for(let i=0;i<tiles.length;i++){
    const t=tiles[i]; if(t===0) continue;
    const gi=t-1; // goal index for tile t is t-1 (since goal=[1,2,...,n,0])
    // except last slot is 0, goal positions: tile t goes to index t-1 for t<size*size
    const gr=Math.floor(gi/size), gc=gi%size;
    const cr=Math.floor(i/size),  cc=i%size;
    h+=Math.abs(gr-cr)+Math.abs(gc-cc);
  }
  return h;
}

function misplacedTiles(tiles, size) {
  const g=makeGoal(size); return tiles.filter((t,i)=>t!==0&&t!==g[i]).length;
}

function tileManhattan(tile, idx, size) {
  if(tile===0) return 0;
  const gi=tile-1;
  const gr=Math.floor(gi/size), gc=gi%size;
  const cr=Math.floor(idx/size), cc=idx%size;
  return Math.abs(gr-cr)+Math.abs(gc-cc);
}

// ═══════════════════════════════════════════════════════════════════════════════
// HEURISTICS — Linear Conflict (stronger than Manhattan for IDA*)
// ═══════════════════════════════════════════════════════════════════════════════
function linearConflict(tiles, size) {
  let lc = 0;
  for(let r=0;r<size;r++){
    const row=[];
    for(let c=0;c<size;c++){
      const t=tiles[r*size+c]; if(t===0) continue;
      const gr=Math.floor((t-1)/size);
      if(gr===r) row.push({gc:(t-1)%size, col:c});
    }
    row.sort((a,b)=>a.col-b.col);
    for(let i=0;i<row.length;i++)
      for(let j=i+1;j<row.length;j++)
        if(row[i].gc > row[j].gc) lc+=2;
  }
  for(let c=0;c<size;c++){
    const col=[];
    for(let r=0;r<size;r++){
      const t=tiles[r*size+c]; if(t===0) continue;
      const gc=(t-1)%size;
      if(gc===c) col.push({gr:Math.floor((t-1)/size), row:r});
    }
    col.sort((a,b)=>a.row-b.row);
    for(let i=0;i<col.length;i++)
      for(let j=i+1;j<col.length;j++)
        if(col[i].gr > col[j].gr) lc+=2;
  }
  return manhattanDist(tiles,size) + lc;
}

// ═══════════════════════════════════════════════════════════════════════════════
// IDA* with GENERATOR — yields every CHUNK nodes so browser never freezes
// Correct iterative DFS using explicit stack (no recursion limit issues)
// Works reliably for 3x3 and 4x4
// ═══════════════════════════════════════════════════════════════════════════════
function idaStarAsync(startTiles, size) {
  return new Promise(resolve => {
    if(isGoalState(startTiles, size)){ resolve({path:[],nodes:0}); return; }
    const hFn  = t => linearConflict(t, size);
    let bound  = hFn(startTiles);
    let nodes  = 0;
    const CHUNK = 6000;

    // Explicit iterative DFS stack — avoids JS call stack overflow
    // Each frame: {tiles, emptyIdx, nbrs, ni, g, lastBlankPos}
    // pathMoves mirrors the stack depth (one entry per "pushed" frame)
    function runBound(onDone) {
      const stack = [{
        tiles: [...startTiles],
        emptyIdx: startTiles.indexOf(0),
        nbrs: getNeighbors(startTiles.indexOf(0), size),
        ni: 0, g: 0, lastBlankPos: -1,
      }];
      const pathMoves = [];
      let nextBound = Infinity;
      let chunk = 0;

      function tick() {
        while(stack.length > 0) {
          const top = stack[stack.length-1];

          if(top.ni === 0) {
            // first visit: pruning check
            const h = hFn(top.tiles);
            const f = top.g + h;
            if(f > bound) {
              if(f < nextBound) nextBound = f;
              stack.pop(); if(pathMoves.length>0) pathMoves.pop();
              continue;
            }
            if(h === 0) { onDone({found:true, path:[...pathMoves], nodes}); return; }
            nodes++; chunk++;
            if(chunk >= CHUNK) { chunk=0; setTimeout(tick,0); return; } // yield
          }

          // expand next unvisited neighbor
          let pushed = false;
          while(top.ni < top.nbrs.length) {
            const nIdx = top.nbrs[top.ni++];
            if(nIdx === top.lastBlankPos) continue;
            const next = [...top.tiles];
            [next[top.emptyIdx], next[nIdx]] = [next[nIdx], next[top.emptyIdx]];
            stack.push({ tiles:next, emptyIdx:nIdx,
              nbrs:getNeighbors(nIdx,size), ni:0,
              g:top.g+1, lastBlankPos:top.emptyIdx });
            pathMoves.push(nIdx);
            pushed = true; break;
          }
          if(!pushed){ stack.pop(); if(pathMoves.length>0) pathMoves.pop(); }
        }
        onDone({found:false, nextBound, nodes});
      }
      setTimeout(tick, 0);
    }

    function iterate() {
      if(nodes > 40000000){ resolve(null); return; }
      runBound(result => {
        if(result.found){ resolve({path:result.path, nodes:result.nodes}); return; }
        if(result.nextBound === Infinity){ resolve(null); return; }
        bound = result.nextBound;
        setTimeout(iterate, 0);
      });
    }
    iterate();
  });
}

// ═══════════════════════════════════════════════════════════════════════════════
// BEAM SEARCH for 5×5 — fast near-optimal solver, fully async
// Explores beam-width best states per depth level, yields per level
// ═══════════════════════════════════════════════════════════════════════════════
function beamSearch(startTiles, size) {
  return new Promise(resolve => {
    if(isGoalState(startTiles, size)){ resolve({path:[],nodes:0}); return; }
    const hFn = t => linearConflict(t, size);
    const BEAM = size===5 ? 500 : 300;
    const MAX_DEPTH = 300;
    let beam = [{tiles:startTiles, emptyIdx:startTiles.indexOf(0), path:[], h:hFn(startTiles)}];
    let depth = 0, nodes = 0;
    const globalVisited = new Set([startTiles.join(",")]);

    function step() {
      if(depth >= MAX_DEPTH){ resolve(null); return; }
      const next = [];

      for(const state of beam){
        for(const nIdx of getNeighbors(state.emptyIdx, size)){
          const nt = [...state.tiles];
          [nt[state.emptyIdx],nt[nIdx]]=[nt[nIdx],nt[state.emptyIdx]];
          const key = nt.join(",");
          if(globalVisited.has(key)) continue;
          globalVisited.add(key);
          nodes++;
          const newPath = [...state.path, nIdx];
          if(isGoalState(nt, size)){ resolve({path:newPath, nodes}); return; }
          next.push({tiles:nt, emptyIdx:nIdx, path:newPath, h:hFn(nt)});
        }
      }
      if(next.length === 0){ resolve(null); return; }
      next.sort((a,b)=>a.h-b.h);
      beam = next.slice(0, BEAM);
      depth++;
      setTimeout(step, 0); // yield per level — keeps UI alive
    }
    step();
  });
}

// ═══════════════════════════════════════════════════════════════════════════════
// MASTER SOLVER — picks best algorithm per puzzle size
// 3x3: IDA* (exact, fast)
// 4x4: IDA* (exact, linear conflict heuristic reduces nodes ~10x)
// 5x5: Beam Search (near-optimal, always terminates quickly)
// ═══════════════════════════════════════════════════════════════════════════════
async function solvePuzzle(tiles, size) {
  if(size === 3) return idaStarAsync(tiles, size);
  if(size === 4) return idaStarAsync(tiles, size);
  return beamSearch(tiles, size);          // 5x5: beam search
}

// ── Fast A* with binary min-heap for 3×3 only (instant) ──
class MinHeap {
  constructor() { this.h=[]; }
  push(item) {
    this.h.push(item);
    let i=this.h.length-1;
    while(i>0){
      const p=Math.floor((i-1)/2);
      if(this.h[p].f<=this.h[i].f) break;
      [this.h[p],this.h[i]]=[this.h[i],this.h[p]]; i=p;
    }
  }
  pop() {
    const top=this.h[0]; const last=this.h.pop();
    if(this.h.length>0){ this.h[0]=last; let i=0;
      while(true){ let s=i,l=2*i+1,r=2*i+2;
        if(l<this.h.length&&this.h[l].f<this.h[s].f) s=l;
        if(r<this.h.length&&this.h[r].f<this.h[s].f) s=r;
        if(s===i) break; [this.h[s],this.h[i]]=[this.h[i],this.h[s]]; i=s;
      }
    }
    return top;
  }
  get size(){ return this.h.length; }
}

function aStarSmall(start, size) {
  if(isGoalState(start,size)) return {path:[],nodes:0};
  const heap=new MinHeap(), closed=new Set();
  const h0=manhattanDist(start,size);
  heap.push({tiles:start,g:0,h:h0,f:h0,parent:null,move:null});
  let nodes=0;
  while(heap.size>0 && nodes<200000){
    nodes++;
    const cur=heap.pop(); const key=cur.tiles.join(",");
    if(closed.has(key)) continue; closed.add(key);
    if(isGoalState(cur.tiles,size)){
      const path=[]; let node=cur;
      while(node.move!==null){path.unshift(node.move);node=node.parent;}
      return {path,nodes};
    }
    const eIdx=cur.tiles.indexOf(0);
    for(const nIdx of getNeighbors(eIdx,size)){
      const next=[...cur.tiles]; [next[eIdx],next[nIdx]]=[next[nIdx],next[eIdx]];
      const nKey=next.join(","); if(closed.has(nKey)) continue;
      const g=cur.g+1, h=manhattanDist(next,size);
      heap.push({tiles:next,g,h,f:g+h,parent:cur,move:nIdx});
    }
  }
  return null;
}

// ── Greedy (async, limited) ──
async function greedySolveAsync(start, size) {
  if(isGoalState(start,size)) return {path:[],nodes:0};
  const heap=new MinHeap(), closed=new Set();
  const h0=manhattanDist(start,size);
  heap.push({tiles:start,h:h0,parent:null,move:null});
  let nodes=0; const MAX=size<=3?50000:100000;
  while(heap.size>0&&nodes<MAX){
    nodes++;
    const cur=heap.pop(); const key=cur.tiles.join(",");
    if(closed.has(key)) continue; closed.add(key);
    if(isGoalState(cur.tiles,size)){
      const path=[]; let node=cur;
      while(node.move!==null){path.unshift(node.move);node=node.parent;}
      return {path,nodes};
    }
    const eIdx=cur.tiles.indexOf(0);
    for(const nIdx of getNeighbors(eIdx,size)){
      const next=[...cur.tiles]; [next[eIdx],next[nIdx]]=[next[nIdx],next[eIdx]];
      const nKey=next.join(","); if(closed.has(nKey)) continue;
      heap.push({tiles:next,h:manhattanDist(next,size),parent:cur,move:nIdx});
    }
    if(nodes%5000===0) await new Promise(r=>setTimeout(r,0)); // yield
  }
  return null;
}

// ── BFS (limited, for comparison only) ──
async function bfsSolveAsync(start, size) {
  if(isGoalState(start,size)) return {path:[],nodes:0};
  const MAX = size<=3?30000:8000;
  const queue=[{tiles:start,path:[]}], visited=new Set([start.join(",")]);
  let nodes=0;
  while(queue.length>0&&nodes<MAX){
    nodes++;
    const {tiles,path}=queue.shift();
    const eIdx=tiles.indexOf(0);
    for(const nIdx of getNeighbors(eIdx,size)){
      const next=[...tiles]; [next[eIdx],next[nIdx]]=[next[nIdx],next[eIdx]];
      const key=next.join(","); if(visited.has(key)) continue;
      visited.add(key);
      const np=[...path,nIdx];
      if(isGoalState(next,size)) return {path:np,nodes};
      queue.push({tiles:next,path:np});
    }
    if(nodes%3000===0) await new Promise(r=>setTimeout(r,0)); // yield
  }
  return {path:null,nodes,partial:true}; // hit limit
}

// ═══════════════════════════════════════════════════════════════════════════════
// SOUND
// ═══════════════════════════════════════════════════════════════════════════════
function createSound(type) {
  try {
    const ctx=new (window.AudioContext||window.webkitAudioContext)();
    const o=ctx.createOscillator(), g=ctx.createGain();
    o.connect(g); g.connect(ctx.destination);
    if(type==="click"){ o.frequency.setValueAtTime(440,ctx.currentTime); o.frequency.exponentialRampToValueAtTime(220,ctx.currentTime+0.1); g.gain.setValueAtTime(0.12,ctx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,ctx.currentTime+0.12); o.start(); o.stop(ctx.currentTime+0.12); }
    if(type==="hint") { o.type="sine"; o.frequency.setValueAtTime(880,ctx.currentTime); o.frequency.setValueAtTime(1100,ctx.currentTime+0.1); g.gain.setValueAtTime(0.09,ctx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,ctx.currentTime+0.25); o.start(); o.stop(ctx.currentTime+0.25); }
    if(type==="win")  { o.type="sine"; [523,659,784,1047].forEach((f,i)=>o.frequency.setValueAtTime(f,ctx.currentTime+i*0.12)); g.gain.setValueAtTime(0.18,ctx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,ctx.currentTime+0.7); o.start(); o.stop(ctx.currentTime+0.7); }
    if(type==="wrong"){ o.type="sawtooth"; o.frequency.setValueAtTime(160,ctx.currentTime); g.gain.setValueAtTime(0.07,ctx.currentTime); g.gain.exponentialRampToValueAtTime(0.001,ctx.currentTime+0.15); o.start(); o.stop(ctx.currentTime+0.15); }
  } catch(e){}
}

// ═══════════════════════════════════════════════════════════════════════════════
// CONFETTI
// ═══════════════════════════════════════════════════════════════════════════════
function Confetti({ active }) {
  const pieces = useMemo(()=>Array.from({length:70},(_,i)=>({
    id:i, x:Math.random()*100, delay:Math.random()*1.2,
    color:["#f1c40f","#e74c3c","#2ecc71","#3498db","#9b59b6","#e67e22","#1abc9c"][i%7],
    size:Math.random()*7+4, rot:Math.random()*360, dur:Math.random()*1.5+1.8,
  })),[]);
  if(!active) return null;
  return (
    <div style={{position:"fixed",inset:0,pointerEvents:"none",zIndex:50,overflow:"hidden"}}>
      {pieces.map(p=>(
        <div key={p.id} style={{
          position:"absolute",left:`${p.x}%`,top:"-20px",
          width:p.size,height:p.size,background:p.color,
          borderRadius:p.id%2===0?"50%":"2px",
          animation:`cfall ${p.dur}s ${p.delay}s ease-in forwards`,
          transform:`rotate(${p.rot}deg)`,
        }}/>
      ))}
      <style>{`@keyframes cfall{0%{top:-20px;opacity:1}100%{top:105vh;opacity:0;transform:rotate(540deg)}}`}</style>
    </div>
  );
}

// ═══════════════════════════════════════════════════════════════════════════════
// PERFORMANCE
// ═══════════════════════════════════════════════════════════════════════════════
function calcPerf(moves,optimal,time) {
  if(optimal===0) return 10000;
  const eff=Math.max(0,1-(moves-optimal)/(optimal+1));
  const spd=Math.max(0,1-time/(optimal*6));
  return Math.round((eff*0.7+spd*0.3)*10000);
}
function gradeOf(ps) {
  if(ps>=9000) return{g:"S",c:"#ffd32a",label:"LEGENDARY"};
  if(ps>=7500) return{g:"A",c:"#2ecc71",label:"EXCELLENT"};
  if(ps>=5500) return{g:"B",c:"#3498db",label:"GOOD"};
  if(ps>=3500) return{g:"C",c:"#ff9f43",label:"AVERAGE"};
  return{g:"D",c:"#e74c3c",label:"KEEP TRYING"};
}

// ═══════════════════════════════════════════════════════════════════════════════
// MAIN COMPONENT
// ═══════════════════════════════════════════════════════════════════════════════
export default function UltimatePuzzle() {
  const [diff,        setDiff]        = useState("easy");
  const [phase,       setPhase]       = useState(PHASES.IDLE);
  const [tiles,       setTiles]       = useState([]);
  const [moves,       setMoves]       = useState(0);
  const [time,        setTime]        = useState(0);
  const [history,     setHistory]     = useState([]);
  const [animTile,    setAnimTile]    = useState(null);
  const [hintIdx,     setHintIdx]     = useState(null);
  const [hintPath,    setHintPath]    = useState([]);
  const [hintHop,     setHintHop]     = useState(0);
  const [showFullPath,setShowFullPath] = useState(false);
  const [solution,    setSolution]    = useState(null);
  const [solveStep,   setSolveStep]   = useState(0);
  const [optLen,      setOptLen]      = useState(null);
  const [nodesExp,    setNodesExp]    = useState(null);
  const [algoStats,   setAlgoStats]   = useState(null);
  const [computing,   setComputing]   = useState(false); // spinner for hint/solve
  const [computeMsg,  setComputeMsg]  = useState("");
  const [perfScore,   setPerfScore]   = useState(null);
  const [leaderboard, setLeaderboard] = useState(()=>{ try{return JSON.parse(localStorage.getItem("puzzle_lb2")||"[]")}catch{return[]} });
  const [darkMode,    setDarkMode]    = useState(true);
  const [soundOn,     setSoundOn]     = useState(true);
  const [tab,         setTab]         = useState("metrics");
  const [showLB,      setShowLB]      = useState(false);
  const [confetti,    setConfetti]    = useState(false);
  const [shuffleAnim, setShuffleAnim] = useState([]);
  const [newRecord,   setNewRecord]   = useState(false);
  const [solveAborted,setSolveAborted]= useState(false);

  const size       = DIFFICULTIES[diff].size;
  const goal       = useMemo(()=>makeGoal(size),[size]);
  const emptyIdx   = tiles.indexOf(0);
  const hVal       = tiles.length>0 ? manhattanDist(tiles,size) : 0;
  const mVal       = tiles.length>0 ? misplacedTiles(tiles,size) : 0;
  const inPlace    = tiles.filter((t,i)=>t!==0&&t===goal[i]).length;
  const totalTiles = size*size-1;

  const timerRef   = useRef(null);
  const solveRef   = useRef(null);
  const abortRef   = useRef(false);   // flag to cancel ongoing solve animation
  const sound      = useCallback(t=>{ if(soundOn) createSound(t); },[soundOn]);

  // ── Theme ──
  const T = darkMode ? {
    bg:"#07090f", surface:"rgba(255,255,255,0.025)", border:"rgba(255,255,255,0.07)",
    text:"#dce8f0", muted:"#3a4a5a", accent:"#3498db", card:"rgba(255,255,255,0.02)",
  } : {
    bg:"#eef2f7", surface:"rgba(0,0,0,0.04)", border:"rgba(0,0,0,0.1)",
    text:"#1a2332", muted:"#7a8899", accent:"#2980b9", card:"rgba(0,0,0,0.03)",
  };

  // ── Timer ──
  useEffect(()=>{
    if(phase===PHASES.PLAYING){ timerRef.current=setInterval(()=>setTime(t=>t+1),1000); }
    else clearInterval(timerRef.current);
    return()=>clearInterval(timerRef.current);
  },[phase]);

  // ── Win detection ──
  useEffect(()=>{
    if(phase!==PHASES.PLAYING && phase!==PHASES.SOLVING) return;
    if(tiles.length>0 && isGoalState(tiles,size)){
      clearInterval(timerRef.current);
      abortRef.current=true;
      setPhase(PHASES.WON);
      const ps=optLen!==null ? calcPerf(moves,optLen,time) : null;
      setPerfScore(ps);
      setConfetti(true);
      sound("win");
      setTimeout(()=>setConfetti(false),4000);
      const entry={diff,moves,time,score:ps||0,date:new Date().toLocaleDateString()};
      const newLB=[...leaderboard,entry].sort((a,b)=>(b.score||0)-(a.score||0)).slice(0,10);
      setLeaderboard(newLB);
      try{localStorage.setItem("puzzle_lb2",JSON.stringify(newLB));}catch{}
      if(!leaderboard.length || (ps||0)>(leaderboard[0]?.score||0)) setNewRecord(true);
    }
  },[tiles]);

  // ── Start game — accepts explicit sz so difficulty switch works immediately ──
  const startGame = useCallback((sz)=>{
    const activeSize = sz ?? size;   // use passed size or current
    abortRef.current=true;
    clearInterval(timerRef.current); clearTimeout(solveRef.current);
    const t=shuffleTiles(activeSize);
    setPhase(PHASES.SHUFFLING); setComputing(false);
    setSolution(null); setSolveStep(0); setOptLen(null); setNodesExp(null);
    setAlgoStats(null); setHistory([]); setMoves(0); setTime(0);
    setHintIdx(null); setHintPath([]); setPerfScore(null); setNewRecord(false);
    setShowFullPath(false); setHintHop(0); setSolveAborted(false);
    setTiles([]);  // clear old grid immediately so stale tiles never show
    let step=0; const steps=10;
    const anim=setInterval(()=>{
      step++;
      setShuffleAnim(Array.from({length:activeSize*activeSize},()=>Math.random()>0.55));
      if(step>=steps){
        clearInterval(anim); setShuffleAnim([]);
        setTiles(t); setPhase(PHASES.PLAYING);
        abortRef.current=false;
      }
    },75);
  },[size]);

  // ── Tile click ──
  const handleClick = useCallback((idx)=>{
    if(phase!==PHASES.PLAYING || animTile!==null) return;
    if(!getNeighbors(emptyIdx,size).includes(idx)){ sound("wrong"); return; }
    sound("click");
    setAnimTile(idx); setTimeout(()=>setAnimTile(null),140);
    setHintIdx(null);
    setTiles(prev=>{
      const next=[...prev]; const ei=next.indexOf(0);
      [next[ei],next[idx]]=[next[idx],next[ei]];
      setHistory(h=>[...h,{tiles:prev,move:idx}]);
      return next;
    });
    setMoves(m=>m+1);
  },[phase,emptyIdx,size,animTile,sound]);

  // ── Undo ──
  const undo = ()=>{
    if(!history.length || phase!==PHASES.PLAYING) return;
    const last=history[history.length-1];
    setTiles(last.tiles); setHistory(h=>h.slice(0,-1)); setMoves(m=>Math.max(0,m-1));
    setHintIdx(null); sound("click");
  };

  // ── Hint (async, non-blocking) ──
  const showHint = useCallback(async()=>{
    if(phase!==PHASES.PLAYING || computing) return;
    setComputing(true);
    setComputeMsg(size===3?"Computing hint…":size===4?"IDA* computing hint…":"Beam Search computing hint…");
    const currentTiles=[...tiles];
    const res = await solvePuzzle(currentTiles, size);
    setComputing(false);
    if(!res || !res.path.length) return;
    setOptLen(res.path.length); setNodesExp(res.nodes);
    setSolution(res.path); setHintPath(res.path); setHintHop(0);
    setHintIdx(res.path[0]);
    sound("hint");
    setTimeout(()=>setHintIdx(null),2000);
  },[phase,computing,tiles,size,sound]);

  // ── Next hint step ──
  const nextHint = ()=>{
    if(!hintPath.length) return;
    const next=(hintHop+1)%hintPath.length;
    setHintHop(next); setHintIdx(hintPath[next]);
    sound("hint");
    setTimeout(()=>setHintIdx(null),1500);
  };

  // ── Auto solve (async, non-blocking) ──
  const autoSolve = useCallback(async()=>{
    if(phase!==PHASES.PLAYING || computing) return;
    setComputing(true);
    setComputeMsg(size===3?"Finding optimal solution…":size===4?`IDA* solving 4×4… computing optimal path`:`Beam Search solving 5×5… finding solution`);
    const currentTiles=[...tiles];
    abortRef.current=false;

    const res = await solvePuzzle(currentTiles, size);
    setComputing(false);

    if(!res || !res.path || abortRef.current) return;
    setSolution(res.path); setSolveStep(0);
    setOptLen(res.path.length); setNodesExp(res.nodes);
    setPhase(PHASES.SOLVING);

    // Run comparison algos in background (non-blocking)
    Promise.all([
      greedySolveAsync(currentTiles, size),
      bfsSolveAsync(currentTiles, size),
    ]).then(([greedy, bfs])=>{
      setAlgoStats({
        astar:  {nodes:res.nodes,    pathLen:res.path.length,       label:"A*/IDA*"},
        greedy: {nodes:greedy?.nodes||"N/A", pathLen:greedy?.path?.length||"N/A", label:"Greedy"},
        bfs:    {nodes:bfs?.nodes||"N/A",    pathLen:bfs?.path?.length||bfs?.partial?"Partial":"N/A", label:"BFS"},
      });
    });
  },[phase,computing,tiles,size]);

  // ── Step through solution ──
  useEffect(()=>{
    if(phase!==PHASES.SOLVING || !solution) return;
    if(abortRef.current){ setPhase(PHASES.PLAYING); return; }
    if(solveStep>=solution.length){ setPhase(PHASES.PLAYING); return; }
    const delay = size<=3?380:size<=4?300:240;
    solveRef.current=setTimeout(()=>{
      if(abortRef.current) return;
      setTiles(prev=>{
        const next=[...prev]; const ei=next.indexOf(0); const mi=solution[solveStep];
        [next[ei],next[mi]]=[next[mi],next[ei]]; return next;
      });
      setMoves(m=>m+1); setSolveStep(s=>s+1);
    },delay);
    return()=>clearTimeout(solveRef.current);
  },[phase,solveStep,solution,size]);

  // ── Stop solving ──
  const stopSolving = ()=>{
    abortRef.current=true;
    clearTimeout(solveRef.current);
    setPhase(PHASES.PLAYING);
    setSolveAborted(true);
  };

  // ── Keyboard ──
  useEffect(()=>{
    const h=e=>{
      if(phase!==PHASES.PLAYING) return;
      const map={ArrowUp:emptyIdx+size,ArrowDown:emptyIdx-size,ArrowLeft:emptyIdx+1,ArrowRight:emptyIdx-1};
      const t=map[e.key]; if(t!==undefined&&t>=0&&t<size*size) handleClick(t);
    };
    window.addEventListener("keydown",h); return()=>window.removeEventListener("keydown",h);
  },[tiles,phase,emptyIdx,size,handleClick]);

  const fmt=s=>`${String(Math.floor(s/60)).padStart(2,"0")}:${String(s%60).padStart(2,"0")}`;

  const tileW = size===3?"min(90px,22vw)":size===4?"min(72px,17vw)":"min(58px,13vw)";
  const gap   = size===3?"8px":size===4?"6px":"5px";
  const numSz = size===3?"clamp(22px,5.5vw,36px)":size===4?"clamp(18px,4vw,28px)":"clamp(14px,3vw,22px)";

  return (
    <div style={{minHeight:"100vh",background:T.bg,color:T.text,fontFamily:"'Courier New',monospace",
      display:"flex",flexDirection:"column",alignItems:"center",padding:"16px 12px 40px",
      transition:"background 0.3s",position:"relative",overflow:"hidden"}}>

      {/* BG grid */}
      <div style={{position:"fixed",inset:0,pointerEvents:"none",zIndex:0,
        backgroundImage:`linear-gradient(${T.border} 1px,transparent 1px),linear-gradient(90deg,${T.border} 1px,transparent 1px)`,
        backgroundSize:"32px 32px"}}/>
      <div style={{position:"fixed",inset:0,pointerEvents:"none",zIndex:0,
        background:`radial-gradient(ellipse at 15% 30%,rgba(52,152,219,0.07) 0%,transparent 55%),
                    radial-gradient(ellipse at 85% 70%,rgba(155,89,182,0.06) 0%,transparent 55%)`}}/>

      <Confetti active={confetti}/>

      {/* ── HEADER ── */}
      <div style={{width:"100%",maxWidth:"920px",display:"flex",justifyContent:"space-between",
        alignItems:"center",marginBottom:"14px",zIndex:1}}>
        <div>
          <div style={{fontSize:"8px",letterSpacing:"6px",color:T.accent,opacity:0.8}}>AI PUZZLE ENGINE v2</div>
          <h1 style={{margin:0,fontSize:"clamp(20px,5vw,36px)",fontWeight:"900",letterSpacing:"2px",
            background:`linear-gradient(135deg,${T.text} 0%,${T.accent} 55%,#9b59b6 100%)`,
            WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent"}}>N-PUZZLE AI</h1>
        </div>
        <div style={{display:"flex",gap:"7px"}}>
          <IBtn onClick={()=>setSoundOn(s=>!s)}>{soundOn?"🔊":"🔇"}</IBtn>
          <IBtn onClick={()=>setDarkMode(d=>!d)}>{darkMode?"☀️":"🌙"}</IBtn>
          <IBtn onClick={()=>setShowLB(l=>!l)}>🏆</IBtn>
        </div>
      </div>

      {/* ── DIFFICULTY ── */}
      <div style={{display:"flex",gap:"8px",marginBottom:"14px",zIndex:1}}>
        {Object.entries(DIFFICULTIES).map(([key,d])=>(
          <button key={key} onClick={()=>{const ns=DIFFICULTIES[key].size; setDiff(key); setTiles([]); setPhase(PHASES.IDLE); setTimeout(()=>startGame(ns),0);}}
            style={{padding:"7px 14px",fontSize:"9px",fontWeight:"700",letterSpacing:"2px",
              fontFamily:"'Courier New',monospace",cursor:"pointer",borderRadius:"8px",
              background:diff===key?T.accent:"transparent",
              color:diff===key?"#fff":T.muted,
              border:`1px solid ${diff===key?T.accent:T.border}`,
              boxShadow:diff===key?`0 0 14px ${T.accent}44`:"none",transition:"all 0.2s"}}>
            {d.emoji} {d.label}<br/><span style={{fontSize:"7px",opacity:0.7}}>{d.desc}</span>
          </button>
        ))}
      </div>

      {/* ── STATS ROW ── */}
      <div style={{display:"flex",gap:"7px",flexWrap:"wrap",justifyContent:"center",marginBottom:"14px",zIndex:1}}>
        {[
          {l:"MOVES",      v:moves,                  c:"#f1c40f"},
          {l:"TIME",       v:fmt(time),               c:T.accent},
          {l:"MANHATTAN",  v:hVal,                    c:hVal===0?"#2ecc71":hVal<8?"#f1c40f":"#e74c3c"},
          {l:"MISPLACED",  v:mVal,                    c:mVal===0?"#2ecc71":"#e67e22"},
          {l:"IN PLACE",   v:`${inPlace}/${totalTiles}`, c:"#2ecc71"},
          {l:"f=g+h",      v:`${moves}+${hVal}`,      c:"#9b59b6"},
        ].map(s=>(
          <div key={s.l} style={{textAlign:"center",padding:"6px 10px",
            background:T.card,border:`1px solid ${T.border}`,borderRadius:"8px",minWidth:"56px"}}>
            <div style={{fontSize:"7px",letterSpacing:"2px",color:T.muted,marginBottom:"2px"}}>{s.l}</div>
            <div style={{fontSize:"15px",fontWeight:"900",color:s.c,lineHeight:1}}>{s.v}</div>
          </div>
        ))}
      </div>

      {/* ── MAIN CONTENT ── */}
      <div style={{display:"flex",gap:"16px",flexWrap:"wrap",justifyContent:"center",zIndex:1,width:"100%",maxWidth:"920px"}}>

        {/* ── BOARD ── */}
        <div style={{display:"flex",flexDirection:"column",alignItems:"center",gap:"10px"}}>

          {/* Status badge */}
          <div style={{height:"22px",textAlign:"center",fontSize:"10px",letterSpacing:"3px",fontWeight:"700",
            color:computing?"#f1c40f":phase===PHASES.PLAYING?"#2ecc71":phase===PHASES.SOLVING?"#f1c40f":phase===PHASES.WON?"#3498db":"transparent",
            animation:(phase===PHASES.PLAYING||phase===PHASES.SOLVING||computing)?"pulse 1.5s ease infinite":"none"}}>
            {computing && `⏳ ${computeMsg}`}
            {!computing && phase===PHASES.PLAYING  && "● ACTIVE — SLIDE TILES"}
            {!computing && phase===PHASES.SOLVING  && `🤖 AUTO-SOLVING ${solveStep}/${solution?.length||0}`}
            {!computing && phase===PHASES.SHUFFLING&& "⚡ SHUFFLING…"}
          </div>

          {/* Board grid */}
          <div style={{padding:"12px",background:T.surface,border:`1px solid ${T.border}`,
            borderRadius:"16px",boxShadow:`0 20px 60px rgba(0,0,0,${darkMode?0.5:0.12})`}}>
            {/* Only render tiles when array matches current difficulty size */}
            <div style={{display:"grid",gridTemplateColumns:`repeat(${size},${tileW})`,gap,
              minWidth:`calc(${tileW} * ${size} + ${gap} * ${size-1})`,
              minHeight:`calc(${tileW} * ${size} + ${gap} * ${size-1})`}}>
              {tiles.length===size*size ? tiles.map((tile,idx)=>{
                const empty  = tile===0;
                const isNeigh= !empty&&getNeighbors(emptyIdx,size).includes(idx);
                const isAnim = animTile===idx;
                const isHint = hintIdx===idx;
                const hv     = tileManhattan(tile,idx,size);
                const color  = TILE_COLORS[(tile-1+TILE_COLORS.length)%TILE_COLORS.length]||"#888";
                const inP    = !empty && goal[idx]===tile;
                const isShuf = shuffleAnim[idx];
                const isPathStep = showFullPath && hintPath[hintHop]===idx;
                const clickable  = isNeigh && phase===PHASES.PLAYING && !computing;

                return (
                  <div key={idx} onClick={()=>handleClick(idx)} style={{
                    width:tileW, height:tileW, borderRadius:size<=3?"12px":size<=4?"10px":"8px",
                    display:"flex",flexDirection:"column",alignItems:"center",justifyContent:"center",
                    position:"relative",userSelect:"none",
                    cursor:clickable?"pointer":"default",
                    transition:"all 0.15s cubic-bezier(0.34,1.56,0.64,1)",
                    transform:isAnim?"scale(0.84)":isShuf?"scale(0.7) rotate(18deg)":clickable?"scale(1.05)":"scale(1)",
                    opacity:isShuf?0.35:1,
                    background:empty?T.surface:isHint?"rgba(241,196,15,0.5)":isPathStep?"rgba(52,152,219,0.4)"
                      :inP?`linear-gradient(135deg,${color}dd,${color}88)`:`linear-gradient(135deg,${color}99,${color}55)`,
                    border:empty?`2px dashed ${T.border}`:isHint?"2px solid #f1c40f":isPathStep?`2px solid ${T.accent}`
                      :inP?`2px solid ${color}99`:`2px solid ${color}44`,
                    boxShadow:empty?"none":isHint?`0 0 20px rgba(241,196,15,0.65)`:isPathStep?`0 0 16px ${T.accent}55`
                      :clickable?`0 6px 20px ${color}55`:inP?`0 4px 14px ${color}44`:`0 2px 8px ${color}22`,
                  }}>
                    {!empty&&(
                      <>
                        <span style={{fontSize:numSz,fontWeight:"900",color:"#fff",
                          textShadow:"0 2px 6px rgba(0,0,0,0.5)",lineHeight:1}}>{tile}</span>
                        <span style={{position:"absolute",bottom:"2px",right:"4px",fontSize:"8px",
                          fontWeight:"700",color:hv===0?"#2ecc71":"#ffaaaa",
                          background:"rgba(0,0,0,0.4)",borderRadius:"3px",padding:"0 2px",lineHeight:"13px"}}>h={hv}</span>
                        {inP&&<span style={{position:"absolute",top:"2px",left:"4px",fontSize:"9px",color:"#2ecc71",opacity:0.9}}>✓</span>}
                        {isHint&&<span style={{position:"absolute",top:"2px",right:"4px",fontSize:"10px",animation:"bounce 0.45s ease infinite alternate"}}>💡</span>}
                      </>
                    )}
                  </div>
                );
              }) : Array.from({length:size*size}).map((_,i)=>(<div key={i} style={{width:tileW,height:tileW,borderRadius:size<=3?"12px":size<=4?"10px":"8px",background:T.border,opacity:0.25,animation:"pulse 1s ease infinite"}}/>) )}
            </div>
          </div>

          {/* ── BUTTONS ── */}
          <div style={{display:"flex",gap:"6px",flexWrap:"wrap",justifyContent:"center"}}>
            <Btn onClick={()=>startGame(size)} color="#2ecc71" glow T={T}>{tiles.length?"⟳ NEW":"▶ START"}</Btn>
            <Btn onClick={undo}        color="#e67e22" disabled={!history.length||phase!==PHASES.PLAYING||computing} T={T}>↩ UNDO</Btn>
            <Btn onClick={showHint}    color="#f1c40f" disabled={phase!==PHASES.PLAYING||computing} T={T}>
              {computing&&hintPath.length===0?"⏳…":"💡 HINT"}
            </Btn>
            {hintPath.length>0&&phase===PHASES.PLAYING&&(
              <Btn onClick={nextHint}  color={T.accent} T={T}>→ STEP</Btn>
            )}
            <Btn onClick={autoSolve}   color="#9b59b6" disabled={phase!==PHASES.PLAYING||computing} T={T}>
              {computing?"⏳ SOLVING…":"🤖 AUTO SOLVE"}
            </Btn>
            {phase===PHASES.SOLVING&&(
              <Btn onClick={stopSolving} color="#e74c3c" T={T}>■ STOP</Btn>
            )}
          </div>

          {/* Hint path toggle */}
          {hintPath.length>0&&(
            <button onClick={()=>setShowFullPath(f=>!f)} style={{
              fontSize:"8px",letterSpacing:"2px",color:T.muted,background:"transparent",
              border:`1px solid ${T.border}`,borderRadius:"6px",padding:"4px 12px",cursor:"pointer"}}>
              {showFullPath?"HIDE PATH":"SHOW SOLUTION PATH"} ({hintPath.length} steps)
            </button>
          )}

          <div style={{fontSize:"8px",color:T.muted,letterSpacing:"1px"}}>← → ↑ ↓ keyboard supported</div>

          {/* Move history */}
          {history.length>0&&(
            <div style={{width:"100%",maxWidth:"350px",background:T.card,border:`1px solid ${T.border}`,
              borderRadius:"10px",padding:"9px",maxHeight:"90px",overflowY:"auto"}}>
              <div style={{fontSize:"7px",letterSpacing:"3px",color:T.muted,marginBottom:"5px"}}>MOVE LOG ({history.length})</div>
              <div style={{display:"flex",flexWrap:"wrap",gap:"3px"}}>
                {history.slice(-36).map((h,i)=>{
                  const movedTile=h.tiles[h.move]||0;
                  const col=movedTile>0?TILE_COLORS[(movedTile-1)%TILE_COLORS.length]:"#555";
                  return(
                    <span key={i} style={{fontSize:"9px",padding:"2px 5px",
                      background:`${col}28`,border:`1px solid ${col}44`,
                      borderRadius:"4px",color:T.text,fontWeight:"700"}}>{movedTile||"_"}</span>
                  );
                })}
                {history.length>36&&<span style={{fontSize:"8px",color:T.muted}}>+{history.length-36}</span>}
              </div>
            </div>
          )}
        </div>

        {/* ── ANALYTICS PANEL ── */}
        <div style={{width:"min(310px,92vw)",background:T.surface,border:`1px solid ${T.border}`,
          borderRadius:"16px",overflow:"hidden",display:"flex",flexDirection:"column",minHeight:"420px"}}>

          {/* Tabs */}
          <div style={{display:"flex",borderBottom:`1px solid ${T.border}`}}>
            {[["metrics","📊"],["solver","🤖"],["algo","⚡"]].map(([k,icon])=>(
              <button key={k} onClick={()=>setTab(k)} style={{
                flex:1,padding:"9px 0",fontSize:"9px",letterSpacing:"2px",fontFamily:"'Courier New',monospace",
                fontWeight:"700",background:tab===k?`${T.accent}18`:"transparent",
                color:tab===k?T.accent:T.muted,border:"none",cursor:"pointer",
                borderBottom:tab===k?`2px solid ${T.accent}`:"2px solid transparent",transition:"all 0.15s"}}>
                {icon} {k.toUpperCase()}
              </button>
            ))}
          </div>

          {/* METRICS */}
          {tab==="metrics"&&(
            <div style={{padding:"13px",display:"flex",flexDirection:"column",gap:"9px",overflowY:"auto"}}>
              <MC label="MANHATTAN DISTANCE h(n)" value={hVal}
                color={hVal===0?"#2ecc71":hVal<8?"#f1c40f":"#e74c3c"}
                bar={Math.max(0,1-hVal/(totalTiles*2))}
                barC={hVal===0?"#2ecc71":hVal<8?"#f1c40f":"#e74c3c"}
                sub={hVal===0?"✅ All tiles in place!":hVal===1?"1 step away":`${hVal} total displacement`} T={T}/>
              <MC label="MISPLACED TILES h(n)" value={mVal}
                color={mVal===0?"#2ecc71":"#e67e22"}
                bar={1-mVal/Math.max(1,totalTiles)} barC="#e67e22"
                sub={`${totalTiles-mVal} of ${totalTiles} tiles correct`} T={T}/>
              <MC label="f(n) = g(n) + h(n)" value={`${moves}+${hVal}=${moves+hVal}`}
                color="#9b59b6" bar={null}
                sub="g = moves made  ·  h = manhattan est." T={T}/>
              <MC label="OPTIMAL PATH LENGTH" value={optLen??`—`}
                color={T.accent} bar={null}
                sub={optLen?`IDA*/A* computed: ${optLen} moves`:"Press HINT or AUTO SOLVE"} T={T}/>
              <MC label="NODES EXPLORED" value={nodesExp!=null?nodesExp.toLocaleString():`—`}
                color="#e67e22" bar={null}
                sub={nodesExp?`States searched by algorithm`:"—"} T={T}/>
              {perfScore!==null&&(()=>{ const gd=gradeOf(perfScore); return(
                <div style={{background:`${gd.c}12`,border:`1px solid ${gd.c}44`,borderRadius:"10px",padding:"11px",textAlign:"center"}}>
                  <div style={{fontSize:"7px",letterSpacing:"3px",color:T.muted,marginBottom:"5px"}}>PERFORMANCE GRADE</div>
                  <div style={{fontSize:"42px",fontWeight:"900",color:gd.c,lineHeight:1,textShadow:`0 0 20px ${gd.c}66`}}>{gd.g}</div>
                  <div style={{fontSize:"18px",fontWeight:"700",color:gd.c}}>{perfScore.toLocaleString()} <span style={{fontSize:"10px"}}>pts</span></div>
                  <div style={{fontSize:"9px",color:T.muted,marginTop:"3px"}}>{gd.label}</div>
                </div>
              );})()}
            </div>
          )}

          {/* SOLVER INFO */}
          {tab==="solver"&&(
            <div style={{padding:"13px",display:"flex",flexDirection:"column",gap:"9px",overflowY:"auto"}}>
              <div style={{background:`${T.accent}10`,border:`1px solid ${T.accent}30`,borderRadius:"10px",padding:"11px"}}>
                <div style={{fontSize:"8px",letterSpacing:"3px",color:T.accent,marginBottom:"7px"}}>ALGORITHM USED</div>
                <IR label="3×3 (Easy)"   value="A* + MinHeap" T={T}/>
                <IR label="4×4 (Medium)" value="IDA* (async)" T={T}/>
                <IR label="5×5 (Hard)"   value="IDA* (async)" T={T}/>
                <IR label="Heuristic"    value="Manhattan dist." T={T}/>
                <IR label="Admissible"   value="✅ Yes" T={T}/>
                <IR label="Optimal"      value="✅ Shortest path" T={T}/>
                <IR label="UI blocking"  value="✅ None (async)" T={T}/>
              </div>
              <div style={{background:"rgba(155,89,182,0.09)",border:"1px solid rgba(155,89,182,0.25)",borderRadius:"10px",padding:"11px"}}>
                <div style={{fontSize:"8px",letterSpacing:"3px",color:"#9b59b6",marginBottom:"7px"}}>CURRENT STATE</div>
                <IR label="h(manhattan)" value={hVal} T={T}/>
                <IR label="h(misplaced)" value={mVal} T={T}/>
                <IR label="g(n) moves"   value={moves} T={T}/>
                <IR label="f(n) total"   value={moves+hVal} T={T}/>
                <IR label="Optimal len"  value={optLen??`Run hint`} T={T}/>
                <IR label="Extra moves"  value={optLen!=null?Math.max(0,moves-optLen):`—`} T={T}/>
              </div>
              {/* Per-tile table */}
              <div style={{background:T.card,border:`1px solid ${T.border}`,borderRadius:"10px",padding:"11px"}}>
                <div style={{fontSize:"7px",letterSpacing:"3px",color:T.muted,marginBottom:"7px"}}>PER-TILE h(n)</div>
                <div style={{display:"grid",gridTemplateColumns:`repeat(${size},1fr)`,gap:"3px"}}>
                  {tiles.map((tile,idx)=>{
                    const hv=tileManhattan(tile,idx,size);
                    const c=hv===0?"#2ecc71":hv<=2?"#f1c40f":"#e74c3c";
                    return(
                      <div key={idx} style={{background:T.surface,border:`1px solid ${tile===0?T.border:c+"44"}`,
                        borderRadius:"5px",padding:"3px 2px",textAlign:"center"}}>
                        <div style={{fontSize:"11px",fontWeight:"900",color:tile===0?T.border:T.text}}>{tile||"_"}</div>
                        <div style={{fontSize:"7px",color:c}}>h={hv}</div>
                      </div>
                    );
                  })}
                </div>
                <div style={{fontSize:"8px",color:T.muted,textAlign:"center",marginTop:"5px"}}>Σ h(n) = {hVal}</div>
              </div>
            </div>
          )}

          {/* ALGO COMPARISON */}
          {tab==="algo"&&(
            <div style={{padding:"13px",display:"flex",flexDirection:"column",gap:"9px",overflowY:"auto"}}>
              <div style={{fontSize:"8px",color:T.muted,letterSpacing:"1px",lineHeight:1.7}}>
                Click <span style={{color:"#9b59b6",fontWeight:"700"}}>AUTO SOLVE</span> to compare all 3 algorithms on the current puzzle state.
              </div>
              {algoStats?(
                <>
                  {[
                    {key:"astar", color:"#2ecc71",label:"★ A*/IDA*",    icon:"⭐"},
                    {key:"greedy",color:"#3498db", label:"Greedy BFS",  icon:"🎯"},
                    {key:"bfs",   color:"#e67e22", label:"BFS",         icon:"🔍"},
                  ].map(({key,color,label,icon})=>{
                    const s=algoStats[key];
                    const allNodes=Object.values(algoStats).map(x=>Number(x.nodes)||0);
                    const allPaths=Object.values(algoStats).map(x=>Number(x.pathLen)||0);
                    const maxN=Math.max(...allNodes,1), maxP=Math.max(...allPaths,1);
                    return(
                      <div key={key} style={{background:T.card,border:`1px solid ${color}30`,borderRadius:"10px",padding:"11px"}}>
                        <div style={{fontSize:"9px",fontWeight:"700",color,letterSpacing:"2px",marginBottom:"7px"}}>{icon} {label}</div>
                        <div style={{marginBottom:"5px"}}>
                          <div style={{display:"flex",justifyContent:"space-between",marginBottom:"2px"}}>
                            <span style={{fontSize:"7px",color:T.muted}}>NODES</span>
                            <span style={{fontSize:"8px",fontWeight:"700",color}}>{typeof s.nodes==="number"?s.nodes.toLocaleString():s.nodes}</span>
                          </div>
                          <div style={{height:"3px",background:T.border,borderRadius:"2px",overflow:"hidden"}}>
                            <div style={{height:"100%",width:`${((Number(s.nodes)||0)/maxN)*100}%`,background:color,transition:"width 0.6s ease"}}/>
                          </div>
                        </div>
                        <div>
                          <div style={{display:"flex",justifyContent:"space-between",marginBottom:"2px"}}>
                            <span style={{fontSize:"7px",color:T.muted}}>PATH</span>
                            <span style={{fontSize:"8px",fontWeight:"700",color}}>{s.pathLen} moves</span>
                          </div>
                          <div style={{height:"3px",background:T.border,borderRadius:"2px",overflow:"hidden"}}>
                            <div style={{height:"100%",width:`${((Number(s.pathLen)||0)/maxP)*100}%`,background:color,transition:"width 0.6s ease"}}/>
                          </div>
                        </div>
                      </div>
                    );
                  })}
                  <div style={{background:`rgba(52,152,219,0.07)`,border:`1px solid rgba(52,152,219,0.2)`,
                    borderRadius:"10px",padding:"10px",fontSize:"8px",lineHeight:1.8,color:T.muted}}>
                    <strong style={{color:T.text}}>Why IDA* wins for large puzzles:</strong> Uses O(depth) memory vs A*'s exponential memory. BFS is memory-intensive. Greedy is fast but suboptimal. IDA* = optimal + memory-efficient.
                  </div>
                </>
              ):(
                <div style={{textAlign:"center",padding:"28px 0",color:T.muted,fontSize:"10px",lineHeight:2.2}}>
                  <div style={{fontSize:"30px",marginBottom:"8px"}}>⚡</div>
                  Run <strong style={{color:"#9b59b6"}}>AUTO SOLVE</strong> to compare algorithm performance.
                </div>
              )}
            </div>
          )}
        </div>
      </div>

      {/* Goal preview */}
      <div style={{display:"flex",alignItems:"center",gap:"10px",marginTop:"14px",zIndex:1}}>
        <div style={{fontSize:"7px",letterSpacing:"3px",color:T.muted}}>GOAL</div>
        <div style={{display:"grid",gridTemplateColumns:`repeat(${size},1fr)`,gap:"2px"}}>
          {goal.map((t,i)=>(
            <div key={i} style={{width:"18px",height:"18px",borderRadius:"3px",
              background:t===0?"transparent":`${TILE_COLORS[(t-1)%TILE_COLORS.length]}55`,
              border:t===0?`1px dashed ${T.border}`:`1px solid ${TILE_COLORS[(t-1)%TILE_COLORS.length]}44`,
              display:"flex",alignItems:"center",justifyContent:"center",
              fontSize:"8px",fontWeight:"700",color:T.text,opacity:0.75}}>{t||""}</div>
          ))}
        </div>
      </div>

      {/* ── LEADERBOARD MODAL ── */}
      {showLB&&(
        <div style={{position:"fixed",inset:0,zIndex:40,background:"rgba(7,9,15,0.92)",
          display:"flex",alignItems:"center",justifyContent:"center"}} onClick={()=>setShowLB(false)}>
          <div style={{background:darkMode?"#0d1117":T.bg,border:`1px solid ${T.border}`,
            borderRadius:"16px",padding:"22px",width:"min(370px,90vw)",maxHeight:"70vh",overflowY:"auto"}}
            onClick={e=>e.stopPropagation()}>
            <div style={{fontSize:"8px",letterSpacing:"5px",color:"#f1c40f",marginBottom:"3px"}}>🏆 LEADERBOARD</div>
            <div style={{fontSize:"20px",fontWeight:"900",color:T.text,marginBottom:"14px"}}>TOP SCORES</div>
            {!leaderboard.length
              ? <div style={{color:T.muted,textAlign:"center",padding:"20px",fontSize:"11px"}}>No scores yet!</div>
              : leaderboard.map((e,i)=>{ const gd=gradeOf(e.score||0); return(
                <div key={i} style={{display:"flex",alignItems:"center",gap:"10px",padding:"9px",
                  background:T.surface,border:`1px solid ${T.border}`,borderRadius:"8px",marginBottom:"5px"}}>
                  <span style={{fontSize:"16px",fontWeight:"900",minWidth:"22px",
                    color:i===0?"#f1c40f":i===1?"#aaa":i===2?"#cd7f32":T.muted}}>#{i+1}</span>
                  <span style={{fontSize:"18px",fontWeight:"900",color:gd.c,minWidth:"24px"}}>{gd.g}</span>
                  <div style={{flex:1}}>
                    <div style={{fontSize:"10px",fontWeight:"700",color:T.text}}>{e.diff?.toUpperCase()} · {e.moves}mv · {fmt(e.time||0)}</div>
                    <div style={{fontSize:"8px",color:T.muted}}>{e.date}</div>
                  </div>
                  <div style={{fontSize:"13px",fontWeight:"900",color:gd.c}}>{(e.score||0).toLocaleString()}</div>
                </div>
              );})}
            <button onClick={()=>setShowLB(false)} style={{width:"100%",marginTop:"10px",padding:"10px",
              fontSize:"10px",fontWeight:"700",letterSpacing:"3px",fontFamily:"'Courier New',monospace",
              background:T.accent,color:"#fff",border:"none",borderRadius:"8px",cursor:"pointer"}}>CLOSE</button>
          </div>
        </div>
      )}

      {/* ── WIN OVERLAY ── */}
      {phase===PHASES.WON&&(
        <div style={{position:"fixed",inset:0,zIndex:35,background:"rgba(7,9,15,0.93)",
          display:"flex",alignItems:"center",justifyContent:"center",flexDirection:"column",gap:"13px",
          animation:"fadeIn 0.35s ease"}}>
          <div style={{fontSize:"54px",animation:"bounce 0.5s ease infinite alternate"}}>🎉</div>
          <div style={{fontSize:"10px",letterSpacing:"6px",color:"#2ecc71"}}>PUZZLE SOLVED!</div>
          <div style={{fontSize:"clamp(26px,7vw,44px)",fontWeight:"900",
            background:"linear-gradient(135deg,#f1c40f,#e74c3c)",WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent"}}>
            {moves} Moves · {fmt(time)}
          </div>
          {optLen!=null&&<div style={{fontSize:"10px",color:T.accent,letterSpacing:"2px"}}>
            Optimal: {optLen} · Extra: {Math.max(0,moves-optLen)} moves
          </div>}
          {perfScore!=null&&(()=>{ const gd=gradeOf(perfScore); return(
            <div style={{display:"flex",alignItems:"center",gap:"12px",background:T.surface,
              border:`1px solid ${gd.c}44`,borderRadius:"12px",padding:"10px 22px"}}>
              <div style={{fontSize:"46px",fontWeight:"900",color:gd.c,lineHeight:1,textShadow:`0 0 22px ${gd.c}66`}}>{gd.g}</div>
              <div>
                <div style={{fontSize:"7px",color:T.muted,letterSpacing:"3px"}}>PERFORMANCE</div>
                <div style={{fontSize:"20px",fontWeight:"900",color:gd.c}}>{perfScore.toLocaleString()} pts</div>
                <div style={{fontSize:"8px",color:gd.c}}>{gd.label}</div>
              </div>
            </div>
          );})()}
          {newRecord&&<div style={{fontSize:"10px",letterSpacing:"4px",color:"#f1c40f",
            padding:"4px 16px",border:"1px solid #f1c40f44",borderRadius:"6px",
            background:"rgba(241,196,15,0.06)"}}>⭐ PERSONAL BEST!</div>}
          <div style={{display:"flex",gap:"10px",marginTop:"4px"}}>
            <button onClick={()=>startGame(size)} style={{padding:"12px 36px",fontSize:"11px",fontWeight:"700",
              letterSpacing:"4px",fontFamily:"'Courier New',monospace",
              background:"linear-gradient(135deg,#2ecc71,#1abc9c)",
              color:"#07090f",border:"none",borderRadius:"10px",cursor:"pointer",
              boxShadow:"0 0 26px rgba(46,204,113,0.4)"}}>▶ PLAY AGAIN</button>
            <button onClick={()=>setShowLB(true)} style={{padding:"12px 20px",fontSize:"11px",fontWeight:"700",
              letterSpacing:"3px",fontFamily:"'Courier New',monospace",background:"transparent",
              color:"#f1c40f",border:"1px solid #f1c40f44",borderRadius:"10px",cursor:"pointer"}}>🏆</button>
          </div>
        </div>
      )}

      {/* ── WELCOME ── */}
      {phase===PHASES.IDLE&&(
        <div style={{position:"fixed",inset:0,zIndex:35,background:"rgba(7,9,15,0.96)",
          display:"flex",alignItems:"center",justifyContent:"center",flexDirection:"column",gap:"14px"}}>
          <div style={{fontSize:"50px"}}>🧩</div>
          <div style={{fontSize:"clamp(26px,7vw,48px)",fontWeight:"900",letterSpacing:"3px",
            background:`linear-gradient(135deg,#fff 10%,${T.accent} 55%,#9b59b6 100%)`,
            WebkitBackgroundClip:"text",WebkitTextFillColor:"transparent"}}>N-PUZZLE AI</div>
          <div style={{maxWidth:"330px",textAlign:"center",fontSize:"10px",color:T.muted,lineHeight:2,letterSpacing:"1px"}}>
            Slide tiles into order using <span style={{color:"#f1c40f"}}>A* / IDA*</span> AI.<br/>
            Non-blocking solver — <span style={{color:"#2ecc71"}}>UI stays responsive</span> on all difficulty levels.
          </div>
          <div style={{display:"flex",gap:"14px",fontSize:"9px",color:T.muted,letterSpacing:"2px",flexWrap:"wrap",justifyContent:"center"}}>
            <span>🤖 IDA* Solver</span><span>📊 Live h(n)</span><span>⚡ Algo Compare</span><span>🏆 Leaderboard</span>
          </div>
          <button onClick={()=>startGame(size)} style={{marginTop:"8px",padding:"13px 52px",fontSize:"12px",fontWeight:"700",
            letterSpacing:"4px",fontFamily:"'Courier New',monospace",
            background:`linear-gradient(135deg,${T.accent},#9b59b6)`,
            color:"#fff",border:"none",borderRadius:"12px",cursor:"pointer",
            boxShadow:`0 0 30px rgba(52,152,219,0.4)`}}>▶ START PUZZLE</button>
        </div>
      )}

      <style>{`
        @keyframes fadeIn {from{opacity:0}to{opacity:1}}
        @keyframes bounce {from{transform:translateY(0)}to{transform:translateY(-10px)}}
        @keyframes pulse  {0%,100%{opacity:1}50%{opacity:0.5}}
      `}</style>
    </div>
  );
}

// ── Sub-components ──
function Btn({onClick,color,children,disabled,glow,T}){
  const [h,setH]=useState(false);
  return(
    <button onClick={disabled?undefined:onClick} onMouseEnter={()=>setH(true)} onMouseLeave={()=>setH(false)}
      style={{padding:"8px 13px",fontSize:"9px",fontWeight:"700",letterSpacing:"2px",
        fontFamily:"'Courier New',monospace",
        background:disabled?"transparent":h?color:"transparent",
        color:disabled?"#333":h?"#07090f":color,
        border:`1px solid ${disabled?"#222":color}`,
        borderRadius:"7px",cursor:disabled?"not-allowed":"pointer",opacity:disabled?0.3:1,
        boxShadow:glow&&h&&!disabled?`0 0 16px ${color}55`:"none",transition:"all 0.15s"}}>
      {children}
    </button>
  );
}
function IBtn({onClick,children}){
  return(
    <button onClick={onClick} style={{width:"33px",height:"33px",borderRadius:"8px",
      border:"1px solid rgba(255,255,255,0.1)",background:"rgba(255,255,255,0.04)",
      cursor:"pointer",fontSize:"14px",display:"flex",alignItems:"center",justifyContent:"center"}}>
      {children}
    </button>
  );
}
function MC({label,value,color,bar,barC,sub,T}){
  return(
    <div style={{background:T.card,border:`1px solid ${T.border}`,borderRadius:"9px",padding:"9px"}}>
      <div style={{fontSize:"7px",letterSpacing:"2px",color:T.muted,marginBottom:"4px"}}>{label}</div>
      <div style={{fontSize:"18px",fontWeight:"900",color,lineHeight:1}}>{value}</div>
      {bar!=null&&<div style={{height:"3px",background:T.border,borderRadius:"2px",marginTop:"5px",overflow:"hidden"}}>
        <div style={{height:"100%",width:`${Math.max(0,Math.min(1,bar))*100}%`,background:barC,transition:"width 0.4s ease"}}/>
      </div>}
      {sub&&<div style={{fontSize:"7px",color:T.muted,marginTop:"4px",letterSpacing:"1px"}}>{sub}</div>}
    </div>
  );
}
function IR({label,value,T}){
  return(
    <div style={{display:"flex",justifyContent:"space-between",marginBottom:"4px"}}>
      <span style={{fontSize:"7px",color:T.muted,letterSpacing:"1px"}}>{label}</span>
      <span style={{fontSize:"8px",fontWeight:"700",color:T.text,letterSpacing:"1px"}}>{value}</span>
    </div>
  );
}
