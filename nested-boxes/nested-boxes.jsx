import { useState, useEffect, useLayoutEffect, useRef, createContext, useContext, useMemo } from "react";
import { parse, complementAst, astToString, parseCoveringPairs, resolvePosition, VarLabel } from "./formula.jsx";

// ─── Cover context (for highlighting complementary pairs in diagrams) ──────────
const CoverContext = createContext(null);

const PAIR_COLORS = ['#e63946', '#1d7cc4', '#2a9d8f', '#e07c00', '#8e44ad', '#555'];

// ─── Box Renderer ─────────────────────────────────────────────────────────────
const PAD = 10, GAP = 8;
const BORDER_COLORS = ['#111', '#1a6bcc', '#b35000', '#2a7a2a', '#7a1a7a'];

function BoxNode({ node, depth = 0, position = [] }) {
  const cover = useContext(CoverContext);
  if (!node) return null;

  if (node.t === 'VAR') {
    const posKey = position.join(',');
    const pairIndices = cover?.posToPairIndices?.[posKey] ?? [];
    const prefixIndices = (cover?.posToPrefixIndices?.[posKey] ?? [])
      .filter(i => !pairIndices.includes(i)); // don't double-show
    const allIndices = [...pairIndices, ...prefixIndices];
    const hasPair = pairIndices.length > 0;
    const hasPrefix = prefixIndices.length > 0;

    const highlighted = allIndices.length > 0;

    // Sort all indices by original cover index for consistent stacking
    const pairSet = new Set(pairIndices);
    const sorted = highlighted ? [...allIndices].sort((a, b) => a - b) : [];

    // Build colored underline bars — one per cover, stacked below the element.
    // Use global maxBarCount for consistent scaling. Bars split into columns
    // of 8, each column offset horizontally.
    const globalMax = cover?.maxBarCount ?? sorted.length;
    const barsPerCol = 8;
    const colCount = Math.ceil(globalMax / barsPerCol);
    const effectiveMax = Math.min(globalMax, barsPerCol);
    const maxStack = 16;
    const barStep = effectiveMax <= 4 ? 4 : Math.max(1, maxStack / effectiveMax);
    const barHeight = barStep;
    const colWidth = colCount > 1 ? `${100 / colCount}%` : undefined;
    const bars = sorted.map((idx, r) => {
      const col = Math.floor(r / barsPerCol);
      const row = r % barsPerCol;
      const color = cover?.idxToGroupColor?.[idx] ?? PAIR_COLORS[idx % PAIR_COLORS.length];
      const dashed = !pairSet.has(idx);
      return (
        <div key={`bar-${idx}`} style={{
          position: 'absolute',
          left: colCount > 1 ? `${(col / colCount) * 100}%` : -1,
          right: colCount > 1 ? `${((colCount - col - 1) / colCount) * 100}%` : -1,
          bottom: -(2 + row * barStep),
          height: barHeight,
          background: dashed ? undefined : color,
          backgroundImage: dashed ? `repeating-linear-gradient(90deg, ${color} 0px, ${color} ${barHeight + 1}px, transparent ${barHeight + 1}px, transparent ${2 * (barHeight + 1)}px)` : undefined,
          borderRadius: 1,
          pointerEvents: 'none',
        }} />
      );
    });

    // Background tint using the first selected cover's group color
    const firstColor = cover?.idxToGroupColor?.[sorted[0]] ?? PAIR_COLORS[sorted[0] % PAIR_COLORS.length];
    const bgColor = highlighted
      ? (hasPair ? firstColor + '20' : firstColor + '12')
      : undefined;

    return (
      <div
        data-position={posKey}
        style={{
          position: 'relative',
          minWidth: 26, display: 'flex', alignItems: 'center',
          justifyContent: 'center',
          padding: '4px 6px',
          fontSize: 17, fontFamily: 'Georgia, serif',
          fontWeight: 'bold', lineHeight: 1, userSelect: 'none',
          ...(bgColor ? { background: bgColor, borderRadius: 3 } : {}),
        }}
      >
        {bars}
        <VarLabel name={node.n} />
      </div>
    );
  }

  const isOR  = node.t === 'OR';
  const color = BORDER_COLORS[depth % BORDER_COLORS.length];

  return (
    <div style={{
      border: `2px solid ${color}`, borderRadius: 3, padding: PAD,
      display: 'inline-flex',
      flexDirection: isOR ? 'row' : 'column',
      alignItems: 'center', justifyContent: 'center',
      gap: GAP, boxSizing: 'border-box',
      overflow: 'visible',
    }}>
      {node.c.map((child, i) => <BoxNode key={i} node={child} depth={depth + 1} position={[...position, i]} />)}
    </div>
  );
}

// ─── Diagram with SVG arc connections for covering pairs ──────────────────────
function DiagramWithConnections({ node, coveringPairs, coveredPrefixes, selectedIndices }) {
  const containerRef = useRef(null);
  const [arcs, setArcs] = useState([]);
  const [pathLines, setPathLines] = useState([]);

  const parsed = useMemo(
    () => (coveringPairs?.length ? parseCoveringPairs(coveringPairs) : []),
    [coveringPairs]
  );

  // Only include selected indices; preserve original index for consistent colors
  const selected = selectedIndices;

  const posToPairIndices = useMemo(() => {
    const m = {};
    parsed.forEach(([posA, posB], i) => {
      if (!selected.has(i)) return;
      const ka = posA.join(','), kb = posB.join(',');
      (m[ka] ??= []).push(i);
      (m[kb] ??= []).push(i);
    });
    return m;
  }, [parsed, selected]);

  const posToPrefixIndices = useMemo(() => {
    const m = {};
    if (coveredPrefixes) {
      coveredPrefixes.forEach((positions, i) => {
        if (!selected.has(i)) return;
        positions.forEach(pos => {
          const key = pos.join(',');
          (m[key] ??= []).push(i);
        });
      });
    }
    return m;
  }, [coveredPrefixes, selected]);

  // Map each cover index to a group color (indices with same pair positions share a color)
  const idxToGroupColor = useMemo(() => {
    const m = {};
    let groupIdx = 0;
    const seen = {};
    parsed.forEach(([posA, posB], i) => {
      const key = posA.join(',') + '|' + posB.join(',');
      if (!(key in seen)) {
        seen[key] = groupIdx++;
      }
      m[i] = PAIR_COLORS[seen[key] % PAIR_COLORS.length];
    });
    return m;
  }, [parsed]);

  // Compute max bar count across all positions for consistent scaling
  const maxBarCount = useMemo(() => {
    const counts = {};
    for (const [key, indices] of Object.entries(posToPairIndices)) {
      counts[key] = (counts[key] ?? 0) + indices.length;
    }
    for (const [key, indices] of Object.entries(posToPrefixIndices)) {
      // Only count prefix indices not already counted as pairs
      const pairSet = new Set(posToPairIndices[key] ?? []);
      counts[key] = (counts[key] ?? 0) + indices.filter(i => !pairSet.has(i)).length;
    }
    return Math.max(0, ...Object.values(counts));
  }, [posToPairIndices, posToPrefixIndices]);

  // Recompute arc positions and path lines after every render (DOM may have changed)
  useLayoutEffect(() => {
    if (!containerRef.current || !parsed.length) {
      setArcs(prev => prev.length === 0 ? prev : []);
      setPathLines(prev => prev.length === 0 ? prev : []);
      return;
    }
    const container = containerRef.current;
    // Walk offsetParent chain to get layout coords relative to container.
    const boundsOf = el => {
      let x = 0, y = 0, cur = el;
      while (cur && cur !== container) { x += cur.offsetLeft; y += cur.offsetTop; cur = cur.offsetParent; }
      return { x, y, w: el.offsetWidth, h: el.offsetHeight };
    };

    const newArcs = [];
    parsed.forEach(([posA, posB], pairIdx) => {
      if (!selected.has(pairIdx)) return;
      const da = container.querySelector(`[data-position="${posA.join(',')}"]`);
      const db = container.querySelector(`[data-position="${posB.join(',')}"]`);
      if (!da || !db) return;
      const ba = boundsOf(da), bb = boundsOf(db);
      newArcs.push({
        x1: ba.x + ba.w / 2, y1: ba.y + ba.h / 2,
        x2: bb.x + bb.w / 2, y2: bb.y + bb.h / 2,
        pairIdx,
      });
    });

    // Path connection lines: connect consecutive positions in each prefix
    const newPathLines = [];
    if (coveredPrefixes) {
      coveredPrefixes.forEach((positions, idx) => {
        if (!selected.has(idx)) return;
        const color = idxToGroupColor[idx] ?? PAIR_COLORS[idx % PAIR_COLORS.length];
        for (let k = 0; k < positions.length - 1; k++) {
          const da = container.querySelector(`[data-position="${positions[k].join(',')}"]`);
          const db = container.querySelector(`[data-position="${positions[k + 1].join(',')}"]`);
          if (!da || !db) continue;
          const ba = boundsOf(da), bb = boundsOf(db);
          newPathLines.push({
            x1: ba.x + ba.w, y1: ba.y + ba.h + 3,
            x2: bb.x,        y2: bb.y + bb.h + 3,
            color,
          });
        }
      });
    }

    setArcs(prev => JSON.stringify(prev) === JSON.stringify(newArcs) ? prev : newArcs);
    setPathLines(prev => JSON.stringify(prev) === JSON.stringify(newPathLines) ? prev : newPathLines);
  });

  return (
    <CoverContext.Provider value={(Object.keys(posToPairIndices).length || Object.keys(posToPrefixIndices).length) ? { posToPairIndices, posToPrefixIndices, maxBarCount, idxToGroupColor } : null}>
      <div ref={containerRef} style={{ position: 'relative', display: 'inline-block' }}>
        <BoxNode node={node} depth={0} />
        {(arcs.length > 0 || pathLines.length > 0) && (
          <svg style={{
            position: 'absolute', top: 0, left: 0,
            width: '100%', height: '100%',
            pointerEvents: 'none', overflow: 'visible',
          }}>
            {pathLines.map((ln, i) => (
              <line key={`pl${i}`}
                x1={ln.x1} y1={ln.y1} x2={ln.x2} y2={ln.y2}
                stroke={ln.color} strokeWidth={1} strokeOpacity={0.5}
              />
            ))}
            {arcs.map((arc, i) => {
              const mx = (arc.x1 + arc.x2) / 2;
              const miny = Math.min(arc.y1, arc.y2);
              const dx = arc.x2 - arc.x1, dy = arc.y2 - arc.y1;
              const dist = Math.sqrt(dx * dx + dy * dy) || 1;
              const voff = Math.max(28, dist * 0.4);
              // Control point: above both endpoints
              const qcx = mx;
              const qcy = miny - voff;
              const color = idxToGroupColor[arc.pairIdx] ?? PAIR_COLORS[arc.pairIdx % PAIR_COLORS.length];
              return (
                <g key={i}>
                  <path
                    d={`M ${arc.x1} ${arc.y1} Q ${qcx} ${qcy} ${arc.x2} ${arc.y2}`}
                    fill="none" stroke={color} strokeWidth={2}
                    strokeOpacity={0.8} strokeDasharray="6 3"
                  />
                  <circle cx={arc.x1} cy={arc.y1} r={3.5} fill={color} fillOpacity={0.85} />
                  <circle cx={arc.x2} cy={arc.y2} r={3.5} fill={color} fillOpacity={0.85} />
                </g>
              );
            })}
          </svg>
        )}
      </div>
    </CoverContext.Provider>
  );
}

// ─── Zoom / Pan wrapper ────────────────────────────────────────────────────────
function ZoomPanWrapper({ children, bg = '#f8f9fc', border = '1px solid #dde', opacity = 1 }) {
  const viewRef    = useRef(null);
  const contentRef = useRef(null);
  const scaleRef   = useRef(1);
  const txRef      = useRef(0);
  const tyRef      = useRef(0);
  const dragRef    = useRef(null);
  const fitRef     = useRef({ scale: 1, x: 0, y: 0 }); // saved fit-to-window transform
  const [display, setDisplay]   = useState({ scale: 1, x: 0, y: 0 });
  const [dragging, setDragging] = useState(false);

  const commit = (s, x, y) => {
    scaleRef.current = s; txRef.current = x; tyRef.current = y;
    setDisplay({ scale: s, x, y });
  };

  // On mount: scale content to fit the viewport, centered
  useLayoutEffect(() => {
    const view = viewRef.current, content = contentRef.current;
    if (!view || !content) return;
    const vw = view.offsetWidth,  vh = view.offsetHeight;
    const cw = content.offsetWidth, ch = content.offsetHeight;
    if (!cw || !ch) return;
    const s  = Math.min(vw / cw, vh / ch, 1);
    const tx = (vw - cw * s) / 2;
    const ty = (vh - ch * s) / 2;
    fitRef.current = { scale: s, x: tx, y: ty };
    commit(s, tx, ty);
  }, []); // runs once on mount; key prop remounts on formula change

  // Non-passive wheel for zoom-to-cursor
  useEffect(() => {
    const el = viewRef.current;
    if (!el) return;
    const onWheel = e => {
      e.preventDefault();
      const rect = el.getBoundingClientRect();
      const mx = e.clientX - rect.left, my = e.clientY - rect.top;
      const s  = scaleRef.current;
      const ns = Math.max(0.1, Math.min(10, s * (e.deltaY < 0 ? 1.12 : 1 / 1.12)));
      commit(ns, mx - (mx - txRef.current) * (ns / s), my - (my - tyRef.current) * (ns / s));
    };
    el.addEventListener('wheel', onWheel, { passive: false });
    return () => el.removeEventListener('wheel', onWheel);
  }, []);

  const onMouseDown = e => {
    if (e.button !== 0) return;
    e.preventDefault();
    dragRef.current = { sx: e.clientX, sy: e.clientY, ox: txRef.current, oy: tyRef.current };
    setDragging(true);
  };
  const onMouseMove = e => {
    if (!dragRef.current) return;
    const { sx, sy, ox, oy } = dragRef.current;
    commit(scaleRef.current, ox + (e.clientX - sx), oy + (e.clientY - sy));
  };
  const onMouseUp = () => { dragRef.current = null; setDragging(false); };

  const zoomBy = f => commit(Math.max(0.1, Math.min(10, scaleRef.current * f)), txRef.current, tyRef.current);
  const reset  = () => {
    const view = viewRef.current, content = contentRef.current;
    if (!view || !content) { const { scale, x, y } = fitRef.current; commit(scale, x, y); return; }
    const vw = view.offsetWidth,  vh = view.offsetHeight;
    const cw = content.offsetWidth, ch = content.offsetHeight;
    if (!cw || !ch) return;
    const s  = Math.min(vw / cw, vh / ch, 1);
    const tx = (vw - cw * s) / 2;
    const ty = (vh - ch * s) / 2;
    fitRef.current = { scale: s, x: tx, y: ty };
    commit(s, tx, ty);
  };

  const cBtn = (label, fn, title) => (
    <button onClick={fn} title={title} style={{
      padding: '1px 7px', fontSize: 13, fontWeight: 'bold', lineHeight: 1.6,
      border: '1px solid #ccc', borderRadius: 3,
      background: 'rgba(255,255,255,0.92)', cursor: 'pointer', color: '#333',
    }}>{label}</button>
  );

  return (
    <div style={{ position: 'relative', borderRadius: 8, border, background: bg,
                  opacity, transition: 'opacity 0.15s' }}>
      <div
        ref={viewRef}
        onMouseDown={onMouseDown}
        onMouseMove={onMouseMove}
        onMouseUp={onMouseUp}
        onMouseLeave={onMouseUp}
        style={{ overflow: 'hidden', cursor: dragging ? 'grabbing' : 'grab',
                 userSelect: 'none', position: 'relative', height: 360 }}
      >
        <div ref={contentRef} style={{
          position: 'absolute', top: 0, left: 0, width: 'max-content',
          transformOrigin: '0 0',
          transform: `translate(${display.x}px, ${display.y}px) scale(${display.scale})`,
          padding: '50px 40px 40px',  // extra padding so arc curves and box-shadow rings aren't clipped
        }}>
          {children}
        </div>
      </div>
      <div style={{
        position: 'absolute', top: 6, right: 6,
        display: 'flex', gap: 3, alignItems: 'center',
        background: 'rgba(255,255,255,0.85)', borderRadius: 4, padding: '2px 5px',
      }}>
        {cBtn('+', () => zoomBy(1.25), 'Zoom in')}
        {cBtn('−', () => zoomBy(1 / 1.25), 'Zoom out')}
        {cBtn('↺', reset, 'Reset')}
        <span style={{ fontSize: 11, color: '#666', minWidth: 30, textAlign: 'right' }}>
          {Math.round(display.scale * 100)}%
        </span>
      </div>
    </div>
  );
}

// ─── Legend ───────────────────────────────────────────────────────────────────
function Legend() {
  const box = (dir, color, children) => (
    <span style={{
      display: 'inline-flex', border: `2px solid ${color}`, padding: '2px 8px',
      gap: 4, verticalAlign: 'middle', fontSize: 13,
      fontFamily: 'Georgia, serif', fontWeight: 'bold',
      borderRadius: 2, flexDirection: dir,
    }}>{children}</span>
  );
  return (
    <div style={{
      display: 'flex', gap: 24, flexWrap: 'wrap', fontSize: 13, color: '#444',
      marginBottom: 18, background: '#f0f4ff', padding: '10px 16px', borderRadius: 6,
    }}>
      <span style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
        <b>AND (·)</b> →
        {box('column', '#111', [<span key="a">A</span>, <span key="b">B</span>])}
        <span style={{ color: '#666' }}>stacked vertically</span>
      </span>
      <span style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
        <b>OR (+)</b> →
        {box('row', '#1a6bcc', [<span key="a">A</span>, <span key="b">B</span>])}
        <span style={{ color: '#666' }}>side by side</span>
      </span>
    </div>
  );
}

// ─── Examples ─────────────────────────────────────────────────────────────────
const EXAMPLES = [
  { label: "CLP(B) #1",    f: "((A·B) + (A'+B')) · ((A'+B') + (A·B))" },
  { label: "CLP(B) #2",   f: "A (R' + S') + A' (R S) + B T + B' T' + A X'" },
  { label: "Simple AND",   f: "A · B · C" },
  { label: "Simple OR",    f: "A + B + C" },
  { label: "Mixed",        f: "(A·B) + (C·D)" },
  { label: "XOR-like",     f: "(A·B') + (A'·B)" },
  { label: "Distributive", f: "A · (B + C)" },
  { label: "De Morgan",    f: "(A'+B') · (A+B)" },
  { label: "Matings",      f: "L K' + L' M + M' + K + L K" },
  { label: "Full Adder",  f: "X Y U1 + (X' + Y') U1' + U3 C1 U2 + (U3' + C1') U2' + (U1+U3) C + U1' U2' C' + ((X·Y') + (X'·Y)) U3 + (X' + Y) (X + Y') U3' + ((U3·C1') + (U3'·C1)) Z3 + (U3' + C1) (U3 + C1') Z3'" },
  { label: "R",           f: "(a+b+c')(b+c+d')(c+d+a)(d+a'+b)(a'+b'+c)(b'+c'+d)(c'+d'+a')(d'+a+b')" },
  { label: "R-prime",     f: "(a+b+c')(b+c+d')(c+d+a)(d+a'+b)(a'+b'+c)(b'+c'+d)(c'+d'+a')" },
];

// ─── Main App ─────────────────────────────────────────────────────────────────
export default function App() {
  const [examples,       setExamples]       = useState(EXAMPLES);
  const [examplesOpen,   setExamplesOpen]   = useState(true);
  const [addingLabel,    setAddingLabel]    = useState('');   // '' = not adding
  const [saveMsg,        setSaveMsg]        = useState('');
  const [input,          setInput]          = useState(EXAMPLES[0].f);
  const [simplified,     setSimplified]     = useState(null); // {formula, ast}
  const [simplifyMsg,    setSimplifyMsg]    = useState(null); // {text, ok}
  const [complementData, setComplementData] = useState(null); // {formula, ast}
  const [validResult,    setValidResult]    = useState(null); // {valid, path}
  const [validSelected,  setValidSelected]  = useState(new Set()); // Set<number> of selected pair indices
  const [validExpanded,  setValidExpanded]  = useState(new Set()); // Set<number> of expanded group indices
  const [satResult,      setSatResult]      = useState(null); // {satisfiable, path, coveringPairs}
  const [satSelected,    setSatSelected]    = useState(new Set()); // Set<number> of selected pair indices
  const [satExpanded,    setSatExpanded]    = useState(new Set()); // Set<number> of expanded group indices
  const [pathsResult,    setPathsResult]    = useState(null); // {coveredPaths, uncoveredPaths, ...} | {error}
  const [pathsLimit,     setPathsLimit]     = useState(100);
  const [loading,        setLoading]        = useState(false);
  const [jqFilter,       setJqFilter]       = useState('');
  const [jqError,        setJqError]        = useState('');
  const [jqLibPath,      setJqLibPath]      = useState('');
  const [jqLibs,         setJqLibs]         = useState([]);    // [{path, name, content}] from server
  const [jqLibLoading,   setJqLibLoading]   = useState(false);
  const [jqLibError,     setJqLibError]     = useState('');
  const [jqLibViewing,   setJqLibViewing]   = useState(null); // {name, content} | null
  const [jqLibFiles,     setJqLibFiles]     = useState([]);   // available .jq filenames
  const [jqOpen,         setJqOpen]         = useState(false);
  const inputRef = useRef(null);

  // Parse synchronously so ast is always current on the same render as input
  const [ast, error] = useMemo(() => {
    try { return [parse(input), '']; }
    catch (e) { return [null, e.message]; }
  }, [input]);

  // Run jq filter live as it is typed; push result into formula input
  useEffect(() => {
    if (!jqFilter.trim()) { setJqError(''); return; }
    const id = setTimeout(async () => {
      try {
        const res  = await fetch('http://localhost:3001/jq', {
          method: 'POST', headers: { 'Content-Type': 'application/json' },
          body: JSON.stringify({ filter: jqFilter }),
        });
        const data = await res.json();
        if (data.error) {
          setJqError(data.error);
        } else {
          const out = data.results;
          if (out && out.length > 0) {
            const val = out[0];
            setInput(typeof val === 'string' ? val : JSON.stringify(val));
            setJqError('');
          } else {
            setJqError('Filter produced no output');
          }
        }
      } catch {
        setJqError('Could not reach Rust service');
      }
    }, 300);
    return () => clearTimeout(id);
  }, [jqFilter, jqLibs]);

  const refreshJqLibs = async () => {
    try {
      const res  = await fetch('http://localhost:3001/jq-lib');
      const data = await res.json();
      setJqLibs(data.libs ?? []);
    } catch {}
  };

  const handleLoadJqLib = async () => {
    if (!jqLibPath.trim()) return;
    setJqLibLoading(true);
    setJqLibError('');
    try {
      const res  = await fetch('http://localhost:3001/jq-lib', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ path: jqLibPath.trim() }),
      });
      const data = await res.json();
      if (data.error) { setJqLibError(data.error); }
      else { setJqLibPath(''); await refreshJqLibs(); }
    } catch {
      setJqLibError('Could not reach Rust service');
    }
    setJqLibLoading(false);
  };

  const handleUnloadJqLib = async (path) => {
    try {
      await fetch('http://localhost:3001/jq-lib', {
        method: 'DELETE', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ path }),
      });
      await refreshJqLibs();
    } catch {}
  };

  // Clear derived state when input changes
  useEffect(() => {
    setSimplified(null);
    setComplementData(null);
    setValidResult(null);
    setValidSelected(new Set());
    setValidExpanded(new Set());
    setSatResult(null);
    setSatSelected(new Set());
    setSatExpanded(new Set());
    setPathsResult(null);
  }, [input]);

  // Load examples from file on mount
  useEffect(() => {
    fetch('http://localhost:3001/examples')
      .then(r => r.json())
      .then(data => { if (data.examples) setExamples(data.examples); })
      .catch(() => {});
  }, []);

  // Load jq lib list and available files from server on mount
  useEffect(() => {
    refreshJqLibs();
    fetch('http://localhost:3001/jq-lib/files')
      .then(r => r.json())
      .then(data => { if (data.files) setJqLibFiles(data.files); })
      .catch(() => {});
  }, []);

  const handleSaveExamples = async () => {
    try {
      const res  = await fetch('http://localhost:3001/examples', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify(examples),
      });
      const data = await res.json();
      setSaveMsg(data.ok ? '✓ Saved' : `✗ ${data.error}`);
    } catch {
      setSaveMsg('✗ Could not reach service');
    }
    setTimeout(() => setSaveMsg(''), 2500);
  };

  const handleAddExample = () => {
    const label = addingLabel.trim();
    if (!label) return;
    setExamples(prev => [...prev, { label, f: input }]);
    setAddingLabel('');
  };

  // Insert a character at the cursor position
  const insertAt = (char) => {
    const el = inputRef.current;
    if (!el) return;
    const s = el.selectionStart, e = el.selectionEnd;
    const next = input.slice(0, s) + char + input.slice(e);
    setInput(next);
    setTimeout(() => { el.selectionStart = el.selectionEnd = s + char.length; el.focus(); }, 0);
  };

  const handleSimplify = async () => {
    setLoading(true);
    try {
      const res = await fetch('http://localhost:3001/simplify', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      const data = await res.json();
      if (data.error) {
        setSimplifyMsg({ text: `✗ ${data.error}`, ok: false });
      } else {
        const result = data.result;
        const inputNorm = input.replace(/\s+/g, '');
        const resultNorm = result.replace(/\s+/g, '');
        if (inputNorm === resultNorm) {
          setSimplifyMsg({ text: '✓ Already in minimal SOP form', ok: true });
          setSimplified(null);
        } else {
          setSimplifyMsg({ text: '✓ Simplified!', ok: true });
          setSimplified({ formula: result, ast: parse(result) });
        }
      }
    } catch (e) {
      setSimplifyMsg({ text: '✗ Could not reach Rust service — is it running? (cargo run)', ok: false });
    }
    setLoading(false);
    setTimeout(() => setSimplifyMsg(null), 3500);
  };

  const handlePaths = async () => {
    if (pathsResult && !pathsResult.error) { setPathsResult(null); return; }
    setLoading(true);
    try {
      const res  = await fetch('http://localhost:3001/paths', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input, paths_limit: pathsLimit }),
      });
      const data = await res.json();
      if (data.error) setPathsResult({ error: data.error });
      else setPathsResult({
        coveredPaths: data.covered_paths,
        uncoveredPaths: data.uncovered_paths,
        coveringPairs: data.covering_pairs,
        coveredPrefixes: data.covered_path_prefixes,
      });
    } catch (e) {
      setPathsResult({ error: 'Could not reach Rust service' });
    }
    setLoading(false);
  };

  const handleComplement = () => {
    if (!ast) return;
    if (complementData) { setComplementData(null); return; }
    const cAst = complementAst(ast);
    setComplementData({ formula: astToString(cAst), ast: cAst });
  };

  const handleValid = async () => {
    if (validResult && !validResult.error) { setValidResult(null); return; }
    setLoading(true);
    try {
      const res  = await fetch('http://localhost:3001/valid', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      const data = await res.json();
      if (data.error) setValidResult({ error: data.error });
      else            setValidResult({ valid: data.valid, path: data.path, coveringPairs: data.covering_pairs, coveredPrefixes: data.covered_path_prefixes });
    } catch (e) {
      setValidResult({ error: 'Could not reach Rust service' });
    }
    setLoading(false);
  };

  const handleSatisfiable = async () => {
    if (satResult && !satResult.error) { setSatResult(null); return; }
    setLoading(true);
    try {
      const res  = await fetch('http://localhost:3001/satisfiable', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      const data = await res.json();
      if (data.error) {
        setSatResult({ error: data.error });
      } else {
        setSatResult({ satisfiable: data.satisfiable, path: data.path, coveringPairs: data.covering_pairs, coveredPrefixes: data.covered_path_prefixes });
        // Covering pairs are from the complement — auto-show it for annotation
        if (!data.satisfiable && ast) {
          const cAst = complementAst(ast);
          setComplementData({ formula: astToString(cAst), ast: cAst });
        }
      }
    } catch (e) {
      setSatResult({ error: 'Could not reach Rust service' });
    }
    setLoading(false);
  };

  const btn = (label, onClick, color = '#333', disabled = false, title = '') => (
    <button onClick={onClick} disabled={disabled} title={title} style={{
      padding: '9px 14px', background: disabled ? '#aaa' : color,
      color: 'white', border: 'none', borderRadius: 5,
      cursor: disabled ? 'not-allowed' : 'pointer',
      fontSize: 14, fontWeight: 'bold', minWidth: 38, flexShrink: 0,
      transition: 'background 0.15s',
    }}>{label}</button>
  );

  return (
    <div style={{
      fontFamily: 'system-ui, sans-serif', padding: 28,
      maxWidth: 900, margin: '0 auto', background: '#fff', minHeight: '100vh',
    }}>

      {/* Header */}
      <h2 style={{ margin: '0 0 4px', fontSize: 22, color: '#111' }}>
        Boolean Formula → Nested Box Diagram
      </h2>
      <p style={{ margin: '0 0 18px', color: '#666', fontSize: 13 }}>
        Diagram updates live as you type. Use <b>Simplify</b> to reduce to minimal sum-of-products form.
      </p>

      <Legend />

      {/* jq filter input */}
      <div style={{ marginBottom: 8 }}>
        <div
          onClick={() => setJqOpen(o => !o)}
          style={{
            display: 'flex', alignItems: 'center', gap: 6, cursor: 'pointer',
            userSelect: 'none', fontSize: 13, color: '#555', marginBottom: jqOpen ? 6 : 0,
          }}
        >
          <span style={{ fontSize: 10, fontFamily: 'monospace', color: '#999' }}>{jqOpen ? '▼' : '▶'}</span>
          <span style={{ fontWeight: 500 }}>jq</span>
        </div>
        {jqOpen && <>
          <div style={{ fontSize: 12, color: '#888', marginBottom: 4 }}>
            <div style={{ display: 'flex', alignItems: 'center', gap: 6, marginBottom: 4 }}>
              <span style={{ color: '#aaa' }}>jq library:</span>
              <input
                value={jqLibPath}
                onChange={e => { setJqLibPath(e.target.value); setJqLibError(''); }}
                onKeyDown={e => e.key === 'Enter' && handleLoadJqLib()}
                placeholder="lib.jq"
                list="jq-lib-files"
                style={{
                  padding: '2px 7px', fontSize: 12, fontFamily: 'monospace',
                  border: `1px solid ${jqLibError ? '#c00' : '#ccc'}`,
                  borderRadius: 4, outline: 'none', width: 220,
                }}
              />
              <datalist id="jq-lib-files">
                {jqLibFiles.map(f => <option key={f} value={f} />)}
              </datalist>
              <button onClick={handleLoadJqLib} disabled={jqLibLoading || !jqLibFiles.includes(jqLibPath.trim())} style={{
                padding: '2px 8px', fontSize: 12, border: '1px solid #bbb',
                borderRadius: 4, cursor: 'pointer', background: '#f5f5f5',
              }}>{jqLibLoading ? '…' : 'Load'}</button>
              {jqLibError && (
                <span style={{ color: '#c00' }} title={jqLibError}>✗ {jqLibError}</span>
              )}
            </div>
            {jqLibs.length > 0 && (
              <div style={{ display: 'flex', flexWrap: 'wrap', gap: 4, marginBottom: 4 }}>
                {jqLibs.map(lib => (
                  <span key={lib.path} style={{
                    display: 'inline-flex', alignItems: 'center', gap: 4,
                    background: '#e8f5e9', border: '1px solid #a5d6a7',
                    borderRadius: 4, padding: '1px 6px', fontSize: 11,
                  }}>
                    <button onClick={() => setJqLibViewing(lib)} title={lib.path} style={{
                      border: 'none', background: 'none', cursor: 'pointer',
                      fontFamily: 'monospace', color: '#2a7a2a', padding: 0,
                      fontSize: 11, textDecoration: 'underline dotted',
                    }}>{lib.name}</button>
                    <button onClick={() => handleUnloadJqLib(lib.path)} style={{
                      border: 'none', background: 'none', cursor: 'pointer',
                      color: '#888', padding: 0, fontSize: 11, lineHeight: 1,
                    }}>✕</button>
                  </span>
                ))}
              </div>
            )}

            {jqLibViewing && (
              <div onClick={() => setJqLibViewing(null)} style={{
                position: 'fixed', inset: 0, background: 'rgba(0,0,0,0.45)',
                zIndex: 1000, display: 'flex', alignItems: 'center', justifyContent: 'center',
              }}>
                <div onClick={e => e.stopPropagation()} style={{
                  background: '#fff', borderRadius: 8, boxShadow: '0 8px 32px rgba(0,0,0,0.25)',
                  width: 'min(700px, 90vw)', maxHeight: '80vh',
                  display: 'flex', flexDirection: 'column', overflow: 'hidden',
                }}>
                  <div style={{
                    display: 'flex', alignItems: 'center', justifyContent: 'space-between',
                    padding: '10px 16px', borderBottom: '1px solid #e0e0e0',
                  }}>
                    <span style={{ fontFamily: 'monospace', fontWeight: 600, fontSize: 14 }}>
                      {jqLibViewing.name}.jq
                    </span>
                    <span style={{ fontSize: 11, color: '#999', flex: 1, marginLeft: 12, overflow: 'hidden', textOverflow: 'ellipsis', whiteSpace: 'nowrap' }}>
                      {jqLibViewing.path}
                    </span>
                    <button onClick={() => setJqLibViewing(null)} style={{
                      border: 'none', background: 'none', cursor: 'pointer',
                      fontSize: 18, color: '#888', marginLeft: 12, lineHeight: 1,
                    }}>✕</button>
                  </div>
                  <pre style={{
                    margin: 0, padding: '14px 16px', overflow: 'auto',
                    fontFamily: 'monospace', fontSize: 13, lineHeight: 1.6,
                    background: '#fafafa', color: '#222', whiteSpace: 'pre',
                  }}>{jqLibViewing.content}</pre>
                </div>
              </div>
            )}
            <span>jq filter <span style={{ color: '#aaa' }}>(result replaces formula)</span></span>
          </div>
          <textarea
            value={jqFilter}
            onChange={e => setJqFilter(e.target.value)}
            rows={2}
            style={{
              width: '100%', padding: '7px 11px', fontSize: 13,
              fontFamily: 'monospace',
              border: `1.5px solid ${jqError ? '#c00' : '#ccc'}`,
              borderRadius: 5, outline: 'none', resize: 'vertical',
              boxSizing: 'border-box', lineHeight: 1.5,
              background: jqFilter.trim() ? '#fffef8' : '#fafafa',
            }}
            placeholder={'e.g. "A + B + C"  or  ["A","B","C"] | join(" + ")'}
            spellCheck={false}
          />
          {jqError && (
            <div style={{ fontSize: 12, color: '#c00', marginTop: 2 }}>{jqError}</div>
          )}
        </>}
      </div>

      {/* Examples */}
      <div style={{ marginBottom: 10 }}>
        <div
          onClick={() => setExamplesOpen(prev => !prev)}
          style={{
            display: 'flex', alignItems: 'center', gap: 6, cursor: 'pointer',
            userSelect: 'none', fontSize: 13, color: '#555', marginBottom: examplesOpen ? 6 : 0,
          }}
        >
          <span style={{ fontSize: 10, fontFamily: 'monospace', color: '#999' }}>{examplesOpen ? '▼' : '▶'}</span>
          <span style={{ fontWeight: 500 }}>Examples</span>
        </div>
        {examplesOpen && (
          <>
            <div style={{ display: 'flex', gap: 6, flexWrap: 'wrap', marginBottom: 6, alignItems: 'center' }}>
              {examples.map(({ label, f }, i) => (
                <span key={i} style={{ display: 'inline-flex', alignItems: 'center' }}>
                  <button onClick={() => setInput(f)} style={{
                    padding: '4px 11px', fontSize: 12, fontFamily: 'Georgia, serif',
                    border: '1px solid #ccc', borderRadius: '4px 0 0 4px', cursor: 'pointer',
                    background: input === f ? '#e8eeff' : '#fafafa', color: '#333',
                  }}>
                    {label}
                  </button>
                  <button
                    onClick={() => setExamples(prev => prev.filter((_, j) => j !== i))}
                    title="Remove example"
                    style={{
                      padding: '4px 6px', fontSize: 11, border: '1px solid #ccc',
                      borderLeft: 'none', borderRadius: '0 4px 4px 0',
                      cursor: 'pointer', background: '#fafafa', color: '#999',
                      lineHeight: 1,
                    }}
                  >✕</button>
                </span>
              ))}
            </div>
            <div style={{ display: 'flex', gap: 6, flexWrap: 'wrap', alignItems: 'center' }}>
              {addingLabel !== null && (
                <>
                  <input
                    value={addingLabel}
                    onChange={e => setAddingLabel(e.target.value)}
                    onKeyDown={e => { if (e.key === 'Enter') handleAddExample(); if (e.key === 'Escape') setAddingLabel(''); }}
                    placeholder="Label for current formula…"
                    autoFocus
                    style={{
                      padding: '4px 8px', fontSize: 12, border: '1px solid #bbb',
                      borderRadius: 4, outline: 'none', width: 200,
                    }}
                  />
                  <button onClick={handleAddExample} disabled={!addingLabel.trim()} style={{
                    padding: '4px 10px', fontSize: 12, border: '1px solid #aaa',
                    borderRadius: 4, cursor: 'pointer', background: '#f0f4ff',
                  }}>Add</button>
                  <button onClick={() => setAddingLabel('')} style={{
                    padding: '4px 8px', fontSize: 12, border: '1px solid #ccc',
                    borderRadius: 4, cursor: 'pointer', background: '#fafafa', color: '#666',
                  }}>Cancel</button>
                </>
              )}
              <button onClick={() => setAddingLabel(prev => prev === '' ? ' ' : '')} title="Add current formula as example" style={{
                padding: '4px 10px', fontSize: 12, border: '1px solid #bbb',
                borderRadius: 4, cursor: 'pointer', background: '#fafafa', color: '#444',
              }}>＋ Add example</button>
              <button onClick={handleSaveExamples} style={{
                padding: '4px 10px', fontSize: 12, border: '1px solid #bbb',
                borderRadius: 4, cursor: 'pointer', background: '#fafafa', color: '#444',
              }}>💾 Save</button>
              {saveMsg && <span style={{ fontSize: 12, color: saveMsg.startsWith('✓') ? '#2a7a2a' : '#c00' }}>{saveMsg}</span>}
            </div>
          </>
        )}
      </div>

      {/* Input */}
      <textarea
        ref={inputRef}
        value={input}
        onChange={e => setInput(e.target.value)}
        rows={3}
        style={{
          width: '100%', padding: '9px 13px', fontSize: 15,
          fontFamily: 'Georgia, serif',
          border: `1.5px solid ${error ? '#c00' : '#bbb'}`,
          borderRadius: 5, outline: 'none', transition: 'border-color 0.2s',
          resize: 'vertical', boxSizing: 'border-box', marginBottom: 8,
          lineHeight: 1.5,
        }}
        placeholder={"Type a formula, e.g. (A·B) + (A'+B')"}
        spellCheck={false}
        autoFocus
      />

      {/* Button row */}
      <div style={{ display: 'flex', gap: 16, marginBottom: 8, flexWrap: 'wrap' }}>
        <div style={{ display: 'flex', gap: 4 }}>
          {btn('·',  () => insertAt('·'),   '#555', false, "Insert AND (·)")}
          {btn("'",  () => insertAt("'"),   '#555', false, "Insert complement (')")}
          {btn('⇒',  () => insertAt(' ⇒ '), '#555', false, "Insert implication (x ⇒ y = x' + y)")}
          {btn('⇔',  () => insertAt(' ⇔ '), '#555', false, "Insert equivalence (x ⇔ y = x·y + x'·y')")}
          {btn('⊕',  () => insertAt(' ⊕ '), '#555', false, "Insert XOR (x ⊕ y = x·y' + x'·y)")}
          {btn('✕',  () => setInput(''),    '#a00', false, "Clear")}
        </div>
        <div style={{ display: 'flex', gap: 4 }}>
          {btn('⚡ Simplify',    handleSimplify,    '#1a6bcc', !ast || loading, !ast ? "Fix syntax errors first" : "Simplify to minimal SOP")}
          {btn("A'  Complement", handleComplement,  '#2a6a6a', !ast,            !ast ? "Fix syntax errors first" : "Show the complement as a nested box diagram")}
        </div>
        <div style={{ display: 'flex', gap: 4 }}>
          {btn('✓ Valid?',       handleValid,       '#6a2a9a', !ast || loading, !ast ? "Fix syntax errors first" : "Check if formula is a tautology")}
          {btn('? Satisfiable?', handleSatisfiable, '#7a4a00', !ast || loading, !ast ? "Fix syntax errors first" : "Check if formula has a satisfying assignment")}
          {btn('ρ  Paths',       handlePaths,       '#4a4a8a', !ast || loading, !ast ? "Fix syntax errors first" : "Show paths through the matrix")}
          <input
            type="number" min={1} value={pathsLimit}
            onChange={e => setPathsLimit(Math.max(1, parseInt(e.target.value) || 1))}
            title="Maximum number of paths to enumerate"
            style={{
              width: 50, padding: '4px 6px', fontSize: 12, border: '1px solid #bbb',
              borderRadius: 4, textAlign: 'center',
            }}
          />
        </div>
      </div>

      {/* Tip */}
      <div style={{ fontSize: 12, color: '#888', marginBottom: 10 }}>
        <code>·</code> or <code>*</code> = AND &nbsp;·&nbsp; <code>+</code> = OR &nbsp;·&nbsp;
        <code>'</code> = complement &nbsp;·&nbsp; <code>⇒</code> = implication &nbsp;·&nbsp;
        <code>⇔</code> or <code>=</code> = equivalence &nbsp;·&nbsp; <code>⊕</code> or <code>≠</code> = XOR
      </div>

      {/* Syntax error box */}
      {error && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 10,
          color: '#8b0000', background: '#fff5f5',
          border: '1.5px solid #f5c2c2',
          padding: '10px 14px', borderRadius: 6,
          fontSize: 13, marginBottom: 12,
        }}>
          <span style={{ fontSize: 16, lineHeight: 1.3 }}>⚠</span>
          <div><b>Syntax error</b><br />{error}</div>
        </div>
      )}

      {/* Simplify result message */}
      {simplifyMsg && (
        <div style={{
          display: 'flex', alignItems: 'center', gap: 8,
          color: simplifyMsg.ok ? '#1a5c1a' : '#8b0000',
          background: simplifyMsg.ok ? '#f0fff0' : '#fff5f5',
          border: `1.5px solid ${simplifyMsg.ok ? '#b2e0b2' : '#f5c2c2'}`,
          padding: '9px 14px', borderRadius: 6,
          fontSize: 13, marginBottom: 12,
          animation: 'fadeIn 0.2s ease',
        }}>
          {simplifyMsg.text}
        </div>
      )}

      {/* Valid result */}
      {validResult && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 8,
          color: validResult.error ? '#8b0000' : validResult.valid ? '#1a5c1a' : '#6a2a9a',
          background: validResult.error ? '#fff5f5' : validResult.valid ? '#f0fff0' : '#f8f0ff',
          border: `1.5px solid ${validResult.error ? '#f5c2c2' : validResult.valid ? '#b2e0b2' : '#d4a0f0'}`,
          padding: '9px 14px', borderRadius: 6, fontSize: 13, marginBottom: 12,
        }}>
          {validResult.error
            ? `✗ ${validResult.error}`
            : validResult.valid
              ? <span>
                  ✓ Valid — all paths are covered
                  {validResult.coveringPairs?.length > 0 && ast && (
                    <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        {new Set(validResult.coveringPairs.map(([a, b]) => a.join(',') + '|' + b.join(','))).size} pairs in the cover:
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set(validResult.coveringPairs.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          // Build variable→cover-indices map (strip primes to get base variable)
                          const varIndices = {};
                          validResult.coveringPairs.forEach(([posA, posB], i) => {
                            const a = resolvePosition(ast, posA)?.n ?? posA.join(',');
                            const base = a.replace(/'$/,'');
                            (varIndices[base] ??= new Set()).add(i);
                          });
                          const vars = Object.keys(varIndices).sort();
                          return <>
                            {' · '}
                            {vars.map((v, j) => {
                              const indices = [...varIndices[v]];
                              const allOn = indices.every(i => validSelected.has(i));
                              return <span key={v}>
                                {j > 0 && ' '}
                                <a href="#" onClick={e => {
                                  e.preventDefault();
                                  setValidSelected(prev => {
                                    const s = new Set(prev);
                                    if (allOn) indices.forEach(i => s.delete(i));
                                    else indices.forEach(i => s.add(i));
                                    return s;
                                  });
                                }} style={{
                                  fontSize: 11, fontFamily: 'Georgia, serif',
                                  color: allOn ? '#333' : '#888',
                                  fontWeight: allOn ? 'bold' : 'normal',
                                }}>{v}</a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      {(() => {
                        // Group pairs by their position key
                        const groups = [];
                        const groupMap = {};
                        validResult.coveringPairs.forEach(([posA, posB], idx) => {
                          const key = posA.join(',') + '|' + posB.join(',');
                          if (!(key in groupMap)) {
                            groupMap[key] = groups.length;
                            groups.push({ posA, posB, indices: [] });
                          }
                          groups[groupMap[key]].indices.push(idx);
                        });
                        return <div style={{
                          ...(groups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                          marginTop: 4,
                        }}>
                          {groups.map((group, gi) => {
                            const a = resolvePosition(ast, group.posA)?.n ?? group.posA.join(',');
                            const b = resolvePosition(ast, group.posB)?.n ?? group.posB.join(',');
                            const allSelected = group.indices.every(i => validSelected.has(i));
                            const prefixes = group.indices.map(idx => {
                              const prefix = validResult.coveredPrefixes?.[idx];
                              return prefix
                                ? '{' + prefix.map(p => resolvePosition(ast, p)?.n ?? p.join(',')).join(', ') + '}'
                                : null;
                            }).filter(Boolean);
                            const expanded = validExpanded.has(gi);
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span
                                onClick={() => setValidSelected(prev => {
                                  const s = new Set(prev);
                                  if (allSelected) group.indices.forEach(i => s.delete(i));
                                  else group.indices.forEach(i => s.add(i));
                                  return s;
                                })}
                                style={{ cursor: 'pointer', opacity: allSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{`{${a}, ${b}}`}</b>
                              </span>
                              {prefixes.length > 0 && <>
                                <span
                                  onClick={e => { e.stopPropagation(); setValidExpanded(prev => {
                                    const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                                  }); }}
                                  style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                  title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                                >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'path' : 'paths'}</span>
                                {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                  {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                                </div>}
                              </>}
                            </div>;
                          })}
                        </div>;
                      })()}
                    </span>
                  )}
                </span>
              : <span>
                  ✗ Not valid — uncovered path: <b style={{ fontFamily: 'Georgia, serif' }}>{validResult.path}</b>
                  {validResult.coveringPairs?.length > 0 && ast && (
                    <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        partial cover: {new Set(validResult.coveringPairs.map(([a, b]) => a.join(',') + '|' + b.join(','))).size} pairs
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set(validResult.coveringPairs.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          const varIndices = {};
                          validResult.coveringPairs.forEach(([posA, posB], i) => {
                            const a = resolvePosition(ast, posA)?.n ?? posA.join(',');
                            const base = a.replace(/'$/,'');
                            (varIndices[base] ??= new Set()).add(i);
                          });
                          const vars = Object.keys(varIndices).sort();
                          return <>
                            {' · '}
                            {vars.map((v, j) => {
                              const indices = [...varIndices[v]];
                              const allOn = indices.every(i => validSelected.has(i));
                              return <span key={v}>
                                {j > 0 && ' '}
                                <a href="#" onClick={e => {
                                  e.preventDefault();
                                  setValidSelected(prev => {
                                    const s = new Set(prev);
                                    if (allOn) indices.forEach(i => s.delete(i));
                                    else indices.forEach(i => s.add(i));
                                    return s;
                                  });
                                }} style={{
                                  fontSize: 11, fontFamily: 'Georgia, serif',
                                  color: allOn ? '#333' : '#888',
                                  fontWeight: allOn ? 'bold' : 'normal',
                                }}>{v}</a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      {(() => {
                        const groups = [];
                        const groupMap = {};
                        validResult.coveringPairs.forEach(([posA, posB], idx) => {
                          const key = posA.join(',') + '|' + posB.join(',');
                          if (!(key in groupMap)) {
                            groupMap[key] = groups.length;
                            groups.push({ posA, posB, indices: [] });
                          }
                          groups[groupMap[key]].indices.push(idx);
                        });
                        return <div style={{
                          ...(groups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                          marginTop: 4,
                        }}>
                          {groups.map((group, gi) => {
                            const a = resolvePosition(ast, group.posA)?.n ?? group.posA.join(',');
                            const b = resolvePosition(ast, group.posB)?.n ?? group.posB.join(',');
                            const allSelected = group.indices.every(i => validSelected.has(i));
                            const prefixes = group.indices.map(idx => {
                              const prefix = validResult.coveredPrefixes?.[idx];
                              return prefix
                                ? '{' + prefix.map(p => resolvePosition(ast, p)?.n ?? p.join(',')).join(', ') + '}'
                                : null;
                            }).filter(Boolean);
                            const expanded = validExpanded.has(gi);
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span
                                onClick={() => setValidSelected(prev => {
                                  const s = new Set(prev);
                                  if (allSelected) group.indices.forEach(i => s.delete(i));
                                  else group.indices.forEach(i => s.add(i));
                                  return s;
                                })}
                                style={{ cursor: 'pointer', opacity: allSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{`{${a}, ${b}}`}</b>
                              </span>
                              {prefixes.length > 0 && <>
                                <span
                                  onClick={e => { e.stopPropagation(); setValidExpanded(prev => {
                                    const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                                  }); }}
                                  style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                  title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                                >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'path' : 'paths'}</span>
                                {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                  {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                                </div>}
                              </>}
                            </div>;
                          })}
                        </div>;
                      })()}
                    </span>
                  )}
                </span>}
        </div>
      )}

      {/* Satisfiable result */}
      {satResult && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 8,
          color: satResult.error ? '#8b0000' : satResult.satisfiable ? '#1a5c1a' : '#7a4a00',
          background: satResult.error ? '#fff5f5' : satResult.satisfiable ? '#f0fff0' : '#fffaf0',
          border: `1.5px solid ${satResult.error ? '#f5c2c2' : satResult.satisfiable ? '#b2e0b2' : '#e0c870'}`,
          padding: '9px 14px', borderRadius: 6, fontSize: 13, marginBottom: 12,
        }}>
          {satResult.error
            ? `✗ ${satResult.error}`
            : satResult.satisfiable
              ? <span>
                  ✓ Satisfiable — uncovered path in complement: <b style={{ fontFamily: 'Georgia, serif' }}>{satResult.path}</b>
                  {satResult.coveringPairs?.length > 0 && complementData?.ast && (
                    <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        partial cover of complement: {new Set(satResult.coveringPairs.map(([a, b]) => a.join(',') + '|' + b.join(','))).size} pairs
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set(satResult.coveringPairs.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          const varIndices = {};
                          satResult.coveringPairs.forEach(([posA, posB], i) => {
                            const a = resolvePosition(complementData.ast, posA)?.n ?? posA.join(',');
                            const base = a.replace(/'$/,'');
                            (varIndices[base] ??= new Set()).add(i);
                          });
                          const vars = Object.keys(varIndices).sort();
                          return <>
                            {' · '}
                            {vars.map((v, j) => {
                              const indices = [...varIndices[v]];
                              const allOn = indices.every(i => satSelected.has(i));
                              return <span key={v}>
                                {j > 0 && ' '}
                                <a href="#" onClick={e => {
                                  e.preventDefault();
                                  setSatSelected(prev => {
                                    const s = new Set(prev);
                                    if (allOn) indices.forEach(i => s.delete(i));
                                    else indices.forEach(i => s.add(i));
                                    return s;
                                  });
                                }} style={{
                                  fontSize: 11, fontFamily: 'Georgia, serif',
                                  color: allOn ? '#333' : '#888',
                                  fontWeight: allOn ? 'bold' : 'normal',
                                }}>{v}</a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      {(() => {
                        const groups = [];
                        const groupMap = {};
                        satResult.coveringPairs.forEach(([posA, posB], idx) => {
                          const key = posA.join(',') + '|' + posB.join(',');
                          if (!(key in groupMap)) {
                            groupMap[key] = groups.length;
                            groups.push({ posA, posB, indices: [] });
                          }
                          groups[groupMap[key]].indices.push(idx);
                        });
                        return <div style={{
                          ...(groups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                          marginTop: 4,
                        }}>
                          {groups.map((group, gi) => {
                            const a = resolvePosition(complementData.ast, group.posA)?.n ?? group.posA.join(',');
                            const b = resolvePosition(complementData.ast, group.posB)?.n ?? group.posB.join(',');
                            const allSelected = group.indices.every(i => satSelected.has(i));
                            const prefixes = group.indices.map(idx => {
                              const prefix = satResult.coveredPrefixes?.[idx];
                              return prefix
                                ? '{' + prefix.map(p => resolvePosition(complementData.ast, p)?.n ?? p.join(',')).join(', ') + '}'
                                : null;
                            }).filter(Boolean);
                            const expanded = satExpanded.has(gi);
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span
                                onClick={() => setSatSelected(prev => {
                                  const s = new Set(prev);
                                  if (allSelected) group.indices.forEach(i => s.delete(i));
                                  else group.indices.forEach(i => s.add(i));
                                  return s;
                                })}
                                style={{ cursor: 'pointer', opacity: allSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{`{${a}, ${b}}`}</b>
                              </span>
                              {prefixes.length > 0 && <>
                                <span
                                  onClick={e => { e.stopPropagation(); setSatExpanded(prev => {
                                    const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                                  }); }}
                                  style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                  title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                                >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'path' : 'paths'}</span>
                                {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                  {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                                </div>}
                              </>}
                            </div>;
                          })}
                        </div>;
                      })()}
                    </span>
                  )}
                </span>
              : <span>
                  ✗ Unsatisfiable — all paths in the complement are covered
                  {satResult.coveringPairs?.length > 0 && complementData?.ast && (
                    <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        {new Set(satResult.coveringPairs.map(([a, b]) => a.join(',') + '|' + b.join(','))).size} pairs in the cover:
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set(satResult.coveringPairs.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          const varIndices = {};
                          satResult.coveringPairs.forEach(([posA, posB], i) => {
                            const a = resolvePosition(complementData.ast, posA)?.n ?? posA.join(',');
                            const base = a.replace(/'$/,'');
                            (varIndices[base] ??= new Set()).add(i);
                          });
                          const vars = Object.keys(varIndices).sort();
                          return <>
                            {' · '}
                            {vars.map((v, j) => {
                              const indices = [...varIndices[v]];
                              const allOn = indices.every(i => satSelected.has(i));
                              return <span key={v}>
                                {j > 0 && ' '}
                                <a href="#" onClick={e => {
                                  e.preventDefault();
                                  setSatSelected(prev => {
                                    const s = new Set(prev);
                                    if (allOn) indices.forEach(i => s.delete(i));
                                    else indices.forEach(i => s.add(i));
                                    return s;
                                  });
                                }} style={{
                                  fontSize: 11, fontFamily: 'Georgia, serif',
                                  color: allOn ? '#333' : '#888',
                                  fontWeight: allOn ? 'bold' : 'normal',
                                }}>{v}</a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      {(() => {
                        const groups = [];
                        const groupMap = {};
                        satResult.coveringPairs.forEach(([posA, posB], idx) => {
                          const key = posA.join(',') + '|' + posB.join(',');
                          if (!(key in groupMap)) {
                            groupMap[key] = groups.length;
                            groups.push({ posA, posB, indices: [] });
                          }
                          groups[groupMap[key]].indices.push(idx);
                        });
                        return <div style={{
                          ...(groups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                          marginTop: 4,
                        }}>
                          {groups.map((group, gi) => {
                            const a = resolvePosition(complementData.ast, group.posA)?.n ?? group.posA.join(',');
                            const b = resolvePosition(complementData.ast, group.posB)?.n ?? group.posB.join(',');
                            const allSelected = group.indices.every(i => satSelected.has(i));
                            const prefixes = group.indices.map(idx => {
                              const prefix = satResult.coveredPrefixes?.[idx];
                              return prefix
                                ? '{' + prefix.map(p => resolvePosition(complementData.ast, p)?.n ?? p.join(',')).join(', ') + '}'
                                : null;
                            }).filter(Boolean);
                            const expanded = satExpanded.has(gi);
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span
                                onClick={() => setSatSelected(prev => {
                                  const s = new Set(prev);
                                  if (allSelected) group.indices.forEach(i => s.delete(i));
                                  else group.indices.forEach(i => s.add(i));
                                  return s;
                                })}
                                style={{ cursor: 'pointer', opacity: allSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{`{${a}, ${b}}`}</b>
                              </span>
                              {prefixes.length > 0 && <>
                                <span
                                  onClick={e => { e.stopPropagation(); setSatExpanded(prev => {
                                    const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                                  }); }}
                                  style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                  title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                                >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'path' : 'paths'}</span>
                                {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                  {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                                </div>}
                              </>}
                            </div>;
                          })}
                        </div>;
                      })()}
                    </span>
                  )}
                </span>}
        </div>
      )}

      {/* Paths through the matrix */}
      {pathsResult && (
        <div style={{ padding: '14px 18px', borderRadius: 8,
                      border: '1px solid #c8c8e8', background: '#f7f7fd', marginBottom: 12 }}>
          <div style={{ fontWeight: 'bold', marginBottom: 8, color: '#333' }}>
            Paths through the matrix
            {!pathsResult.error && (
              <span style={{ fontWeight: 'normal', color: '#666', marginLeft: 8 }}>
                ({pathsResult.coveredPaths.length + pathsResult.uncoveredPaths.length} shown —{' '}
                {pathsResult.coveredPaths.length} covered,{' '}
                {pathsResult.uncoveredPaths.length} uncovered)
              </span>
            )}
          </div>
          {pathsResult.error ? (
            <div style={{ color: '#c00' }}>{pathsResult.error}</div>
          ) : (
            <div style={{ display: 'flex', gap: 12 }}>
              <div style={{ flex: 1, minWidth: 0 }}>
                <div style={{ fontSize: 12, color: '#1b5e20', fontWeight: 600, marginBottom: 4 }}>
                  ✓ Covered ({pathsResult.coveredPaths.length})
                </div>
                <div style={{ maxHeight: 200, overflowY: 'auto', display: 'flex', flexWrap: 'wrap', gap: 4, alignContent: 'flex-start' }}>
                  {pathsResult.coveredPaths.map((path, i) => (
                    <span key={`c${i}`} style={{
                      fontFamily: 'Georgia, serif', fontSize: 13,
                      padding: '2px 8px', borderRadius: 4,
                      background: '#e8f5e9', border: '1px solid #81c784', color: '#1b5e20',
                    }}>
                      {path}
                    </span>
                  ))}
                </div>
              </div>
              <div style={{ flex: 1, minWidth: 0 }}>
                <div style={{ fontSize: 12, color: '#7a3a00', fontWeight: 600, marginBottom: 4 }}>
                  ✗ Uncovered ({pathsResult.uncoveredPaths.length})
                </div>
                <div style={{ maxHeight: 200, overflowY: 'auto', display: 'flex', flexWrap: 'wrap', gap: 4, alignContent: 'flex-start' }}>
                  {pathsResult.uncoveredPaths.map((path, i) => (
                    <span key={`u${i}`} style={{
                      fontFamily: 'Georgia, serif', fontSize: 13,
                      padding: '2px 8px', borderRadius: 4,
                      background: '#fff3e0', border: '1px solid #ffb74d', color: '#7a3a00',
                    }}>
                      {path}
                    </span>
                  ))}
                </div>
              </div>
            </div>
          )}
        </div>
      )}

      {/* Diagrams */}
      {ast && (
        <>
          <div style={{ fontSize: 12, color: '#888', marginBottom: 10 }}>
            {simplified ? 'Original' : 'Diagram'}{error ? ' (last valid formula)' : ''} — border colors show nesting depth:
          </div>
          <ZoomPanWrapper key={input} bg='#f8f9fc' border='1px solid #dde' opacity={error ? 0.5 : 1}>
            <DiagramWithConnections
              node={ast}
              coveringPairs={validResult?.coveringPairs ?? null}
              coveredPrefixes={validResult?.coveredPrefixes ?? null}
              selectedIndices={validSelected}
            />
          </ZoomPanWrapper>

          {simplified && (
            <>
              <div style={{ fontSize: 12, color: '#888', marginTop: 20, marginBottom: 10 }}>
                Simplified — <span style={{ fontFamily: 'Georgia, serif' }}>{simplified.formula}</span>
              </div>
              <ZoomPanWrapper key={simplified.formula} bg='#f0fff4' border='1px solid #b2e0b2'>
                <DiagramWithConnections node={simplified.ast} coveringPairs={null} coveredPrefixes={null} selectedIndices={new Set()} />
              </ZoomPanWrapper>
              <div style={{ display: 'flex', justifyContent: 'center', marginTop: 10 }}>
                {btn('Use simplified formula', () => setInput(simplified.formula), '#2a7a2a')}
              </div>
            </>
          )}

          {complementData && (
            <>
              <div style={{ fontSize: 12, color: '#888', marginTop: 20, marginBottom: 10 }}>
                Complement — <span style={{ fontFamily: 'Georgia, serif' }}>{complementData.formula}</span>
              </div>
              <ZoomPanWrapper key={complementData.formula} bg='#f0fafa' border='1px solid #a0d4d4'>
                <DiagramWithConnections
                  node={complementData.ast}
                  coveringPairs={satResult?.coveringPairs ?? null}
                  coveredPrefixes={satResult?.coveredPrefixes ?? null}
                  selectedIndices={satSelected}
                />
              </ZoomPanWrapper>
              <div style={{ display: 'flex', justifyContent: 'center', marginTop: 10 }}>
                {btn('Use complement as formula', () => setInput(complementData.formula), '#2a6a6a')}
              </div>
            </>
          )}
        </>
      )}

      <style>{`@keyframes fadeIn { from { opacity: 0; transform: translateY(-4px); } to { opacity: 1; transform: translateY(0); } }`}</style>
    </div>
  );
}
