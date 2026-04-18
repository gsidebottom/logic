import { useState, useEffect, useLayoutEffect, useRef, createContext, useContext, useMemo } from "react";
import { parse, complementAst, astToString, resolvePosition, VarLabel } from "./formula.jsx";

// ─── Cover context (for highlighting complementary pairs in diagrams) ──────────
const CoverContext = createContext(null);

const PAIR_COLORS = ['#e63946', '#1d7cc4', '#2a9d8f', '#e07c00', '#8e44ad', '#555'];

// Format a number with metric suffixes for large values (>= 1M), up to 6 sig figs.
function fmtNum(n) {
  if (n == null) return '0';
  const abs = Math.abs(n);
  if (abs < 1e6) return n.toLocaleString();
  const suffixes = [
    [1e30, 'Q'],  // quetta
    [1e27, 'R'],  // ronna
    [1e24, 'Y'],  // yotta
    [1e21, 'Z'],  // zetta
    [1e18, 'E'],  // exa
    [1e15, 'P'],  // peta
    [1e12, 'T'],  // tera
    [1e9,  'G'],  // giga
    [1e6,  'M'],  // mega
  ];
  for (const [threshold, suffix] of suffixes) {
    if (abs >= threshold) {
      const scaled = n / threshold;
      // Up to 6 significant figures
      const s = Number(scaled.toPrecision(6));
      // Remove trailing zeros after decimal
      return s.toLocaleString() + suffix;
    }
  }
  return n.toLocaleString();
}

// Format seconds as DDdHHhMMmSSs, omitting leading zero components.
function fmtTime(secs) {
  if (secs == null || secs <= 0) return '';
  const d = Math.floor(secs / 86400);
  const h = Math.floor((secs % 86400) / 3600);
  const m = Math.floor((secs % 3600) / 60);
  const s = Math.floor(secs % 60);
  const frac = secs % 1;
  let parts = [];
  if (d > 0) parts.push(`${d}d`);
  if (d > 0 || h > 0) parts.push(`${parts.length ? String(h).padStart(2, '0') : h}h`);
  if (d > 0 || h > 0 || m > 0) parts.push(`${parts.length ? String(m).padStart(2, '0') : m}m`);
  if (parts.length) {
    parts.push(`${String(s).padStart(2, '0')}s`);
  } else if (secs >= 1) {
    parts.push(`${s}s`);
  } else {
    return `${(secs * 1000).toFixed(0)}ms`;
  }
  return parts.join('');
}

// Format a cadical learned clause: translate 1-based literal numbers to variable names.
function fmtClause(clause, vars) {
  return clause.map(lit => {
    const idx = Math.abs(lit) - 1;
    const neg = lit < 0;
    const name = idx < vars.length ? vars[idx] : `t${idx + 1}`;
    return neg ? name + "'" : name;
  }).join(' + ');
}

// Complement a literal name: a → a', a' → a
const compName = n => n?.endsWith("'") ? n.slice(0, -1) : (n ? n + "'" : n);

// Evaluate an AST against a variable assignment { varName: '0'|'1' }.
// Returns a Map<positionKey, 'true'|'false'|'undetermined'> for every node.
function evaluateAst(node, assignment, position = []) {
  const result = new Map();
  const posKey = position.join(',');

  if (node.t === 'VAR') {
    const neg = node.n.endsWith("'");
    const base = neg ? node.n.slice(0, -1) : node.n;
    if (base === '1') {
      // Constant 1: true; 1': false
      result.set(posKey, neg ? 'false' : 'true');
    } else if (base === '0') {
      // Constant 0: false; 0': true
      result.set(posKey, neg ? 'true' : 'false');
    } else if (!(base in assignment)) {
      result.set(posKey, 'undetermined');
    } else {
      const varTrue = assignment[base] === '1';
      result.set(posKey, (varTrue !== neg) ? 'true' : 'false');
    }
  } else if (node.t === 'OR') {
    let hasTrue = false, hasUndetermined = false;
    node.c.forEach((child, i) => {
      const childResult = evaluateAst(child, assignment, [...position, i]);
      childResult.forEach((v, k) => result.set(k, v));
      const cv = childResult.get([...position, i].join(','));
      if (cv === 'true') hasTrue = true;
      else if (cv === 'undetermined') hasUndetermined = true;
    });
    result.set(posKey, hasTrue ? 'true' : hasUndetermined ? 'undetermined' : 'false');
  } else if (node.t === 'AND') {
    let hasFalse = false, hasUndetermined = false;
    node.c.forEach((child, i) => {
      const childResult = evaluateAst(child, assignment, [...position, i]);
      childResult.forEach((v, k) => result.set(k, v));
      const cv = childResult.get([...position, i].join(','));
      if (cv === 'false') hasFalse = true;
      else if (cv === 'undetermined') hasUndetermined = true;
    });
    result.set(posKey, hasFalse ? 'false' : hasUndetermined ? 'undetermined' : 'true');
  }
  return result;
}

const EVAL_COLORS = { 'true': '#d4edda', 'false': '#f8d7da', 'undetermined': '#d6eaf8' };

// Extract all unique base variable names from an AST, sorted alphabetically.
function extractVars(node) {
  const vars = new Set();
  const walk = n => {
    if (!n) return;
    if (n.t === 'VAR') {
      const name = n.n;
      const base = name.endsWith("'") ? name.slice(0, -1) : name;
      vars.add(base);
    } else if (n.c) {
      n.c.forEach(walk);
    }
  };
  walk(node);
  return [...vars].sort();
}

// ─── Box Renderer ─────────────────────────────────────────────────────────────
const PAD = 10, GAP = 8;
const BORDER_COLORS = ['#111', '#1a6bcc', '#b35000', '#2a7a2a', '#7a1a7a'];

function BoxNode({ node, depth = 0, position = [], complementView = false }) {
  const cover = useContext(CoverContext);
  const compView = cover?.complementView ?? complementView;
  if (!node) return null;

  if (node.t === 'VAR') {
    // In complement view, swap the displayed literal name
    const displayName = compView
      ? (node.n.endsWith("'") ? node.n.slice(0, -1) : node.n + "'")
      : node.n;
    const posKey = position.join(',');
    const pairIndices = cover?.posToPairIndices?.[posKey] ?? [];
    const prefixIndices = (cover?.posToPrefixIndices?.[posKey] ?? [])
      .filter(i => !pairIndices.includes(i)); // don't double-show
    const highlightIndices = cover?.posToHighlightIndices?.[posKey] ?? [];
    const allIndices = [...pairIndices, ...prefixIndices];
    const hasPair = pairIndices.length > 0;
    const hasPrefix = prefixIndices.length > 0;
    const hasHighlight = highlightIndices.length > 0;

    const highlighted = allIndices.length > 0 || hasHighlight;

    // Sort all indices by original cover index for consistent stacking
    const pairSet = new Set(pairIndices);
    const sorted = allIndices.length > 0 ? [...allIndices].sort((a, b) => a - b) : [];

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
      const dashGrad = `repeating-linear-gradient(${compView ? '180deg' : '90deg'}, ${color} 0px, ${color} ${barHeight + 1}px, transparent ${barHeight + 1}px, transparent ${2 * (barHeight + 1)}px)`;
      return (
        <div key={`bar-${idx}`} style={{
          position: 'absolute',
          ...(compView ? {
            top: colCount > 1 ? `${(col / colCount) * 100}%` : -1,
            bottom: colCount > 1 ? `${((colCount - col - 1) / colCount) * 100}%` : -1,
            right: -(2 + row * barStep),
            width: barHeight,
          } : {
            left: colCount > 1 ? `${(col / colCount) * 100}%` : -1,
            right: colCount > 1 ? `${((colCount - col - 1) / colCount) * 100}%` : -1,
            bottom: -(2 + row * barStep),
            height: barHeight,
          }),
          background: dashed ? undefined : color,
          backgroundImage: dashed ? dashGrad : undefined,
          borderRadius: 1,
          pointerEvents: 'none',
        }} />
      );
    });

    // Uncovered path highlight bars (dashed, red tones)
    const UNCOV_COLORS = ['#d32f2f', '#f57c00', '#7b1fa2', '#00838f', '#c2185b', '#4e342e'];
    const uncovBars = highlightIndices.map((hi, r) => {
      const color = UNCOV_COLORS[hi % UNCOV_COLORS.length];
      const col = Math.floor((sorted.length + r) / barsPerCol);
      const row = (sorted.length + r) % barsPerCol;
      const dashGrad = `repeating-linear-gradient(${compView ? '180deg' : '90deg'}, ${color} 0px, ${color} ${barHeight + 1}px, transparent ${barHeight + 1}px, transparent ${2 * (barHeight + 1)}px)`;
      return (
        <div key={`hl-${hi}`} style={{
          position: 'absolute',
          ...(compView ? {
            top: colCount > 1 ? `${(col / colCount) * 100}%` : -1,
            bottom: colCount > 1 ? `${((colCount - col - 1) / colCount) * 100}%` : -1,
            right: -(2 + row * barStep),
            width: barHeight,
          } : {
            left: colCount > 1 ? `${(col / colCount) * 100}%` : -1,
            right: colCount > 1 ? `${((colCount - col - 1) / colCount) * 100}%` : -1,
            bottom: -(2 + row * barStep),
            height: barHeight,
          }),
          backgroundImage: dashGrad,
          borderRadius: 1,
          pointerEvents: 'none',
        }} />
      );
    });

    // Background tint
    const evalResult = cover?.assignmentEval?.get(posKey);
    const evalBg = evalResult ? EVAL_COLORS[evalResult] : undefined;
    const firstColor = sorted.length > 0
      ? (cover?.idxToGroupColor?.[sorted[0]] ?? PAIR_COLORS[sorted[0] % PAIR_COLORS.length])
      : hasHighlight ? UNCOV_COLORS[highlightIndices[0] % UNCOV_COLORS.length] : null;
    const bgColor = evalBg ?? (highlighted && firstColor
      ? (hasPair ? firstColor + '20' : firstColor + '12')
      : undefined);

    return (
      <div
        data-position={posKey}
        style={{
          position: 'relative',
          minWidth: compView ? undefined : 26,
          minHeight: compView ? 26 : undefined,
          display: 'flex', alignItems: 'center',
          justifyContent: 'center',
          padding: compView ? '6px 4px' : '4px 6px',
          fontSize: 17, fontFamily: 'Georgia, serif',
          fontWeight: 'bold', lineHeight: 1, userSelect: 'none',
          ...(bgColor ? { background: bgColor, borderRadius: 3 } : {}),
        }}
      >
        {bars}
        {uncovBars}
        <span style={{
          display: 'inline-block',
          transform: compView ? 'rotate(-90deg)' : 'rotate(0deg)',
          transition: 'transform 0.4s ease',
        }}>
          <VarLabel name={displayName} />
        </span>
      </div>
    );
  }

  const isOR  = node.t === 'OR';
  const color = BORDER_COLORS[depth % BORDER_COLORS.length];
  const posKey = position.join(',');
  const evalResult = cover?.assignmentEval?.get(posKey);
  const evalBg = evalResult ? EVAL_COLORS[evalResult] : undefined;

  return (
    <div style={{
      border: `2px solid ${color}`, borderRadius: 3, padding: PAD,
      display: 'inline-flex',
      flexDirection: isOR ? 'row' : 'column',
      alignItems: 'center', justifyContent: 'center',
      gap: GAP, boxSizing: 'border-box',
      overflow: 'visible',
      ...(evalBg ? { background: evalBg } : {}),
    }}>
      {(compView && !isOR ? [...node.c].reverse().map((child, ri) => {
        const i = node.c.length - 1 - ri;
        return <BoxNode key={i} node={child} depth={depth + 1} position={[...position, i]} complementView={compView} />;
      }) : node.c.map((child, i) => <BoxNode key={i} node={child} depth={depth + 1} position={[...position, i]} complementView={compView} />))}
    </div>
  );
}

// ─── Diagram with SVG arc connections for covering pairs ──────────────────────
function DiagramWithConnections({ node, coverGroups, selectedGroups, highlightedPaths, assignmentEval = null, complementView = false }) {
  const containerRef = useRef(null);
  const [arcs, setArcs] = useState([]);
  const [pathLines, setPathLines] = useState([]);

  // Each group is already a unique pair — no dedup needed.
  const groups = coverGroups ?? [];
  const selected = selectedGroups;

  const posToPairIndices = useMemo(() => {
    const m = {};
    groups.forEach((g, i) => {
      if (!selected.has(i)) return;
      const ka = g.pair[0].join(','), kb = g.pair[1].join(',');
      (m[ka] ??= []).push(i);
      (m[kb] ??= []).push(i);
    });
    return m;
  }, [groups, selected]);

  const posToPrefixIndices = useMemo(() => {
    const m = {};
    groups.forEach((g, gi) => {
      if (!selected.has(gi) || !g.prefixes?.length) return;
      g.prefixes.forEach(positions => {
        positions.forEach(pos => {
          const key = pos.join(',');
          (m[key] ??= []).push(gi);
        });
      });
    });
    return m;
  }, [groups, selected]);

  const idxToGroupColor = useMemo(() => {
    const m = {};
    groups.forEach((_, i) => { m[i] = PAIR_COLORS[i % PAIR_COLORS.length]; });
    return m;
  }, [groups]);

  // Build set of positions highlighted by uncovered paths
  const posToHighlightIndices = useMemo(() => {
    const m = {};
    if (highlightedPaths) {
      highlightedPaths.forEach((positions, i) => {
        positions.forEach(pos => {
          const key = pos.join(',');
          (m[key] ??= []).push(i);
        });
      });
    }
    return m;
  }, [highlightedPaths]);

  // Compute max bar count across all positions for consistent scaling
  const maxBarCount = useMemo(() => {
    const counts = {};
    for (const [key, indices] of Object.entries(posToPairIndices)) {
      counts[key] = (counts[key] ?? 0) + indices.length;
    }
    for (const [key, indices] of Object.entries(posToPrefixIndices)) {
      const pairSet = new Set(posToPairIndices[key] ?? []);
      counts[key] = (counts[key] ?? 0) + indices.filter(i => !pairSet.has(i)).length;
    }
    for (const [key, indices] of Object.entries(posToHighlightIndices)) {
      counts[key] = (counts[key] ?? 0) + indices.length;
    }
    return Math.max(0, ...Object.values(counts));
  }, [posToPairIndices, posToPrefixIndices, posToHighlightIndices]);

  // Recompute arc positions and path lines after every render (DOM may have changed)
  useLayoutEffect(() => {
    if (!containerRef.current) return;
    if (!groups.length && !highlightedPaths?.length) {
      setArcs(prev => prev.length === 0 ? prev : []);
      setPathLines(prev => prev.length === 0 ? prev : []);
      return;
    }
    const container = containerRef.current;
    const boundsOf = el => {
      let x = 0, y = 0, cur = el;
      while (cur && cur !== container) { x += cur.offsetLeft; y += cur.offsetTop; cur = cur.offsetParent; }
      return { x, y, w: el.offsetWidth, h: el.offsetHeight };
    };

    const newArcs = [];
    groups.forEach((g, gi) => {
      if (!selected.has(gi)) return;
      const da = container.querySelector(`[data-position="${g.pair[0].join(',')}"]`);
      const db = container.querySelector(`[data-position="${g.pair[1].join(',')}"]`);
      if (!da || !db) return;
      const ba = boundsOf(da), bb = boundsOf(db);
      newArcs.push({
        x1: ba.x + ba.w / 2, y1: ba.y + ba.h / 2,
        x2: bb.x + bb.w / 2, y2: bb.y + bb.h / 2,
        pairIdx: gi,
      });
    });

    // Compute bar layout params (must match BoxNode logic)
    const barsPerCol = 8;
    const globalMax = maxBarCount;
    const effectiveMax = Math.min(globalMax, barsPerCol);
    const maxStack = 16;
    const barStep = effectiveMax <= 4 ? 4 : Math.max(1, maxStack / effectiveMax);

    const barOffset = (posKey, coverIdx, isHighlight) => {
      const pairs = posToPairIndices[posKey] ?? [];
      const prefixes = (posToPrefixIndices[posKey] ?? []).filter(i => !pairs.includes(i));
      const sorted = [...pairs, ...prefixes].sort((a, b) => a - b);
      const highlights = posToHighlightIndices[posKey] ?? [];
      let ringIdx;
      if (isHighlight) {
        ringIdx = sorted.length + highlights.indexOf(coverIdx);
      } else {
        ringIdx = sorted.indexOf(coverIdx);
        if (ringIdx === -1) ringIdx = 0;
      }
      const row = ringIdx % barsPerCol;
      return 2 + row * barStep - barStep / 2;
    };

    const lineEndpoints = (ba, bb, offA, offB) => {
      if (complementView) {
        return {
          x1: ba.x + ba.w + offA, y1: ba.y,
          x2: bb.x + bb.w + offB, y2: bb.y + bb.h,
        };
      }
      return {
        x1: ba.x + ba.w, y1: ba.y + ba.h + offA,
        x2: bb.x,        y2: bb.y + bb.h + offB,
      };
    };

    // Path connection lines: connect consecutive positions via their specific bars
    const newPathLines = [];
    groups.forEach((g, gi) => {
      if (!selected.has(gi) || !g.prefixes?.length) return;
      const color = idxToGroupColor[gi] ?? PAIR_COLORS[gi % PAIR_COLORS.length];
      g.prefixes.forEach(positions => {
        for (let k = 0; k < positions.length - 1; k++) {
          const keyA = positions[k].join(','), keyB = positions[k + 1].join(',');
          const da = container.querySelector(`[data-position="${keyA}"]`);
          const db = container.querySelector(`[data-position="${keyB}"]`);
          if (!da || !db) continue;
          const ba = boundsOf(da), bb = boundsOf(db);
          const offA = barOffset(keyA, gi, false);
          const offB = barOffset(keyB, gi, false);
          newPathLines.push({ ...lineEndpoints(ba, bb, offA, offB), color });
        }
      });
    });
    // Highlighted uncovered path lines
    if (highlightedPaths) {
      const UNCOV_COLORS = ['#d32f2f', '#f57c00', '#7b1fa2', '#00838f', '#c2185b', '#4e342e'];
      highlightedPaths.forEach((positions, hi) => {
        const color = UNCOV_COLORS[hi % UNCOV_COLORS.length];
        for (let k = 0; k < positions.length - 1; k++) {
          const keyA = positions[k].join(','), keyB = positions[k + 1].join(',');
          const da = container.querySelector(`[data-position="${keyA}"]`);
          const db = container.querySelector(`[data-position="${keyB}"]`);
          if (!da || !db) continue;
          const ba = boundsOf(da), bb = boundsOf(db);
          const offA = barOffset(keyA, hi, true);
          const offB = barOffset(keyB, hi, true);
          newPathLines.push({ ...lineEndpoints(ba, bb, offA, offB), color });
        }
      });
    }

    setArcs(prev => JSON.stringify(prev) === JSON.stringify(newArcs) ? prev : newArcs);
    setPathLines(prev => JSON.stringify(prev) === JSON.stringify(newPathLines) ? prev : newPathLines);
  });

  return (
    <CoverContext.Provider value={(Object.keys(posToPairIndices).length || Object.keys(posToPrefixIndices).length || Object.keys(posToHighlightIndices).length || assignmentEval || complementView) ? { posToPairIndices, posToPrefixIndices, posToHighlightIndices, maxBarCount, idxToGroupColor, assignmentEval, complementView } : null}>
      <div ref={containerRef} style={{
        position: 'relative', display: 'inline-block',
        transform: complementView ? 'rotate(90deg)' : 'rotate(0deg)',
        transition: 'transform 0.4s ease',
      }}>
        <BoxNode node={node} depth={0} complementView={complementView} />
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
              const my = (arc.y1 + arc.y2) / 2;
              const dx = arc.x2 - arc.x1, dy = arc.y2 - arc.y1;
              const dist = Math.sqrt(dx * dx + dy * dy) || 1;
              const voff = Math.max(28, dist * 0.4);
              const qcx = complementView ? Math.min(arc.x1, arc.x2) - voff : mx;
              const qcy = complementView ? my : Math.min(arc.y1, arc.y2) - voff;
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
function ZoomPanWrapper({ children, bg = '#f8f9fc', border = '1px solid #dde', opacity = 1, rotated = false }) {
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
    const rawW = content.offsetWidth, rawH = content.offsetHeight;
    // When rotated 90°, effective width and height swap
    const cw = rotated ? rawH : rawW;
    const ch = rotated ? rawW : rawH;
    if (!cw || !ch) return;
    const s  = Math.min(vw / cw, vh / ch, 1);
    // Center the visual content: place (rawW/2, rawH/2) at viewport center
    const tx = vw / 2 - (rawW / 2) * s;
    const ty = vh / 2 - (rawH / 2) * s;
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
                  opacity, transition: 'opacity 0.15s, background 0.4s ease, border-color 0.4s ease' }}>
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
  const [helpOpen,       setHelpOpen]       = useState(false);
  const [addingLabel,    setAddingLabel]    = useState('');   // '' = not adding
  const [saveMsg,        setSaveMsg]        = useState('');
  const [input,          setInput]          = useState(EXAMPLES[0].f);
  const [simplified,     setSimplified]     = useState(null); // {formula, ast}
  const [simplifyMsg,    setSimplifyMsg]    = useState(null); // {text, ok}
  const [simplifyForm,   setSimplifyForm]   = useState('DNF'); // 'DNF' or 'CNF'
  const [complementData, setComplementData] = useState(null); // truthy = show complement view
  const [validResult,    setValidResult]    = useState(null); // {valid, path}
  const [validSelected,  setValidSelected]  = useState(new Set()); // Set<number> of selected pair indices
  const [validExpanded,  setValidExpanded]  = useState(new Set()); // Set<number> of expanded group indices
  const [validUncovOn,   setValidUncovOn]   = useState(false);     // toggle uncovered path highlight
  const [validPathExpanded, setValidPathExpanded] = useState(false); // show full uncovered path
  const [validVarsExpanded, setValidVarsExpanded] = useState(false); // show full sorted unique literals
  const [validAsgnFmt,      setValidAsgnFmt]      = useState(0);     // 0=expanded, 1=factored, 2=value string
  const [validAsgnOn,       setValidAsgnOn]       = useState(false); // highlight assignment in diagram
  const [satResult,      setSatResult]      = useState(null); // {satisfiable, path, coverGroups}
  const [satSelected,    setSatSelected]    = useState(new Set()); // Set<number> of selected pair indices
  const [satExpanded,    setSatExpanded]    = useState(new Set()); // Set<number> of expanded group indices
  const [satUncovOn,     setSatUncovOn]     = useState(false);     // toggle uncovered path highlight
  const [validRunning,   setValidRunning]   = useState(false);
  const validPollRef = useRef(null);
  const [satRunning,     setSatRunning]     = useState(false);
  const satPollRef = useRef(null);
  const [satPathExpanded, setSatPathExpanded] = useState(false);   // show full uncovered path
  const [satVarsExpanded, setSatVarsExpanded] = useState(false);   // show full sorted unique literals
  const [satAsgnFmt,      setSatAsgnFmt]      = useState(0);     // 0=expanded, 1=factored, 2=value string
  const [satAsgnOn,       setSatAsgnOn]       = useState(false);   // highlight assignment in diagram
  // ── CaDiCaL SAT solver state ──────────────────────────────────────────────
  const [cadicalEnabled,        setCadicalEnabled]        = useState(false);
  const [cadicalValidResult,    setCadicalValidResult]    = useState(null); // {assignment, learnedClauses, elapsedSecs, error}
  const [cadicalSatResult,      setCadicalSatResult]      = useState(null);
  const [cadicalValidRunning,   setCadicalValidRunning]   = useState(false);
  const [cadicalSatRunning,     setCadicalSatRunning]     = useState(false);
  const cadicalValidPollRef = useRef(null);
  const cadicalSatPollRef   = useRef(null);
  const [cadicalValidAsgnOn,    setCadicalValidAsgnOn]    = useState(false); // highlight cadical assignment in diagram
  const [cadicalSatAsgnOn,      setCadicalSatAsgnOn]      = useState(false);
  const [cadicalValidAsgnFmt,   setCadicalValidAsgnFmt]   = useState(0);    // 0=expanded, 1=factored, 2=value string
  const [cadicalSatAsgnFmt,     setCadicalSatAsgnFmt]     = useState(0);
  const [cadicalValidVarsExpanded, setCadicalValidVarsExpanded] = useState(false);
  const [cadicalSatVarsExpanded,   setCadicalSatVarsExpanded]   = useState(false);
  const [cadicalValidClausesExpanded, setCadicalValidClausesExpanded] = useState(false);
  const [cadicalSatClausesExpanded,   setCadicalSatClausesExpanded]   = useState(false);
  const [pathsResult,    setPathsResult]    = useState(null); // {uncoveredPaths, coverGroups, totalPrefixCount} | {error}
  const [pathsLimit,     setPathsLimit]     = useState(100);
  const [pathsComp,      setPathsComp]      = useState(false); // show paths of complement
  const [pathsSelected,  setPathsSelected]  = useState(new Set());
  const [pathsExpanded,  setPathsExpanded]  = useState(new Set());
  const [pathsUncovSel,  setPathsUncovSel]  = useState(new Set()); // selected uncovered path indices
  const [pathsRunning,   setPathsRunning]   = useState(false); // server-side path generation in progress
  const [pathsTreeExpanded, setPathsTreeExpanded] = useState(new Set()); // Set<nodeKey> of expanded prefix-tree nodes
  const pathsPollRef = useRef(null);
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
    stopValidPolling();
    if (validRunning) { fetch('http://localhost:3001/valid/cancel', { method: 'POST' }).catch(()=>{}); }
    setValidResult(null);
    setValidRunning(false);
    setValidSelected(new Set());
    setValidExpanded(new Set());
    setValidUncovOn(false);
    setValidPathExpanded(false);
    setValidVarsExpanded(false);
    setValidAsgnOn(false);
    stopSatPolling();
    if (satRunning) { fetch('http://localhost:3001/satisfiable/cancel', { method: 'POST' }).catch(()=>{}); }
    setSatResult(null);
    setSatRunning(false);
    setSatSelected(new Set());
    setSatExpanded(new Set());
    setSatUncovOn(false);
    setSatPathExpanded(false);
    setSatVarsExpanded(false);
    setSatAsgnOn(false);
    // CaDiCaL reset
    stopCadicalValidPolling();
    if (cadicalValidRunning) { fetch('http://localhost:3001/cadical/valid/cancel', { method: 'POST' }).catch(()=>{}); }
    setCadicalValidResult(null);
    setCadicalValidRunning(false);
    setCadicalValidAsgnOn(false);
    stopCadicalSatPolling();
    if (cadicalSatRunning) { fetch('http://localhost:3001/cadical/sat/cancel', { method: 'POST' }).catch(()=>{}); }
    setCadicalSatResult(null);
    setCadicalSatRunning(false);
    setCadicalSatAsgnOn(false);
    stopPathsPolling();
    if (pathsRunning) { fetch('http://localhost:3001/paths/cancel', { method: 'POST' }).catch(()=>{}); }
    setPathsResult(null);
    setPathsRunning(false);
    setPathsSelected(new Set());
    setPathsExpanded(new Set());
    setPathsUncovSel(new Set());
    setPathsTreeExpanded(new Set());
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
    const form = simplifyForm;
    try {
      const res = await fetch('http://localhost:3001/simplify', {
        method: 'POST',
        headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input, cnf: form === 'CNF' }),
      });
      const data = await res.json();
      if (data.error) {
        setSimplifyMsg({ text: `✗ ${data.error}`, ok: false });
      } else {
        const result = data.result;
        const inputNorm = input.replace(/\s+/g, '');
        const resultNorm = result.replace(/\s+/g, '');
        if (inputNorm === resultNorm) {
          setSimplifyMsg({ text: `✓ Already in minimal ${form}`, ok: true });
          setSimplified(null);
        } else {
          setSimplifyMsg({ text: `✓ Simplified ${form}!`, ok: true });
          setSimplified({ formula: result, ast: parse(result) });
          setInput(result);
        }
      }
    } catch (e) {
      setSimplifyMsg({ text: '✗ Could not reach Rust service — is it running? (cargo run)', ok: false });
    }
    setLoading(false);
    setTimeout(() => setSimplifyMsg(null), 3500);
  };

  const stopPathsPolling = () => {
    if (pathsPollRef.current) {
      clearInterval(pathsPollRef.current);
      pathsPollRef.current = null;
    }
  };

  const applyPathsStatus = (data, complementFlag) => {
    if (data.error) {
      setPathsResult({ error: data.error });
      setPathsRunning(false);
      stopPathsPolling();
      return;
    }
    setPathsResult({
      uncoveredPaths: data.uncovered_paths,
      uncoveredPositions: data.uncovered_path_positions,
      coverGroups: data.cover_groups,
      totalPrefixCount: data.total_prefix_count,
      classifiedCount: data.classified_count,
      elapsedSecs: data.elapsed_secs,
      totalPathCount: data.total_path_count,
      hitLimit: data.hit_limit,
      isComplement: complementFlag,
    });
    setPathsRunning(!!data.running);
    if (!data.running) stopPathsPolling();
  };

  const pollPathsOnce = async (complementFlag) => {
    try {
      const res = await fetch('http://localhost:3001/paths');
      const data = await res.json();
      applyPathsStatus(data, complementFlag);
    } catch (e) {
      setPathsResult({ error: 'Could not reach Rust service' });
      setPathsRunning(false);
      stopPathsPolling();
    }
  };

  const fetchPaths = async () => {
    stopPathsPolling();
    setPathsRunning(true);
    setPathsResult({
      uncoveredPaths: [], uncoveredPositions: [],
      coverGroups: [], totalPrefixCount: 0,
      hitLimit: false, isComplement: pathsComp,
    });
    setComplementData(pathsComp);
    const complementFlag = pathsComp;
    try {
      const res = await fetch('http://localhost:3001/paths', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input, paths_class_limit: pathsLimit, complement: complementFlag }),
      });
      if (!res.ok) throw new Error('start failed');
    } catch (e) {
      setPathsResult({ error: 'Could not reach Rust service' });
      setPathsRunning(false);
      return;
    }
    // Poll every 5s. Fetch once immediately so something shows up faster than 5s if quick.
    pollPathsOnce(complementFlag);
    pathsPollRef.current = setInterval(() => pollPathsOnce(complementFlag), 500);
  };

  const cancelPaths = async () => {
    stopPathsPolling();
    try {
      await fetch('http://localhost:3001/paths/cancel', { method: 'POST' });
    } catch (e) { /* ignore */ }
    // Final fetch to grab whatever the worker accumulated before cancellation.
    try {
      const res = await fetch('http://localhost:3001/paths');
      const data = await res.json();
      applyPathsStatus(data, pathsResult?.isComplement ?? false);
    } catch (e) { /* ignore */ }
    setPathsRunning(false);
  };

  // ── Valid polling ──────────────────────────────────────────────────────────
  const stopValidPolling = () => {
    if (validPollRef.current) {
      clearInterval(validPollRef.current);
      validPollRef.current = null;
    }
  };

  const applyValidStatus = (data) => {
    if (data.error) {
      setValidResult({ error: data.error });
      setValidRunning(false);
      stopValidPolling();
      return;
    }
    setValidResult({
      valid: !data.running ? (data.uncovered_paths.length === 0) : null,
      path: data.uncovered_paths[0] || null,
      uncoveredPositions: data.uncovered_path_positions[0] || null,
      coverGroups: data.cover_groups,
      totalPrefixCount: data.total_prefix_count,
      classifiedCount: data.classified_count,
      totalPathCount: data.total_path_count,
      elapsedSecs: data.elapsed_secs,
      hitLimit: data.hit_limit,
    });
    setValidRunning(!!data.running);
    if (!data.running) stopValidPolling();
  };

  const pollValidOnce = async () => {
    try {
      const res = await fetch('http://localhost:3001/valid');
      const data = await res.json();
      applyValidStatus(data);
    } catch (e) {
      setValidResult({ error: 'Could not reach Rust service' });
      setValidRunning(false);
      stopValidPolling();
    }
  };

  const fetchValid = async () => {
    stopValidPolling();
    setValidRunning(true);
    setValidResult({
      valid: null, path: null, uncoveredPositions: null,
      coverGroups: [], totalPrefixCount: 0,
      hitLimit: false,
    });
    try {
      const res = await fetch('http://localhost:3001/valid', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      if (!res.ok) throw new Error('start failed');
    } catch (e) {
      setValidResult({ error: 'Could not reach Rust service' });
      setValidRunning(false);
      return;
    }
    pollValidOnce();
    validPollRef.current = setInterval(() => pollValidOnce(), 500);
  };

  const cancelValid = async () => {
    stopValidPolling();
    try {
      await fetch('http://localhost:3001/valid/cancel', { method: 'POST' });
    } catch (e) { /* ignore */ }
    try {
      const res = await fetch('http://localhost:3001/valid');
      const data = await res.json();
      applyValidStatus(data);
    } catch (e) { /* ignore */ }
    setValidRunning(false);
    if (cadicalValidRunning) cancelCadicalValid();
  };

  // ── Satisfiable polling ───────────────────────────────────────────────────
  const stopSatPolling = () => {
    if (satPollRef.current) {
      clearInterval(satPollRef.current);
      satPollRef.current = null;
    }
  };

  const applySatStatus = (data) => {
    if (data.error) {
      setSatResult({ error: data.error });
      setSatRunning(false);
      stopSatPolling();
      return;
    }
    setSatResult({
      satisfiable: !data.running ? (data.uncovered_paths.length > 0) : null,
      path: data.uncovered_paths[0] || null,
      uncoveredPositions: data.uncovered_path_positions[0] || null,
      coverGroups: data.cover_groups,
      totalPrefixCount: data.total_prefix_count,
      classifiedCount: data.classified_count,
      totalPathCount: data.total_path_count,
      elapsedSecs: data.elapsed_secs,
      hitLimit: data.hit_limit,
      isComplement: true,
    });
    setSatRunning(!!data.running);
    if (!data.running) stopSatPolling();
  };

  const pollSatOnce = async () => {
    try {
      const res = await fetch('http://localhost:3001/satisfiable');
      const data = await res.json();
      applySatStatus(data);
    } catch (e) {
      setSatResult({ error: 'Could not reach Rust service' });
      setSatRunning(false);
      stopSatPolling();
    }
  };

  const fetchSat = async () => {
    stopSatPolling();
    setSatRunning(true);
    setSatResult({
      satisfiable: null, path: null, uncoveredPositions: null,
      coverGroups: [], totalPrefixCount: 0,
      hitLimit: false, isComplement: true,
    });
    try {
      const res = await fetch('http://localhost:3001/satisfiable', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      if (!res.ok) throw new Error('start failed');
    } catch (e) {
      setSatResult({ error: 'Could not reach Rust service' });
      setSatRunning(false);
      return;
    }
    pollSatOnce();
    satPollRef.current = setInterval(() => pollSatOnce(), 500);
  };

  const cancelSat = async () => {
    stopSatPolling();
    try {
      await fetch('http://localhost:3001/satisfiable/cancel', { method: 'POST' });
    } catch (e) { /* ignore */ }
    try {
      const res = await fetch('http://localhost:3001/satisfiable');
      const data = await res.json();
      applySatStatus(data);
    } catch (e) { /* ignore */ }
    setSatRunning(false);
    if (cadicalSatRunning) cancelCadicalSat();
  };

  // ── CaDiCaL Valid polling ──────────────────────────────────────────────────
  const stopCadicalValidPolling = () => {
    if (cadicalValidPollRef.current) {
      clearInterval(cadicalValidPollRef.current);
      cadicalValidPollRef.current = null;
    }
  };

  const applyCadicalValidStatus = (data) => {
    if (data.error) {
      setCadicalValidResult({ error: data.error });
      setCadicalValidRunning(false);
      stopCadicalValidPolling();
      return;
    }
    if (data.result || !data.running) {
      const r = data.result;
      setCadicalValidResult(r ? {
        assignment: r.assignment,
        learnedClauses: r.learned_clauses,
        elapsedSecs: r.elapsed_secs,
      } : { assignment: null, learnedClauses: [], elapsedSecs: 0 });
      setCadicalValidRunning(false);
      stopCadicalValidPolling();
    }
  };

  const pollCadicalValidOnce = async () => {
    try {
      const res = await fetch('http://localhost:3001/cadical/valid');
      const data = await res.json();
      applyCadicalValidStatus(data);
    } catch (e) {
      setCadicalValidResult({ error: 'Could not reach Rust service' });
      setCadicalValidRunning(false);
      stopCadicalValidPolling();
    }
  };

  const startCadicalValid = async () => {
    stopCadicalValidPolling();
    setCadicalValidRunning(true);
    setCadicalValidResult(null);
    try {
      const res = await fetch('http://localhost:3001/cadical/valid', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      if (!res.ok) throw new Error('start failed');
    } catch (e) {
      setCadicalValidResult({ error: 'Could not reach Rust service' });
      setCadicalValidRunning(false);
      return;
    }
    pollCadicalValidOnce();
    cadicalValidPollRef.current = setInterval(() => pollCadicalValidOnce(), 500);
  };

  const cancelCadicalValid = async () => {
    stopCadicalValidPolling();
    try {
      await fetch('http://localhost:3001/cadical/valid/cancel', { method: 'POST' });
    } catch (e) { /* ignore */ }
    try {
      const res = await fetch('http://localhost:3001/cadical/valid');
      const data = await res.json();
      applyCadicalValidStatus(data);
    } catch (e) { /* ignore */ }
    setCadicalValidRunning(false);
  };

  // ── CaDiCaL Sat polling ───────────────────────────────────────────────────
  const stopCadicalSatPolling = () => {
    if (cadicalSatPollRef.current) {
      clearInterval(cadicalSatPollRef.current);
      cadicalSatPollRef.current = null;
    }
  };

  const applyCadicalSatStatus = (data) => {
    if (data.error) {
      setCadicalSatResult({ error: data.error });
      setCadicalSatRunning(false);
      stopCadicalSatPolling();
      return;
    }
    if (data.result || !data.running) {
      const r = data.result;
      setCadicalSatResult(r ? {
        assignment: r.assignment,
        learnedClauses: r.learned_clauses,
        elapsedSecs: r.elapsed_secs,
      } : { assignment: null, learnedClauses: [], elapsedSecs: 0 });
      setCadicalSatRunning(false);
      stopCadicalSatPolling();
    }
  };

  const pollCadicalSatOnce = async () => {
    try {
      const res = await fetch('http://localhost:3001/cadical/sat');
      const data = await res.json();
      applyCadicalSatStatus(data);
    } catch (e) {
      setCadicalSatResult({ error: 'Could not reach Rust service' });
      setCadicalSatRunning(false);
      stopCadicalSatPolling();
    }
  };

  const startCadicalSat = async () => {
    stopCadicalSatPolling();
    setCadicalSatRunning(true);
    setCadicalSatResult(null);
    try {
      const res = await fetch('http://localhost:3001/cadical/sat', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      if (!res.ok) throw new Error('start failed');
    } catch (e) {
      setCadicalSatResult({ error: 'Could not reach Rust service' });
      setCadicalSatRunning(false);
      return;
    }
    pollCadicalSatOnce();
    cadicalSatPollRef.current = setInterval(() => pollCadicalSatOnce(), 500);
  };

  const cancelCadicalSat = async () => {
    stopCadicalSatPolling();
    try {
      await fetch('http://localhost:3001/cadical/sat/cancel', { method: 'POST' });
    } catch (e) { /* ignore */ }
    try {
      const res = await fetch('http://localhost:3001/cadical/sat');
      const data = await res.json();
      applyCadicalSatStatus(data);
    } catch (e) { /* ignore */ }
    setCadicalSatRunning(false);
  };

  const handlePaths = () => {
    if (pathsResult && !pathsResult.error) {
      stopPathsPolling();
      if (pathsRunning) { fetch('http://localhost:3001/paths/cancel', { method: 'POST' }).catch(()=>{}); }
      setPathsResult(null); setPathsRunning(false); setComplementData(false); return;
    }
    stopValidPolling();
    if (validRunning) { fetch('http://localhost:3001/valid/cancel', { method: 'POST' }).catch(()=>{}); setValidRunning(false); }
    setValidResult(null);
    stopSatPolling();
    if (satRunning) { fetch('http://localhost:3001/satisfiable/cancel', { method: 'POST' }).catch(()=>{}); setSatRunning(false); }
    setSatResult(null);
    stopCadicalValidPolling();
    if (cadicalValidRunning) { fetch('http://localhost:3001/cadical/valid/cancel', { method: 'POST' }).catch(()=>{}); setCadicalValidRunning(false); }
    setCadicalValidResult(null); setCadicalValidAsgnOn(false);
    stopCadicalSatPolling();
    if (cadicalSatRunning) { fetch('http://localhost:3001/cadical/sat/cancel', { method: 'POST' }).catch(()=>{}); setCadicalSatRunning(false); }
    setCadicalSatResult(null); setCadicalSatAsgnOn(false);
    fetchPaths();
  };

  // Stop polling on unmount.
  useEffect(() => () => { stopPathsPolling(); stopValidPolling(); stopSatPolling(); stopCadicalValidPolling(); stopCadicalSatPolling(); }, []);

  // Re-fetch paths when the limit or complement checkbox changes while the display is open
  useEffect(() => {
    if (pathsResult && !pathsResult.error) fetchPaths();
  }, [pathsLimit, pathsComp]);

  // Auto-rotate to complement when sat selections are active, rotate back when none
  useEffect(() => {
    if (!satResult || satResult.error) return;
    const hasSelection = satSelected.size > 0 || satUncovOn;
    setComplementData(hasSelection ? true : false);
  }, [satResult, satSelected, satUncovOn]);

  const handleComplement = () => {
    if (!ast) return;
    setComplementData(prev => !prev);
  };

  const handleValid = () => {
    if (validResult && !validResult.error) {
      stopValidPolling();
      if (validRunning) { fetch('http://localhost:3001/valid/cancel', { method: 'POST' }).catch(()=>{}); }
      setValidResult(null); setValidRunning(false);
      // Also cancel cadical valid
      stopCadicalValidPolling();
      if (cadicalValidRunning) { fetch('http://localhost:3001/cadical/valid/cancel', { method: 'POST' }).catch(()=>{}); }
      setCadicalValidResult(null); setCadicalValidRunning(false); setCadicalValidAsgnOn(false);
      return;
    }
    stopSatPolling();
    if (satRunning) { fetch('http://localhost:3001/satisfiable/cancel', { method: 'POST' }).catch(()=>{}); setSatRunning(false); }
    setSatResult(null);
    stopCadicalSatPolling();
    if (cadicalSatRunning) { fetch('http://localhost:3001/cadical/sat/cancel', { method: 'POST' }).catch(()=>{}); setCadicalSatRunning(false); }
    setCadicalSatResult(null); setCadicalSatAsgnOn(false);
    stopPathsPolling();
    if (pathsRunning) { fetch('http://localhost:3001/paths/cancel', { method: 'POST' }).catch(()=>{}); setPathsRunning(false); }
    setPathsResult(null); setComplementData(false);
    fetchValid();
    if (cadicalEnabled) startCadicalValid();
  };

  const handleSatisfiable = () => {
    if (satResult && !satResult.error) {
      stopSatPolling();
      if (satRunning) { fetch('http://localhost:3001/satisfiable/cancel', { method: 'POST' }).catch(()=>{}); }
      setSatResult(null); setSatRunning(false); setComplementData(false);
      // Also cancel cadical sat
      stopCadicalSatPolling();
      if (cadicalSatRunning) { fetch('http://localhost:3001/cadical/sat/cancel', { method: 'POST' }).catch(()=>{}); }
      setCadicalSatResult(null); setCadicalSatRunning(false); setCadicalSatAsgnOn(false);
      return;
    }
    stopValidPolling();
    if (validRunning) { fetch('http://localhost:3001/valid/cancel', { method: 'POST' }).catch(()=>{}); setValidRunning(false); }
    setValidResult(null);
    stopCadicalValidPolling();
    if (cadicalValidRunning) { fetch('http://localhost:3001/cadical/valid/cancel', { method: 'POST' }).catch(()=>{}); setCadicalValidRunning(false); }
    setCadicalValidResult(null); setCadicalValidAsgnOn(false);
    stopPathsPolling();
    if (pathsRunning) { fetch('http://localhost:3001/paths/cancel', { method: 'POST' }).catch(()=>{}); setPathsRunning(false); }
    setPathsResult(null);
    fetchSat();
    if (cadicalEnabled) startCadicalSat();
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

      <div style={{ marginBottom: 10 }}>
        <div
          onClick={() => setHelpOpen(prev => !prev)}
          style={{
            display: 'flex', alignItems: 'center', gap: 6, cursor: 'pointer',
            userSelect: 'none', fontSize: 13, color: '#555', marginBottom: helpOpen ? 6 : 0,
          }}
        >
          <span style={{ fontSize: 10, fontFamily: 'monospace', color: '#999' }}>{helpOpen ? '▼' : '▶'}</span>
          <span style={{ fontWeight: 500 }}>Legend</span>
        </div>
        {helpOpen && <Legend />}
      </div>

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
        <div style={{ display: 'flex', gap: 4, alignItems: 'center' }}>
          {btn('⚡ Simplify',    handleSimplify,    '#1a6bcc', !ast || loading, !ast ? "Fix syntax errors first" : `Simplify to minimal ${simplifyForm}`)}
          <span style={{ display: 'inline-flex', border: '1px solid #1a6bcc', borderRadius: 4, overflow: 'hidden', fontSize: 12 }}>
            {['DNF', 'CNF'].map(f => (
              <span key={f}
                onClick={() => setSimplifyForm(f)}
                title={f === 'DNF' ? "Disjunctive normal form (sum of products)" : "Conjunctive normal form (product of sums)"}
                style={{
                  padding: '4px 8px', cursor: 'pointer', userSelect: 'none',
                  background: simplifyForm === f ? '#1a6bcc' : '#fff',
                  color: simplifyForm === f ? '#fff' : '#1a6bcc',
                  fontWeight: simplifyForm === f ? 'bold' : 'normal',
                }}>{f}</span>
            ))}
          </span>
          {btn("A'  Complement", handleComplement,  '#2a6a6a', !ast,            !ast ? "Fix syntax errors first" : "Show the complement as a nested box diagram")}
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

      {/* Diagrams */}
      {ast && (
        <>
          <div style={{ fontSize: 12, color: '#888', marginBottom: 10 }}>
            {complementData ? 'Complement' : simplified ? 'Original' : 'Diagram'}{error ? ' (last valid formula)' : ''} — border colors show nesting depth:
          </div>
          <ZoomPanWrapper key={input} bg={complementData ? '#f0fafa' : '#f8f9fc'} border={complementData ? '1px solid #a0d4d4' : '1px solid #dde'} opacity={error ? 0.5 : 1} rotated={!!complementData}>
            <DiagramWithConnections
              node={ast}
              complementView={!!complementData}
              coverGroups={pathsResult?.coverGroups ?? (complementData ? satResult?.coverGroups : validResult?.coverGroups) ?? null}
              selectedGroups={pathsResult?.coverGroups ? pathsSelected : (complementData ? satSelected : validSelected)}
              highlightedPaths={(() => {
                const paths = [
                  ...(pathsResult?.uncoveredPositions?.filter((_, i) => pathsUncovSel.has(i)) ?? []),
                  ...(validUncovOn && validResult?.uncoveredPositions ? [validResult.uncoveredPositions] : []),
                  ...(satUncovOn && satResult?.uncoveredPositions ? [satResult.uncoveredPositions] : []),
                ];
                return paths.length ? paths : null;
              })()}
              assignmentEval={(() => {
                if (!ast) return null;
                // Build assignment from path string
                const buildAsgn = (pathStr) => {
                  if (!pathStr) return null;
                  const inner = pathStr.startsWith('{') && pathStr.endsWith('}') ? pathStr.slice(1, -1) : null;
                  if (!inner) return null;
                  const asgn = {};
                  inner.split(', ').forEach(l => {
                    const neg = l.endsWith("'");
                    const base = neg ? l.slice(0, -1) : l;
                    if (!(base in asgn)) asgn[base] = neg ? '1' : '0';
                  });
                  return asgn;
                };
                // Build assignment from cadical [var_index, is_negated] pairs
                const buildCadicalAsgn = (cadResult) => {
                  if (!cadResult?.assignment) return null;
                  const allVars = extractVars(ast);
                  const asgn = {};
                  cadResult.assignment.forEach(([varIdx, neg]) => {
                    const varName = allVars[varIdx];
                    if (varName) asgn[varName] = neg ? '0' : '1';
                  });
                  return asgn;
                };
                if (validAsgnOn && validResult?.path) {
                  const asgn = buildAsgn(validResult.path);
                  return asgn ? evaluateAst(ast, asgn) : null;
                }
                if (satAsgnOn && satResult?.path) {
                  const asgn = buildAsgn(satResult.path);
                  return asgn ? evaluateAst(ast, asgn) : null;
                }
                if (cadicalValidAsgnOn && cadicalValidResult?.assignment) {
                  const asgn = buildCadicalAsgn(cadicalValidResult);
                  return asgn ? evaluateAst(ast, asgn) : null;
                }
                if (cadicalSatAsgnOn && cadicalSatResult?.assignment) {
                  const asgn = buildCadicalAsgn(cadicalSatResult);
                  return asgn ? evaluateAst(ast, asgn) : null;
                }
                return null;
              })()}
            />
          </ZoomPanWrapper>

          {simplified && (
            <>
              <div style={{ fontSize: 12, color: '#888', marginTop: 20, marginBottom: 10 }}>
                Simplified — <span style={{ fontFamily: 'Georgia, serif' }}>{simplified.formula}</span>
              </div>
              <ZoomPanWrapper key={simplified.formula} bg='#f0fff4' border='1px solid #b2e0b2'>
                <DiagramWithConnections node={simplified.ast} coverGroups={null} selectedGroups={new Set()} highlightedPaths={null} />
              </ZoomPanWrapper>
              <div style={{ display: 'flex', justifyContent: 'center', marginTop: 10 }}>
                {btn('Use simplified formula', () => setInput(simplified.formula), '#2a7a2a')}
              </div>
            </>
          )}

      {/* Analysis buttons */}
      <div style={{ display: 'flex', justifyContent: 'center', gap: 4, marginTop: 12, marginBottom: 8, flexWrap: 'wrap' }}>
        {btn('✓ Valid?',       handleValid,       '#6a2a9a', !ast || loading, !ast ? "Fix syntax errors first" : "Check if formula is a tautology")}
        {validRunning && (
          <span style={{ display: 'inline-flex', alignItems: 'center', gap: 6 }}>
            <button
              onClick={cancelValid}
              title="Cancel validity check"
              style={{
                display: 'inline-flex', alignItems: 'center', gap: 6,
                padding: '4px 10px', fontSize: 12, border: '1px solid #d4a0f0',
                borderRadius: 4, background: '#f8f0ff', color: '#6a2a9a',
                cursor: 'pointer',
              }}
            >
              <span
                aria-hidden="true"
                style={{
                  display: 'inline-block', width: 12, height: 12,
                  border: '2px solid #d4a0f0', borderTopColor: '#6a2a9a',
                  borderRadius: '50%', animation: 'logic-spin 0.8s linear infinite',
                }}
              />
              Cancel
            </button>
            {validResult?.totalPathCount > 0 && (() => {
              const classified = validResult.classifiedCount ?? 0;
              const total = validResult.totalPathCount;
              const elapsed = validResult.elapsedSecs ?? 0;
              const pct = Math.min(100, (classified / total) * 100);
              const rate = elapsed > 0 ? Math.round(classified / elapsed) : 0;
              return <span style={{ display: 'inline-flex', alignItems: 'center', gap: 4, fontSize: 11, color: '#666' }}>
                <span style={{
                  display: 'inline-block', width: 80, height: 8,
                  background: '#e0e0e0', borderRadius: 4, overflow: 'hidden',
                }}>
                  <span style={{
                    display: 'block', height: '100%', borderRadius: 4,
                    background: '#6a2a9a', width: `${pct}%`,
                    transition: 'width 0.3s ease',
                  }} />
                </span>
                {pct.toFixed(1)}%{rate > 0 ? ` (${fmtNum(rate)}/s)` : ''}
              </span>;
            })()}
          </span>
        )}
        {btn('? Satisfiable?', handleSatisfiable, '#7a4a00', !ast || loading, !ast ? "Fix syntax errors first" : "Check if formula has a satisfying assignment")}
        {satRunning && (
          <span style={{ display: 'inline-flex', alignItems: 'center', gap: 6 }}>
            <button
              onClick={cancelSat}
              title="Cancel satisfiability check"
              style={{
                display: 'inline-flex', alignItems: 'center', gap: 6,
                padding: '4px 10px', fontSize: 12, border: '1px solid #e0c870',
                borderRadius: 4, background: '#fffaf0', color: '#7a4a00',
                cursor: 'pointer',
              }}
            >
              <span
                aria-hidden="true"
                style={{
                  display: 'inline-block', width: 12, height: 12,
                  border: '2px solid #e0c870', borderTopColor: '#7a4a00',
                  borderRadius: '50%', animation: 'logic-spin 0.8s linear infinite',
                }}
              />
              Cancel
            </button>
            {satResult?.totalPathCount > 0 && (() => {
              const classified = satResult.classifiedCount ?? 0;
              const total = satResult.totalPathCount;
              const elapsed = satResult.elapsedSecs ?? 0;
              const pct = Math.min(100, (classified / total) * 100);
              const rate = elapsed > 0 ? Math.round(classified / elapsed) : 0;
              return <span style={{ display: 'inline-flex', alignItems: 'center', gap: 4, fontSize: 11, color: '#666' }}>
                <span style={{
                  display: 'inline-block', width: 80, height: 8,
                  background: '#e0e0e0', borderRadius: 4, overflow: 'hidden',
                }}>
                  <span style={{
                    display: 'block', height: '100%', borderRadius: 4,
                    background: '#7a4a00', width: `${pct}%`,
                    transition: 'width 0.3s ease',
                  }} />
                </span>
                {pct.toFixed(1)}%{rate > 0 ? ` (${fmtNum(rate)}/s)` : ''}
              </span>;
            })()}
          </span>
        )}
        <label style={{ display: 'flex', alignItems: 'center', gap: 3, cursor: 'pointer', fontSize: 13 }}
               title="Also run CaDiCaL SAT solver alongside matrix checks">
          <input type="checkbox" checked={cadicalEnabled} onChange={e => setCadicalEnabled(e.target.checked)} />
          CaDiCaL
        </label>
        {btn('ρ  Paths',       handlePaths,       '#4a4a8a', !ast || loading, !ast ? "Fix syntax errors first" : "Show paths through the matrix")}
        <label style={{ display: 'flex', alignItems: 'center', gap: 3, cursor: 'pointer', fontSize: 13 }}
               title="Show paths of the complement">
          <input type="checkbox" checked={pathsComp} onChange={e => setPathsComp(e.target.checked)} />
          <span style={{ fontFamily: 'Georgia, serif', fontWeight: 'bold' }}>'</span>
        </label>
        <input
          type="number" min={1} value={pathsLimit}
          onChange={e => setPathsLimit(Math.max(1, parseInt(e.target.value) || 1))}
          title="Maximum number of paths to enumerate"
          style={{
            width: 50, padding: '4px 6px', fontSize: 12, border: '1px solid #bbb',
            borderRadius: 4, textAlign: 'center',
          }}
        />
        {pathsRunning && (
          <span style={{ display: 'inline-flex', alignItems: 'center', gap: 6 }}>
            <button
              onClick={cancelPaths}
              title="Cancel path generation"
              style={{
                display: 'inline-flex', alignItems: 'center', gap: 6,
                padding: '4px 10px', fontSize: 12, border: '1px solid #c8c8e8',
                borderRadius: 4, background: '#f7f7fd', color: '#4a4a8a',
                cursor: 'pointer',
              }}
            >
              <span
                aria-hidden="true"
                style={{
                  display: 'inline-block', width: 12, height: 12,
                  border: '2px solid #c8c8e8', borderTopColor: '#4a4a8a',
                  borderRadius: '50%', animation: 'logic-spin 0.8s linear infinite',
                }}
              />
              Cancel
            </button>
            {pathsResult?.totalPathCount > 0 && (() => {
              const classified = pathsResult.classifiedCount ?? 0;
              const total = pathsResult.totalPathCount;
              const elapsed = pathsResult.elapsedSecs ?? 0;
              const pct = Math.min(100, (classified / total) * 100);
              const rate = elapsed > 0 ? Math.round(classified / elapsed) : 0;
              return <span style={{ display: 'inline-flex', alignItems: 'center', gap: 4, fontSize: 11, color: '#666' }}>
                <span style={{
                  display: 'inline-block', width: 80, height: 8,
                  background: '#e0e0e0', borderRadius: 4, overflow: 'hidden',
                }}>
                  <span style={{
                    display: 'block', height: '100%', borderRadius: 4,
                    background: '#4a4a8a', width: `${pct}%`,
                    transition: 'width 0.3s ease',
                  }} />
                </span>
                {pct.toFixed(1)}%{rate > 0 ? ` (${fmtNum(rate)}/s)` : ''}
              </span>;
            })()}
          </span>
        )}
      </div>

      {/* Valid result */}
      {validResult && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 8,
          color: validResult.error ? '#8b0000' : validResult.valid === true ? '#1a5c1a' : '#6a2a9a',
          background: validResult.error ? '#fff5f5' : validResult.valid === true ? '#f0fff0' : '#f8f0ff',
          border: `1.5px solid ${validResult.error ? '#f5c2c2' : validResult.valid === true ? '#b2e0b2' : '#d4a0f0'}`,
          padding: '9px 14px', borderRadius: 6, fontSize: 13, marginBottom: 12,
        }}>
          {validResult.error
            ? `✗ ${validResult.error}`
            : validResult.valid === null
              ? <span>Checking validity{validResult.totalPathCount > 0 ? ` — ${fmtNum(validResult.classifiedCount ?? 0)} / ${fmtNum(validResult.totalPathCount)} paths classified` : ''}...</span>
              : validResult.valid
              ? <span>
                  {(() => {
                    const total = validResult.totalPathCount ?? 0;
                    const elapsed = validResult.elapsedSecs ?? 0;
                    const rate = elapsed > 0 ? Math.round((validResult.classifiedCount ?? 0) / elapsed) : 0;
                    const ratePart = elapsed > 0 ? ` in ${fmtTime(elapsed)} at ${fmtNum(rate)} paths/s` : '';
                    return `✓ Valid — all ${fmtNum(total)} paths through the matrix are covered${ratePart}`;
                  })()}
                  {validResult.coverGroups?.length > 0 && ast && (() => {
                    const resName = pos => resolvePosition(ast, pos)?.n ?? pos.join(',');
                    const tooMany = (validResult.totalPrefixCount ?? 0) > 1000;
                    return <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        {fmtNum(validResult.coverGroups.length)} {validResult.coverGroups.length === 1 ? 'pair' : 'pairs'} in the cover covering {fmtNum(validResult.totalPrefixCount)} {validResult.totalPrefixCount === 1 ? 'prefix' : 'prefixes'}{(() => {
                          const lo = Math.min(...validResult.coverGroups.map(g => g.prefix_length_min));
                          const hi = Math.max(...validResult.coverGroups.map(g => g.prefix_length_max));
                          return lo === hi ? ` ${lo} long` : ` ${lo}..${hi} long`;
                        })()}:
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set(validResult.coverGroups.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          const varIndices = {};
                          validResult.coverGroups.forEach((g, i) => {
                            const a = resName(g.pair[0]);
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
                                }}><VarLabel name={v} /></a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      <div style={{
                        ...(validResult.coverGroups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                        marginTop: 4,
                      }}>
                        {validResult.coverGroups.map((g, gi) => {
                          const a = resName(g.pair[0]);
                          const b = resName(g.pair[1]);
                          const isSelected = validSelected.has(gi);
                          const lenRange = g.prefix_length_min === g.prefix_length_max
                            ? ` ${g.prefix_length_min} long`
                            : ` ${g.prefix_length_min}..${g.prefix_length_max} long`;
                          if (tooMany || !g.prefixes?.length) {
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span onClick={() => setValidSelected(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                              </span>
                              <span style={{ color: '#888', fontSize: 11, marginLeft: 4 }}>
                                {fmtNum(g.count)} {g.count === 1 ? 'prefix' : 'prefixes'}{lenRange}
                              </span>
                            </div>;
                          }
                          const prefixes = g.prefixes.map(p => {
                            const names = p.map(pos => resName(pos));
                            return <>{'{'}{names.map((n, ni) => <span key={ni}>{ni > 0 && ', '}<VarLabel name={n} /></span>)}{'}' }</>;
                          });
                          const expanded = validExpanded.has(gi);
                          return <div key={gi} style={{ fontWeight: 'normal' }}>
                            <span onClick={() => setValidSelected(prev => {
                              const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                            })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                              <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                            </span>
                            {prefixes.length > 0 && <>
                              <span onClick={e => { e.stopPropagation(); setValidExpanded(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              }); }}
                                style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                              >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'prefix' : 'prefixes'}{lenRange}</span>
                              {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                              </div>}
                            </>}
                          </div>;
                        })}
                      </div>
                    </span>;
                  })()}
                </span>
              : <span>
                  {(() => {
                    const total = validResult.totalPathCount ?? 0;
                    const elapsed = validResult.elapsedSecs ?? 0;
                    const rate = elapsed > 0 ? Math.round((validResult.classifiedCount ?? 0) / elapsed) : 0;
                    const ratePart = elapsed > 0 ? ` in ${fmtTime(elapsed)} at ${fmtNum(rate)} paths/s` : '';
                    return `✗ Not valid — falsifying assignment and uncovered path in ${fmtNum(total)} path matrix${ratePart}:`;
                  })()}
                  {validResult.path && (() => {
                    const p = validResult.path;
                    const inner = p.startsWith('{') && p.endsWith('}') ? p.slice(1, -1) : null;
                    const lits = inner ? inner.split(', ') : [];
                    const long = lits.length > 10;
                    // Build assignment: variable (no complement) = 0 if complemented, 1 if positive
                    const asgn = {};
                    lits.forEach(l => {
                      const neg = l.endsWith("'");
                      const base = neg ? l.slice(0, -1) : l;
                      if (!(base in asgn)) asgn[base] = neg ? '1' : '0';
                    });
                    const asgnEntries = Object.keys(asgn).sort().map(v => ({ name: v, val: asgn[v] }));
                    const aLong = asgnEntries.length > 10;
                    const allVars = ast ? extractVars(ast) : [];
                    const valueStr = allVars.map(v => v in asgn ? asgn[v] : '-').join('');
                    return <span style={{ fontWeight: 'normal' }}>
                      <br />
                      <span onClick={() => { const next = !validAsgnOn; setValidAsgnOn(next); if (next) { setSatAsgnOn(false); setCadicalValidAsgnOn(false); setCadicalSatAsgnOn(false); } }}
                        style={{ cursor: 'pointer', opacity: validAsgnOn ? 1 : 0.35 }}>
                        assignment ({asgnEntries.length}):{' '}
                        {validAsgnFmt === 0 && <>
                          <b style={{ fontFamily: 'Georgia, serif' }}>
                            {((!aLong || validVarsExpanded) ? asgnEntries : asgnEntries.slice(0, 10)).map((e, ei) => <span key={ei}>{ei > 0 && ', '}<VarLabel name={e.name} />{`=${e.val}`}</span>)}
                            {aLong && !validVarsExpanded && ', '}
                          </b>
                          {aLong && !validVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setValidVarsExpanded(true); }}
                            style={{ fontFamily: 'Georgia, serif', fontWeight: 'bold', textDecoration: 'none' }}>{'…'}</a>}
                          {aLong && validVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setValidVarsExpanded(false); }}
                            style={{ fontSize: 11, color: '#888', marginLeft: 4 }}>less</a>}
                        </>}
                        {validAsgnFmt === 1 && <b style={{ fontFamily: 'Georgia, serif' }}>
                          {asgnEntries.map((e, ei) => <span key={ei}>{ei > 0 && ' '}<VarLabel name={e.name} /></span>)}
                          {' = '}{asgnEntries.map(e => e.val).join('')}
                        </b>}
                        {validAsgnFmt === 2 && <b style={{ fontFamily: 'Georgia, serif' }}>{valueStr}</b>}
                      </span>
                      {' '}<a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setValidAsgnFmt(f => (f + 1) % 3); }}
                        style={{ fontSize: 11, color: '#888' }}>{['factored', 'value', 'expanded'][validAsgnFmt]}</a>
                      <br />
                      <span onClick={() => setValidUncovOn(prev => !prev)}
                        style={{ cursor: 'pointer', opacity: validUncovOn ? 1 : 0.35 }}>
                        path ({lits.length}): <b style={{ fontFamily: 'Georgia, serif' }}>
                          {'{'}{((!long || validPathExpanded) ? lits : lits.slice(0, 10)).map((l, li) => <span key={li}>{li > 0 && ', '}<VarLabel name={l} /></span>)}
                          {(!long || validPathExpanded) ? '}' : ', '}
                        </b>
                        {long && !validPathExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setValidPathExpanded(true); }}
                          style={{ fontFamily: 'Georgia, serif', fontWeight: 'bold', textDecoration: 'none' }}>{'…}'}</a>}
                        {long && validPathExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setValidPathExpanded(false); }}
                          style={{ fontSize: 11, color: '#888', marginLeft: 4 }}>less</a>}
                      </span>
                    </span>;
                  })()}
                  {validResult.coverGroups?.length > 0 && ast && (() => {
                    const resName = pos => resolvePosition(ast, pos)?.n ?? pos.join(',');
                    const tooMany = (validResult.totalPrefixCount ?? 0) > 1000;
                    return <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        partial cover: {fmtNum(validResult.coverGroups.length)} {validResult.coverGroups.length === 1 ? 'pair' : 'pairs'}
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set(validResult.coverGroups.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setValidSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          const varIndices = {};
                          validResult.coverGroups.forEach((g, i) => {
                            const a = resName(g.pair[0]);
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
                                }}><VarLabel name={v} /></a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      <div style={{
                        ...(validResult.coverGroups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                        marginTop: 4,
                      }}>
                        {validResult.coverGroups.map((g, gi) => {
                          const a = resName(g.pair[0]);
                          const b = resName(g.pair[1]);
                          const isSelected = validSelected.has(gi);
                          const lenRange = g.prefix_length_min === g.prefix_length_max
                            ? ` ${g.prefix_length_min} long`
                            : ` ${g.prefix_length_min}..${g.prefix_length_max} long`;
                          if (tooMany || !g.prefixes?.length) {
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span onClick={() => setValidSelected(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                              </span>
                              <span style={{ color: '#888', fontSize: 11, marginLeft: 4 }}>
                                {fmtNum(g.count)} {g.count === 1 ? 'prefix' : 'prefixes'}{lenRange}
                              </span>
                            </div>;
                          }
                          const prefixes = g.prefixes.map(p => {
                            const names = p.map(pos => resName(pos));
                            return <>{'{'}{names.map((n, ni) => <span key={ni}>{ni > 0 && ', '}<VarLabel name={n} /></span>)}{'}' }</>;
                          });
                          const expanded = validExpanded.has(gi);
                          return <div key={gi} style={{ fontWeight: 'normal' }}>
                            <span onClick={() => setValidSelected(prev => {
                              const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                            })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                              <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                            </span>
                            {prefixes.length > 0 && <>
                              <span onClick={e => { e.stopPropagation(); setValidExpanded(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              }); }}
                                style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                              >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'prefix' : 'prefixes'}{lenRange}</span>
                              {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                              </div>}
                            </>}
                          </div>;
                        })}
                      </div>
                    </span>;
                  })()}
                </span>}
        </div>
      )}

      {/* CaDiCaL Valid result */}
      {(cadicalValidResult || cadicalValidRunning) && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 8,
          color: cadicalValidResult?.error ? '#8b0000' : cadicalValidResult?.assignment === null ? '#1a5c1a' : '#6a2a9a',
          background: cadicalValidResult?.error ? '#fff5f5' : cadicalValidResult?.assignment === null ? '#f0fff0' : '#f8f0ff',
          border: `1.5px solid ${cadicalValidResult?.error ? '#f5c2c2' : cadicalValidResult?.assignment === null ? '#b2e0b2' : '#d4a0f0'}`,
          padding: '9px 14px', borderRadius: 6, fontSize: 13, marginBottom: 12,
        }}>
          {cadicalValidRunning && !cadicalValidResult
            ? <span>CaDiCaL: checking validity...</span>
            : cadicalValidResult?.error
            ? `CaDiCaL: ${cadicalValidResult.error}`
            : cadicalValidResult?.assignment === null
            ? <span>CaDiCaL: valid in {(cadicalValidResult.elapsedSecs * 1000).toFixed(0)}ms
                {cadicalValidResult.learnedClauses?.length > 0 && <span style={{ fontWeight: 'normal' }}>
                  <br />
                  <span onClick={e => { e.stopPropagation(); setCadicalValidClausesExpanded(prev => !prev); }}
                    style={{ cursor: 'pointer', color: '#888', fontSize: 12, userSelect: 'none' }}>
                    {cadicalValidClausesExpanded ? '▾' : '▸'} {cadicalValidResult.learnedClauses.length} learned clause{cadicalValidResult.learnedClauses.length !== 1 ? 's' : ''}
                  </span>
                  {cadicalValidClausesExpanded && <div style={{ marginLeft: 16, fontSize: 11, color: '#666', maxHeight: '8em', overflowY: 'auto' }}>
                    {cadicalValidResult.learnedClauses.map((cl, ci) => <div key={ci}>{fmtClause(cl, ast ? extractVars(ast) : [])}</div>)}
                  </div>}
                </span>}
              </span>
            : <span>
                CaDiCaL: not valid in {(cadicalValidResult.elapsedSecs * 1000).toFixed(0)}ms
                {cadicalValidResult.assignment && (() => {
                  const allVars = ast ? extractVars(ast) : [];
                  const asgnEntries = cadicalValidResult.assignment.map(([varIdx, neg]) => ({
                    name: allVars[varIdx] ?? `v${varIdx}`, val: neg ? '0' : '1',
                  }));
                  const aLong = asgnEntries.length > 10;
                  const valueStr = allVars.map(v => {
                    const e = asgnEntries.find(a => a.name === v);
                    return e ? e.val : '-';
                  }).join('');
                  return <span style={{ fontWeight: 'normal' }}>
                    <br />
                    <span onClick={() => { const next = !cadicalValidAsgnOn; setCadicalValidAsgnOn(next); if (next) { setValidAsgnOn(false); setSatAsgnOn(false); setCadicalSatAsgnOn(false); } }}
                      style={{ cursor: 'pointer', opacity: cadicalValidAsgnOn ? 1 : 0.35 }}>
                      assignment ({asgnEntries.length}):{' '}
                      {cadicalValidAsgnFmt === 0 && <>
                        <b style={{ fontFamily: 'Georgia, serif' }}>
                          {((!aLong || cadicalValidVarsExpanded) ? asgnEntries : asgnEntries.slice(0, 10)).map((e, ei) => <span key={ei}>{ei > 0 && ', '}<VarLabel name={e.name} />{`=${e.val}`}</span>)}
                          {aLong && !cadicalValidVarsExpanded && ', '}
                        </b>
                        {aLong && !cadicalValidVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setCadicalValidVarsExpanded(true); }}
                          style={{ fontFamily: 'Georgia, serif', fontWeight: 'bold', textDecoration: 'none' }}>{'…'}</a>}
                        {aLong && cadicalValidVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setCadicalValidVarsExpanded(false); }}
                          style={{ fontSize: 11, color: '#888', marginLeft: 4 }}>less</a>}
                      </>}
                      {cadicalValidAsgnFmt === 1 && <b style={{ fontFamily: 'Georgia, serif' }}>
                        {asgnEntries.map((e, ei) => <span key={ei}>{ei > 0 && ' '}<VarLabel name={e.name} /></span>)}
                        {' = '}{asgnEntries.map(e => e.val).join('')}
                      </b>}
                      {cadicalValidAsgnFmt === 2 && <b style={{ fontFamily: 'Georgia, serif' }}>{valueStr}</b>}
                    </span>
                    {' '}<a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setCadicalValidAsgnFmt(f => (f + 1) % 3); }}
                      style={{ fontSize: 11, color: '#888' }}>{['factored', 'value', 'expanded'][cadicalValidAsgnFmt]}</a>
                  </span>;
                })()}
                {cadicalValidResult.learnedClauses?.length > 0 && <span style={{ fontWeight: 'normal' }}>
                  <br />
                  <span onClick={e => { e.stopPropagation(); setCadicalValidClausesExpanded(prev => !prev); }}
                    style={{ cursor: 'pointer', color: '#888', fontSize: 12, userSelect: 'none' }}>
                    {cadicalValidClausesExpanded ? '▾' : '▸'} {cadicalValidResult.learnedClauses.length} learned clause{cadicalValidResult.learnedClauses.length !== 1 ? 's' : ''}
                  </span>
                  {cadicalValidClausesExpanded && <div style={{ marginLeft: 16, fontSize: 11, color: '#666', maxHeight: '8em', overflowY: 'auto' }}>
                    {cadicalValidResult.learnedClauses.map((cl, ci) => <div key={ci}>{fmtClause(cl, ast ? extractVars(ast) : [])}</div>)}
                  </div>}
                </span>}
              </span>}
        </div>
      )}

      {/* Satisfiable result */}
      {satResult && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 8,
          color: satResult.error ? '#8b0000' : satResult.satisfiable === true ? '#1a5c1a' : '#7a4a00',
          background: satResult.error ? '#fff5f5' : satResult.satisfiable === true ? '#f0fff0' : '#fffaf0',
          border: `1.5px solid ${satResult.error ? '#f5c2c2' : satResult.satisfiable === true ? '#b2e0b2' : '#e0c870'}`,
          padding: '9px 14px', borderRadius: 6, fontSize: 13, marginBottom: 12,
        }}>
          {satResult.error
            ? `✗ ${satResult.error}`
            : satResult.satisfiable === null
              ? <span>Checking satisfiability{satResult.totalPathCount > 0 ? ` — ${fmtNum(satResult.classifiedCount ?? 0)} / ${fmtNum(satResult.totalPathCount)} paths classified` : ''}...</span>
              : satResult.satisfiable
              ? <span>
                  {(() => {
                    const total = satResult.totalPathCount ?? 0;
                    const elapsed = satResult.elapsedSecs ?? 0;
                    const rate = elapsed > 0 ? Math.round((satResult.classifiedCount ?? 0) / elapsed) : 0;
                    const ratePart = elapsed > 0 ? ` in ${fmtTime(elapsed)} at ${fmtNum(rate)} paths/s` : '';
                    return `✓ Satisfiable — satisfying assignment and uncovered path in complement of ${fmtNum(total)} path matrix${ratePart}:`;
                  })()}
                  {satResult.path && (() => {
                    const p = satResult.path;
                    const inner = p.startsWith('{') && p.endsWith('}') ? p.slice(1, -1) : null;
                    const lits = inner ? inner.split(', ') : [];
                    const long = lits.length > 10;
                    // Build satisfying assignment: complement literal a' → a=1, a → a=0
                    const asgn = {};
                    lits.forEach(l => {
                      const neg = l.endsWith("'");
                      const base = neg ? l.slice(0, -1) : l;
                      if (!(base in asgn)) asgn[base] = neg ? '1' : '0';
                    });
                    const asgnEntries = Object.keys(asgn).sort().map(v => ({ name: v, val: asgn[v] }));
                    const aLong = asgnEntries.length > 10;
                    const allVars = ast ? extractVars(ast) : [];
                    const valueStr = allVars.map(v => v in asgn ? asgn[v] : '-').join('');
                    return <span style={{ fontWeight: 'normal' }}>
                      <br />
                      <span onClick={() => { const next = !satAsgnOn; setSatAsgnOn(next); if (next) { setValidAsgnOn(false); setCadicalValidAsgnOn(false); setCadicalSatAsgnOn(false); } }}
                        style={{ cursor: 'pointer', opacity: satAsgnOn ? 1 : 0.35 }}>
                        assignment ({asgnEntries.length}):{' '}
                        {satAsgnFmt === 0 && <>
                          <b style={{ fontFamily: 'Georgia, serif' }}>
                            {((!aLong || satVarsExpanded) ? asgnEntries : asgnEntries.slice(0, 10)).map((e, ei) => <span key={ei}>{ei > 0 && ', '}<VarLabel name={e.name} />{`=${e.val}`}</span>)}
                            {aLong && !satVarsExpanded && ', '}
                          </b>
                          {aLong && !satVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setSatVarsExpanded(true); }}
                            style={{ fontFamily: 'Georgia, serif', fontWeight: 'bold', textDecoration: 'none' }}>{'…'}</a>}
                          {aLong && satVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setSatVarsExpanded(false); }}
                            style={{ fontSize: 11, color: '#888', marginLeft: 4 }}>less</a>}
                        </>}
                        {satAsgnFmt === 1 && <b style={{ fontFamily: 'Georgia, serif' }}>
                          {asgnEntries.map((e, ei) => <span key={ei}>{ei > 0 && ' '}<VarLabel name={e.name} /></span>)}
                          {' = '}{asgnEntries.map(e => e.val).join('')}
                        </b>}
                        {satAsgnFmt === 2 && <b style={{ fontFamily: 'Georgia, serif' }}>{valueStr}</b>}
                      </span>
                      {' '}<a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setSatAsgnFmt(f => (f + 1) % 3); }}
                        style={{ fontSize: 11, color: '#888' }}>{['factored', 'value', 'expanded'][satAsgnFmt]}</a>
                      <br />
                      <span onClick={() => setSatUncovOn(prev => !prev)}
                        style={{ cursor: 'pointer', opacity: satUncovOn ? 1 : 0.35 }}>
                        path ({lits.length}): <b style={{ fontFamily: 'Georgia, serif' }}>
                          {'{'}{((!long || satPathExpanded) ? lits : lits.slice(0, 10)).map((l, li) => <span key={li}>{li > 0 && ', '}<VarLabel name={l} /></span>)}
                          {(!long || satPathExpanded) ? '}' : ', '}
                        </b>
                        {long && !satPathExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setSatPathExpanded(true); }}
                          style={{ fontFamily: 'Georgia, serif', fontWeight: 'bold', textDecoration: 'none' }}>{'…}'}</a>}
                        {long && satPathExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setSatPathExpanded(false); }}
                          style={{ fontSize: 11, color: '#888', marginLeft: 4 }}>less</a>}
                      </span>
                    </span>;
                  })()}
                  {satResult.coverGroups?.length > 0 && ast && (() => {
                    const resName = pos => compName(resolvePosition(ast, pos)?.n) ?? pos.join(',');
                    const tooMany = (satResult.totalPrefixCount ?? 0) > 1000;
                    return <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        {fmtNum(satResult.coverGroups.length)} {satResult.coverGroups.length === 1 ? 'pair' : 'pairs'} in the partial cover covering {fmtNum(satResult.totalPrefixCount)} {satResult.totalPrefixCount === 1 ? 'prefix' : 'prefixes'}{(() => {
                          const lo = Math.min(...satResult.coverGroups.map(g => g.prefix_length_min));
                          const hi = Math.max(...satResult.coverGroups.map(g => g.prefix_length_max));
                          return lo === hi ? ` ${lo} long` : ` ${lo}..${hi} long`;
                        })()}:
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set(satResult.coverGroups.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          const varIndices = {};
                          satResult.coverGroups.forEach((g, i) => {
                            const a = resName(g.pair[0]);
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
                                }}><VarLabel name={v} /></a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      <div style={{
                        ...(satResult.coverGroups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                        marginTop: 4,
                      }}>
                        {satResult.coverGroups.map((g, gi) => {
                          const a = resName(g.pair[0]);
                          const b = resName(g.pair[1]);
                          const isSelected = satSelected.has(gi);
                          const lenRange = g.prefix_length_min === g.prefix_length_max
                            ? ` ${g.prefix_length_min} long`
                            : ` ${g.prefix_length_min}..${g.prefix_length_max} long`;
                          if (tooMany || !g.prefixes?.length) {
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span onClick={() => setSatSelected(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                              </span>
                              <span style={{ color: '#888', fontSize: 11, marginLeft: 4 }}>
                                {fmtNum(g.count)} {g.count === 1 ? 'prefix' : 'prefixes'}{lenRange}
                              </span>
                            </div>;
                          }
                          const prefixes = g.prefixes.map(p => {
                            const names = p.map(pos => resName(pos));
                            return <>{'{'}{names.map((n, ni) => <span key={ni}>{ni > 0 && ', '}<VarLabel name={n} /></span>)}{'}' }</>;
                          });
                          const expanded = satExpanded.has(gi);
                          return <div key={gi} style={{ fontWeight: 'normal' }}>
                            <span onClick={() => setSatSelected(prev => {
                              const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                            })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                              <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                            </span>
                            {prefixes.length > 0 && <>
                              <span onClick={e => { e.stopPropagation(); setSatExpanded(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              }); }}
                                style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                              >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'prefix' : 'prefixes'}{lenRange}</span>
                              {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                              </div>}
                            </>}
                          </div>;
                        })}
                      </div>
                    </span>;
                  })()}
                </span>
              : <span>
                  {(() => {
                    const total = satResult.totalPathCount ?? 0;
                    const elapsed = satResult.elapsedSecs ?? 0;
                    const rate = elapsed > 0 ? Math.round((satResult.classifiedCount ?? 0) / elapsed) : 0;
                    const ratePart = elapsed > 0 ? ` in ${fmtTime(elapsed)} at ${fmtNum(rate)} paths/s` : '';
                    return `✗ Unsatisfiable — all ${fmtNum(total)} paths in the complement are covered${ratePart}`;
                  })()}
                  {satResult.coverGroups?.length > 0 && ast && (() => {
                    const resName = pos => compName(resolvePosition(ast, pos)?.n) ?? pos.join(',');
                    const tooMany = (satResult.totalPrefixCount ?? 0) > 1000;
                    return <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        {fmtNum(satResult.coverGroups.length)} {satResult.coverGroups.length === 1 ? 'pair' : 'pairs'} in the cover covering {fmtNum(satResult.totalPrefixCount)} {satResult.totalPrefixCount === 1 ? 'prefix' : 'prefixes'}{(() => {
                          const lo = Math.min(...satResult.coverGroups.map(g => g.prefix_length_min));
                          const hi = Math.max(...satResult.coverGroups.map(g => g.prefix_length_max));
                          return lo === hi ? ` ${lo} long` : ` ${lo}..${hi} long`;
                        })()}:
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set(satResult.coverGroups.map((_, i) => i))); }}
                           style={{ fontSize: 11, color: '#888' }}>all</a>
                        {' · '}
                        <a href="#" onClick={e => { e.preventDefault(); setSatSelected(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>none</a>
                        {(() => {
                          const varIndices = {};
                          satResult.coverGroups.forEach((g, i) => {
                            const a = resName(g.pair[0]);
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
                                }}><VarLabel name={v} /></a>
                              </span>;
                            })}
                          </>;
                        })()}
                      </span>
                      <div style={{
                        ...(satResult.coverGroups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                        marginTop: 4,
                      }}>
                        {satResult.coverGroups.map((g, gi) => {
                          const a = resName(g.pair[0]);
                          const b = resName(g.pair[1]);
                          const isSelected = satSelected.has(gi);
                          const lenRange = g.prefix_length_min === g.prefix_length_max
                            ? ` ${g.prefix_length_min} long`
                            : ` ${g.prefix_length_min}..${g.prefix_length_max} long`;
                          if (tooMany || !g.prefixes?.length) {
                            return <div key={gi} style={{ fontWeight: 'normal' }}>
                              <span onClick={() => setSatSelected(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                                <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                              </span>
                              <span style={{ color: '#888', fontSize: 11, marginLeft: 4 }}>
                                {fmtNum(g.count)} {g.count === 1 ? 'prefix' : 'prefixes'}{lenRange}
                              </span>
                            </div>;
                          }
                          const prefixes = g.prefixes.map(p => {
                            const names = p.map(pos => resName(pos));
                            return <>{'{'}{names.map((n, ni) => <span key={ni}>{ni > 0 && ', '}<VarLabel name={n} /></span>)}{'}' }</>;
                          });
                          const expanded = satExpanded.has(gi);
                          return <div key={gi} style={{ fontWeight: 'normal' }}>
                            <span onClick={() => setSatSelected(prev => {
                              const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                            })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                              <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                            </span>
                            {prefixes.length > 0 && <>
                              <span onClick={e => { e.stopPropagation(); setSatExpanded(prev => {
                                const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                              }); }}
                                style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                                title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                              >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'prefix' : 'prefixes'}{lenRange}</span>
                              {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                                {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                              </div>}
                            </>}
                          </div>;
                        })}
                      </div>
                    </span>;
                  })()}
                </span>}
        </div>
      )}

      {/* CaDiCaL Sat result */}
      {(cadicalSatResult || cadicalSatRunning) && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 8,
          color: cadicalSatResult?.error ? '#8b0000' : cadicalSatResult?.assignment ? '#1a5c1a' : '#7a4a00',
          background: cadicalSatResult?.error ? '#fff5f5' : cadicalSatResult?.assignment ? '#f0fff0' : '#fffaf0',
          border: `1.5px solid ${cadicalSatResult?.error ? '#f5c2c2' : cadicalSatResult?.assignment ? '#b2e0b2' : '#e0c870'}`,
          padding: '9px 14px', borderRadius: 6, fontSize: 13, marginBottom: 12,
        }}>
          {cadicalSatRunning && !cadicalSatResult
            ? <span>CaDiCaL: checking satisfiability...</span>
            : cadicalSatResult?.error
            ? `CaDiCaL: ${cadicalSatResult.error}`
            : cadicalSatResult?.assignment
            ? <span>
                CaDiCaL: satisfiable in {(cadicalSatResult.elapsedSecs * 1000).toFixed(0)}ms
                {(() => {
                  const allVars = ast ? extractVars(ast) : [];
                  const asgnEntries = cadicalSatResult.assignment.map(([varIdx, neg]) => ({
                    name: allVars[varIdx] ?? `v${varIdx}`, val: neg ? '0' : '1',
                  }));
                  const aLong = asgnEntries.length > 10;
                  const valueStr = allVars.map(v => {
                    const e = asgnEntries.find(a => a.name === v);
                    return e ? e.val : '-';
                  }).join('');
                  return <span style={{ fontWeight: 'normal' }}>
                    <br />
                    <span onClick={() => { const next = !cadicalSatAsgnOn; setCadicalSatAsgnOn(next); if (next) { setValidAsgnOn(false); setSatAsgnOn(false); setCadicalValidAsgnOn(false); } }}
                      style={{ cursor: 'pointer', opacity: cadicalSatAsgnOn ? 1 : 0.35 }}>
                      assignment ({asgnEntries.length}):{' '}
                      {cadicalSatAsgnFmt === 0 && <>
                        <b style={{ fontFamily: 'Georgia, serif' }}>
                          {((!aLong || cadicalSatVarsExpanded) ? asgnEntries : asgnEntries.slice(0, 10)).map((e, ei) => <span key={ei}>{ei > 0 && ', '}<VarLabel name={e.name} />{`=${e.val}`}</span>)}
                          {aLong && !cadicalSatVarsExpanded && ', '}
                        </b>
                        {aLong && !cadicalSatVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setCadicalSatVarsExpanded(true); }}
                          style={{ fontFamily: 'Georgia, serif', fontWeight: 'bold', textDecoration: 'none' }}>{'…'}</a>}
                        {aLong && cadicalSatVarsExpanded && <a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setCadicalSatVarsExpanded(false); }}
                          style={{ fontSize: 11, color: '#888', marginLeft: 4 }}>less</a>}
                      </>}
                      {cadicalSatAsgnFmt === 1 && <b style={{ fontFamily: 'Georgia, serif' }}>
                        {asgnEntries.map((e, ei) => <span key={ei}>{ei > 0 && ' '}<VarLabel name={e.name} /></span>)}
                        {' = '}{asgnEntries.map(e => e.val).join('')}
                      </b>}
                      {cadicalSatAsgnFmt === 2 && <b style={{ fontFamily: 'Georgia, serif' }}>{valueStr}</b>}
                    </span>
                    {' '}<a href="#" onClick={e => { e.preventDefault(); e.stopPropagation(); setCadicalSatAsgnFmt(f => (f + 1) % 3); }}
                      style={{ fontSize: 11, color: '#888' }}>{['factored', 'value', 'expanded'][cadicalSatAsgnFmt]}</a>
                  </span>;
                })()}
                {cadicalSatResult.learnedClauses?.length > 0 && <span style={{ fontWeight: 'normal' }}>
                  <br />
                  <span onClick={e => { e.stopPropagation(); setCadicalSatClausesExpanded(prev => !prev); }}
                    style={{ cursor: 'pointer', color: '#888', fontSize: 12, userSelect: 'none' }}>
                    {cadicalSatClausesExpanded ? '▾' : '▸'} {cadicalSatResult.learnedClauses.length} learned clause{cadicalSatResult.learnedClauses.length !== 1 ? 's' : ''}
                  </span>
                  {cadicalSatClausesExpanded && <div style={{ marginLeft: 16, fontSize: 11, color: '#666', maxHeight: '8em', overflowY: 'auto' }}>
                    {cadicalSatResult.learnedClauses.map((cl, ci) => <div key={ci}>{fmtClause(cl, ast ? extractVars(ast) : [])}</div>)}
                  </div>}
                </span>}
              </span>
            : <span>CaDiCaL: unsatisfiable in {(cadicalSatResult?.elapsedSecs * 1000).toFixed(0)}ms
                {cadicalSatResult?.learnedClauses?.length > 0 && <span style={{ fontWeight: 'normal' }}>
                  <br />
                  <span onClick={e => { e.stopPropagation(); setCadicalSatClausesExpanded(prev => !prev); }}
                    style={{ cursor: 'pointer', color: '#888', fontSize: 12, userSelect: 'none' }}>
                    {cadicalSatClausesExpanded ? '▾' : '▸'} {cadicalSatResult.learnedClauses.length} learned clause{cadicalSatResult.learnedClauses.length !== 1 ? 's' : ''}
                  </span>
                  {cadicalSatClausesExpanded && <div style={{ marginLeft: 16, fontSize: 11, color: '#666', maxHeight: '8em', overflowY: 'auto' }}>
                    {cadicalSatResult.learnedClauses.map((cl, ci) => <div key={ci}>{fmtClause(cl, ast ? extractVars(ast) : [])}</div>)}
                  </div>}
                </span>}
              </span>}
        </div>
      )}

      {/* Paths through the matrix */}
      {pathsResult && (
        <div style={{
          display: 'flex', alignItems: 'flex-start', gap: 8,
          color: pathsResult.error ? '#8b0000' : pathsResult.uncoveredPaths?.length ? '#4a4a8a' : '#1a5c1a',
          background: pathsResult.error ? '#fff5f5' : '#f7f7fd',
          border: `1.5px solid ${pathsResult.error ? '#f5c2c2' : '#c8c8e8'}`,
          padding: '9px 14px', borderRadius: 6, fontSize: 13, marginBottom: 12,
        }}>
          {pathsResult.error
            ? `✗ ${pathsResult.error}`
            : <span>
                {(() => {
                  const classified = pathsResult.classifiedCount ?? 0;
                  const total = pathsResult.totalPathCount ?? 0;
                  const elapsed = pathsResult.elapsedSecs ?? 0;
                  const rate = elapsed > 0 ? Math.round(classified / elapsed) : 0;
                  const ratePart = elapsed > 0 ? ` in ${fmtTime(elapsed)} at ${fmtNum(rate)} paths/s` : '';
                  if (pathsResult.hitLimit) {
                    const pct = total > 0 ? ((classified / total) * 100).toFixed(1) : '0';
                    return `${fmtNum(classified)} of ${fmtNum(total)} paths (${pct}%) through the ${pathsResult.isComplement ? 'complement ' : ''}matrix${ratePart}`;
                  }
                  return `All ${fmtNum(total)} paths through the ${pathsResult.isComplement ? 'complement ' : ''}matrix${ratePart}`;
                })()}
                {pathsResult.uncoveredPaths.length > 0 && (() => {
                  const resName = pos => {
                    const n = resolvePosition(ast, pos)?.n ?? pos.join(',');
                    return pathsResult.isComplement ? compName(n) : n;
                  };
                  // Build a trie of uncovered paths keyed on literal positions.
                  const root = { children: new Map(), pathIndex: null, key: '', position: null };
                  (pathsResult.uncoveredPositions || []).forEach((posList, i) => {
                    let node = root;
                    let chain = '';
                    posList.forEach(pos => {
                      const k = pos.join(',');
                      chain = chain ? chain + '|' + k : k;
                      if (!node.children.has(k)) {
                        node.children.set(k, { children: new Map(), pathIndex: null, key: chain, position: pos });
                      }
                      node = node.children.get(k);
                    });
                    node.pathIndex = i;
                  });
                  const toggleExpand = key => setPathsTreeExpanded(prev => {
                    const s = new Set(prev); if (s.has(key)) s.delete(key); else s.add(key); return s;
                  });
                  const toggleSel = i => setPathsUncovSel(prev => {
                    const s = new Set(prev); if (s.has(i)) s.delete(i); else s.add(i); return s;
                  });
                  const collectIndices = node => {
                    const out = [];
                    const walk = n => {
                      if (n.pathIndex !== null) out.push(n.pathIndex);
                      n.children.forEach(walk);
                    };
                    walk(node);
                    return out;
                  };
                  // Walk down a single-child chain starting at `node`.
                  // Returns { chain: [chainNode...], end: terminalNode }
                  // where end is the first node with !=1 children or a path leaf.
                  const collapseChain = startNode => {
                    const chain = [startNode];
                    let cur = startNode;
                    while (cur.children.size === 1 && cur.pathIndex === null) {
                      cur = cur.children.values().next().value;
                      chain.push(cur);
                    }
                    return { chain, end: cur };
                  };
                  const renderNode = (node, depth) => {
                    const children = Array.from(node.children.values());
                    return children.map(child => {
                      const { chain, end } = collapseChain(child);
                      const chainKey = end.key;
                      const hasChildren = end.children.size > 0;
                      const expanded = pathsTreeExpanded.has(chainKey);
                      const isLeaf = end.pathIndex !== null && !hasChildren;
                      const subIdxs = collectIndices(end);
                      const allSel = subIdxs.length > 0 && subIdxs.every(i => pathsUncovSel.has(i));
                      const opacity = isLeaf
                        ? (pathsUncovSel.has(end.pathIndex) ? 1 : 0.35)
                        : (allSel ? 1 : 0.6);
                      return (
                        <div key={child.key} style={{ marginLeft: depth === 0 ? 0 : 14, lineHeight: 1.5 }}>
                          <span>
                            {hasChildren ? (
                              <span onClick={() => toggleExpand(chainKey)}
                                    style={{ cursor: 'pointer', userSelect: 'none', display: 'inline-block', width: 12, color: '#888' }}>
                                {expanded ? '▼' : '▶'}
                              </span>
                            ) : (
                              <span style={{ display: 'inline-block', width: 12 }} />
                            )}
                            <span
                              onClick={() => {
                                if (isLeaf) toggleSel(end.pathIndex);
                                else {
                                  setPathsUncovSel(prev => {
                                    const s = new Set(prev);
                                    if (allSel) subIdxs.forEach(i => s.delete(i));
                                    else subIdxs.forEach(i => s.add(i));
                                    return s;
                                  });
                                }
                              }}
                              style={{ cursor: 'pointer', opacity }}>
                              <b style={{ fontFamily: 'Georgia, serif' }}>
                                {chain.map((cn, ci) => <span key={ci}>{ci > 0 && ' '}<VarLabel name={resName(cn.position)} /></span>)}
                              </b>
                              {!isLeaf && (
                                <span style={{ fontWeight: 'normal', color: '#888', fontSize: 11 }}>
                                  {' '}({subIdxs.length})
                                </span>
                              )}
                            </span>
                          </span>
                          {hasChildren && expanded && renderNode(end, depth + 1)}
                        </div>
                      );
                    });
                  };
                  return (
                    <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>
                        {fmtNum(pathsResult.uncoveredPaths.length)} uncovered {pathsResult.uncoveredPaths.length === 1 ? 'path' : 'paths'}{' '}
                        <a href="#" onClick={e => { e.preventDefault();
                          // Expand all internal nodes.
                          const all = new Set();
                          const walk = n => { if (n.children.size > 0) { if (n.key) all.add(n.key); n.children.forEach(walk); } };
                          walk(root);
                          setPathsTreeExpanded(all);
                        }} style={{ fontSize: 11, color: '#888' }}>expand all</a>
                        {' '}
                        <a href="#" onClick={e => { e.preventDefault(); setPathsTreeExpanded(new Set()); }}
                           style={{ fontSize: 11, color: '#888' }}>collapse all</a>
                        :
                      </span>
                      <div style={{ marginTop: 4 }}>
                        {renderNode(root, 0)}
                      </div>
                    </span>
                  );
                })()}
                {pathsResult.coverGroups?.length > 0 && ast && (() => {
                  const resName = pos => {
                    const n = resolvePosition(ast, pos)?.n ?? pos.join(',');
                    return pathsResult.isComplement ? compName(n) : n;
                  };
                  const tooMany = (pathsResult.totalPrefixCount ?? 0) > 1000;
                  const isPartial = pathsResult.uncoveredPaths.length > 0 || pathsResult.hitLimit;
                  return <span>
                    <br />
                    <span style={{ fontWeight: 'normal' }}>
                      {fmtNum(pathsResult.coverGroups.length)} {pathsResult.coverGroups.length === 1 ? 'pair' : 'pairs'} in the {isPartial ? 'partial ' : ''}cover covering {fmtNum(pathsResult.totalPrefixCount)} {pathsResult.totalPrefixCount === 1 ? 'prefix' : 'prefixes'}{(() => {
                        const lo = Math.min(...pathsResult.coverGroups.map(g => g.prefix_length_min));
                        const hi = Math.max(...pathsResult.coverGroups.map(g => g.prefix_length_max));
                        return lo === hi ? ` ${lo} long` : ` ${lo}..${hi} long`;
                      })()}:
                      {' '}
                      <a href="#" onClick={e => { e.preventDefault(); setPathsSelected(new Set(pathsResult.coverGroups.map((_, i) => i))); }}
                         style={{ fontSize: 11, color: '#888' }}>all</a>
                      {' · '}
                      <a href="#" onClick={e => { e.preventDefault(); setPathsSelected(new Set()); }}
                         style={{ fontSize: 11, color: '#888' }}>none</a>
                      {(() => {
                        const varIndices = {};
                        pathsResult.coverGroups.forEach((g, i) => {
                          const a = resName(g.pair[0]);
                          const base = a.replace(/'$/,'');
                          (varIndices[base] ??= new Set()).add(i);
                        });
                        const vars = Object.keys(varIndices).sort();
                        return <>
                          {' · '}
                          {vars.map((v, j) => {
                            const indices = [...varIndices[v]];
                            const allOn = indices.every(i => pathsSelected.has(i));
                            return <span key={v}>
                              {j > 0 && ' '}
                              <a href="#" onClick={e => {
                                e.preventDefault();
                                setPathsSelected(prev => {
                                  const s = new Set(prev);
                                  if (allOn) indices.forEach(i => s.delete(i));
                                  else indices.forEach(i => s.add(i));
                                  return s;
                                });
                              }} style={{
                                fontSize: 11, fontFamily: 'Georgia, serif',
                                color: allOn ? '#333' : '#888',
                                fontWeight: allOn ? 'bold' : 'normal',
                              }}><VarLabel name={v} /></a>
                            </span>;
                          })}
                        </>;
                      })()}
                    </span>
                    <div style={{
                      ...(pathsResult.coverGroups.length > 6 ? { maxHeight: '9.5em', overflowY: 'auto' } : {}),
                      marginTop: 4,
                    }}>
                      {pathsResult.coverGroups.map((g, gi) => {
                        const a = resName(g.pair[0]);
                        const b = resName(g.pair[1]);
                        const isSelected = pathsSelected.has(gi);
                        const lenRange = g.prefix_length_min === g.prefix_length_max
                          ? ` ${g.prefix_length_min} long`
                          : ` ${g.prefix_length_min}..${g.prefix_length_max} long`;
                        if (tooMany || !g.prefixes?.length) {
                          return <div key={gi} style={{ fontWeight: 'normal' }}>
                            <span onClick={() => setPathsSelected(prev => {
                              const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                            })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                              <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                            </span>
                            <span style={{ color: '#888', fontSize: 11, marginLeft: 4 }}>
                              {fmtNum(g.count)} {g.count === 1 ? 'prefix' : 'prefixes'}{lenRange}
                            </span>
                          </div>;
                        }
                        const prefixes = g.prefixes.map(p => {
                          const names = p.map(pos => resName(pos));
                          return <>{'{'}{names.map((n, ni) => <span key={ni}>{ni > 0 && ', '}<VarLabel name={n} /></span>)}{'}' }</>;
                        });
                        const expanded = pathsExpanded.has(gi);
                        return <div key={gi} style={{ fontWeight: 'normal' }}>
                          <span onClick={() => setPathsSelected(prev => {
                            const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                          })} style={{ cursor: 'pointer', opacity: isSelected ? 1 : 0.35 }}>
                            <b style={{ fontFamily: 'Georgia, serif' }}>{'{'}<VarLabel name={a} />{', '}<VarLabel name={b} />{'}'}</b>
                          </span>
                          {prefixes.length > 0 && <>
                            <span onClick={e => { e.stopPropagation(); setPathsExpanded(prev => {
                              const s = new Set(prev); if (s.has(gi)) s.delete(gi); else s.add(gi); return s;
                            }); }}
                              style={{ cursor: 'pointer', color: '#888', fontSize: 11, marginLeft: 4, userSelect: 'none' }}
                              title={expanded ? 'Collapse covered paths' : 'Expand covered paths'}
                            >{expanded ? '▾' : '▸'} {prefixes.length} {prefixes.length === 1 ? 'prefix' : 'prefixes'}{lenRange}</span>
                            {expanded && <div style={{ marginLeft: 16, fontSize: 12, color: '#666' }}>
                              {prefixes.map((p, pi) => <div key={pi}>{p}</div>)}
                            </div>}
                          </>}
                        </div>;
                      })}
                    </div>
                  </span>;
                })()}
              </span>}
        </div>
      )}



        </>
      )}

      <style>{`@keyframes fadeIn { from { opacity: 0; transform: translateY(-4px); } to { opacity: 1; transform: translateY(0); } } @keyframes logic-spin { to { transform: rotate(360deg); } }`}</style>
    </div>
  );
}
