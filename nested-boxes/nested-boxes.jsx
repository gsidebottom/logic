import { useState, useEffect, useLayoutEffect, useRef, createContext, useContext, useMemo } from "react";

// ─── Tokenizer ────────────────────────────────────────────────────────────────
function tokenize(str) {
  const tokens = [];
  let i = 0;
  while (i < str.length) {
    const ch = str[i];
    if (/\s/.test(ch)) { i++; continue; }
    if (ch === '(')               { tokens.push('('); i++; }
    else if (ch === ')')          { tokens.push(')'); i++; }
    else if (ch === '+')          { tokens.push('+'); i++; }
    else if ('·*.⋅'.includes(ch)) { tokens.push('·'); i++; }
    else if (/[A-Za-z]/.test(ch)) {
      let name = ch; i++;
      while (i < str.length && /[A-Za-z0-9_]/.test(str[i])) { name += str[i]; i++; }
      while (i < str.length && /\s/.test(str[i])) { i++; }
      while (i < str.length && str[i] === "'") { name += "'"; i++; }
      tokens.push({ v: name });
    } else if (ch === '0' || ch === '1') {
      let name = ch; i++;
      while (i < str.length && /\s/.test(str[i])) { i++; }
      while (i < str.length && str[i] === "'") { name += "'"; i++; }
      tokens.push({ v: name });
    } else if (/[0-9]/.test(ch)) {
      throw new Error(`Variable names cannot start with a digit: '${ch}'`);
    } else if (ch === "'") {
      throw new Error("Unexpected ' — complement must follow a variable name");
    } else { i++; }
  }
  return tokens;
}

// ─── Recursive Descent Parser ─────────────────────────────────────────────────
// expr   := term ('+' term)*
// term   := factor ('·' factor)*
// factor := '(' expr ')' | VAR
function parse(str) {
  if (!str.trim()) throw new Error("Formula is empty");
  const tokens = tokenize(str);
  let pos = 0;
  const peek = () => tokens[pos];
  const eat  = () => tokens[pos++];

  function parseExpr() {
    let left = parseTerm();
    while (peek() === '+') {
      eat();
      if (peek() === undefined) throw new Error("Expected term after '+'");
      const right = parseTerm();
      left = left.t === 'OR'
        ? { t: 'OR',  c: [...left.c, right] }
        : { t: 'OR',  c: [left, right] };
    }
    return left;
  }

  function parseTerm() {
    let left = parseFactor();
    while (true) {
      const t = peek();
      if (t === '·') { eat(); }                                    // explicit ·
      else if (t !== undefined && (typeof t === 'object' || t === '(')) {} // implicit AND
      else break;
      const right = parseFactor();
      left = left.t === 'AND'
        ? { t: 'AND', c: [...left.c, right] }
        : { t: 'AND', c: [left, right] };
    }
    return left;
  }

  function parseFactor() {
    const t = peek();
    if (t === undefined)  throw new Error("Unexpected end of formula");
    if (t === ')')        throw new Error("Unexpected ')'");
    if (t === '+')        throw new Error("Unexpected '+' — missing left operand?");
    if (t === '·')        throw new Error("Unexpected '·' — missing left operand?");
    if (t === '(') {
      eat();
      const expr = parseExpr();
      if (peek() !== ')') throw new Error("Missing closing ')'");
      eat();
      return expr;
    }
    if (typeof t === 'object') { eat(); return { t: 'VAR', n: t.v }; }
    throw new Error(`Unexpected token: ${JSON.stringify(t)}`);
  }

  const result = parseExpr();
  if (pos < tokens.length) {
    const leftover = tokens[pos];
    throw new Error(
      `Unexpected ${leftover === ')' ? "')'" : `'${leftover?.v ?? leftover}'`} — extra content after formula`
    );
  }
  return result;
}

// ─── Complement & display helpers ─────────────────────────────────────────────

function complementAst(node) {
  if (node.t === 'VAR') {
    const n = node.n.endsWith("'") ? node.n.slice(0, -1) : node.n + "'";
    return { t: 'VAR', n };
  }
  if (node.t === 'AND') return { t: 'OR',  c: node.c.map(complementAst) };
  if (node.t === 'OR')  return { t: 'AND', c: node.c.map(complementAst) };
  return node;
}

function astToString(node) {
  if (node.t === 'VAR') return node.n;
  if (node.t === 'AND') return node.c.map(c =>
    c.t === 'OR' ? `(${astToString(c)})` : astToString(c)
  ).join('·');
  if (node.t === 'OR')  return node.c.map(c =>
    c.t === 'AND' ? astToString(c) : astToString(c)
  ).join(' + ');
  return '';
}

// ─── Cover context (for highlighting complementary pairs in diagrams) ──────────
const CoverContext = createContext(null);

const PAIR_COLORS = ['#e63946', '#1d7cc4', '#2a9d8f', '#e07c00', '#8e44ad', '#555'];

function parseCoveringPairs(pairs) {
  // Each pair string looks like "{A, A'}" — extract the two names
  return pairs.map(p => {
    const inner = p.replace(/^\{|\}$/g, '');
    return inner.split(',').map(s => s.trim());
  });
}

// ─── Box Renderer ─────────────────────────────────────────────────────────────
const PAD = 10, GAP = 8;
const BORDER_COLORS = ['#111', '#1a6bcc', '#b35000', '#2a7a2a', '#7a1a7a'];

function BoxNode({ node, depth = 0 }) {
  const cover = useContext(CoverContext);
  if (!node) return null;

  if (node.t === 'VAR') {
    const pairIdx = cover?.varToPairIdx?.[node.n];
    const highlighted = pairIdx !== undefined;
    const hColor = highlighted ? PAIR_COLORS[pairIdx % PAIR_COLORS.length] : null;
    return (
      <div
        data-var={node.n}
        style={{
          minWidth: 26, display: 'flex', alignItems: 'center',
          justifyContent: 'center', padding: '4px 6px',
          fontSize: 17, fontFamily: 'Georgia, serif',
          fontWeight: 'bold', lineHeight: 1, userSelect: 'none',
          ...(highlighted ? {
            background: hColor + '28',
            borderRadius: 3,
            outline: `2.5px solid ${hColor}`,
            outlineOffset: 1,
          } : {}),
        }}
      >
        {node.n}
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
    }}>
      {node.c.map((child, i) => <BoxNode key={i} node={child} depth={depth + 1} />)}
    </div>
  );
}

// ─── Diagram with SVG arc connections for covering pairs ──────────────────────
function DiagramWithConnections({ node, coveringPairs }) {
  const containerRef = useRef(null);
  const [arcs, setArcs] = useState([]);

  const parsed = useMemo(
    () => (coveringPairs?.length ? parseCoveringPairs(coveringPairs) : []),
    [coveringPairs]
  );

  const varToPairIdx = useMemo(() => {
    const m = {};
    parsed.forEach((pair, i) => pair.forEach(v => { m[v] = i; }));
    return m;
  }, [parsed]);

  // Recompute arc positions after every render (DOM may have changed)
  useLayoutEffect(() => {
    if (!containerRef.current || !parsed.length) {
      // Use functional update to avoid re-rendering when already empty
      setArcs(prev => prev.length === 0 ? prev : []);
      return;
    }
    const container = containerRef.current;
    const cr = container.getBoundingClientRect();
    const newArcs = [];
    parsed.forEach((pair, pairIdx) => {
      if (pair.length !== 2) return;
      const [a, b] = pair;
      const da = container.querySelector(`[data-var="${a}"]`);
      const db = container.querySelector(`[data-var="${b}"]`);
      if (!da || !db) return;
      const ra = da.getBoundingClientRect();
      const rb = db.getBoundingClientRect();
      newArcs.push({
        x1: ra.left + ra.width / 2 - cr.left,
        y1: ra.top + ra.height / 2 - cr.top,
        x2: rb.left + rb.width / 2 - cr.left,
        y2: rb.top + rb.height / 2 - cr.top,
        pairIdx,
      });
    });
    setArcs(prev => JSON.stringify(prev) === JSON.stringify(newArcs) ? prev : newArcs);
  });

  return (
    <CoverContext.Provider value={parsed.length ? { varToPairIdx } : null}>
      <div ref={containerRef} style={{ position: 'relative', display: 'inline-block' }}>
        <BoxNode node={node} depth={0} />
        {arcs.length > 0 && (
          <svg style={{
            position: 'absolute', top: 0, left: 0,
            width: '100%', height: '100%',
            pointerEvents: 'none', overflow: 'visible',
          }}>
            {arcs.map((arc, i) => {
              const mx = (arc.x1 + arc.x2) / 2;
              const miny = Math.min(arc.y1, arc.y2);
              const dx = arc.x2 - arc.x1, dy = arc.y2 - arc.y1;
              const dist = Math.sqrt(dx * dx + dy * dy) || 1;
              const voff = Math.max(28, dist * 0.4);
              // Control point: above both endpoints
              const qcx = mx;
              const qcy = miny - voff;
              const color = PAIR_COLORS[arc.pairIdx % PAIR_COLORS.length];
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
];

// ─── Main App ─────────────────────────────────────────────────────────────────
export default function App() {
  const [input,         setInput]         = useState(EXAMPLES[0].f);
  const [ast,           setAst]           = useState(null);
  const [error,         setError]         = useState('');
  const [simplified,    setSimplified]    = useState(null); // {formula, ast}
  const [simplifyMsg,   setSimplifyMsg]   = useState(null); // {text, ok}
  const [complementData, setComplementData] = useState(null); // {formula, ast}
  const [validResult,   setValidResult]   = useState(null); // {valid, path}
  const [satResult,     setSatResult]     = useState(null); // {satisfiable, path, coveringPairs}
  const [loading,       setLoading]       = useState(false);
  const inputRef = useRef(null);

  // Live redraw on every keystroke; clear simplified result when input changes
  useEffect(() => {
    try {
      setAst(parse(input));
      setError('');
    } catch (e) {
      setError(e.message);
    }
    setSimplified(null);
    setComplementData(null);
    setValidResult(null);
    setSatResult(null);
  }, [input]);

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

  const handleComplement = () => {
    if (!ast) return;
    const cAst = complementAst(ast);
    setComplementData({ formula: astToString(cAst), ast: cAst });
  };

  const handleValid = async () => {
    setLoading(true);
    try {
      const res  = await fetch('http://localhost:3001/valid', {
        method: 'POST', headers: { 'Content-Type': 'application/json' },
        body: JSON.stringify({ formula: input }),
      });
      const data = await res.json();
      if (data.error) setValidResult({ error: data.error });
      else            setValidResult({ valid: data.valid, path: data.path, coveringPairs: data.covering_pairs });
    } catch (e) {
      setValidResult({ error: 'Could not reach Rust service' });
    }
    setLoading(false);
  };

  const handleSatisfiable = async () => {
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
        setSatResult({ satisfiable: data.satisfiable, path: data.path, coveringPairs: data.covering_pairs });
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

      {/* Input row */}
      <div style={{ display: 'flex', gap: 8, marginBottom: 8, flexWrap: 'wrap' }}>
        <input
          ref={inputRef}
          value={input}
          onChange={e => setInput(e.target.value)}
          style={{
            flex: '1 1 380px', padding: '9px 13px', fontSize: 15,
            fontFamily: 'Georgia, serif',
            border: `1.5px solid ${error ? '#c00' : '#bbb'}`,
            borderRadius: 5, outline: 'none', transition: 'border-color 0.2s',
          }}
          placeholder="Type a formula, e.g. (A·B) + (A'+B')"
          spellCheck={false}
          autoFocus
        />
        {btn('·',   () => insertAt('·'),   '#555', false, "Insert AND (·)")}
        {btn("'",   () => insertAt("'"),   '#555', false, "Insert complement (')")}
        {btn('✕',   () => setInput(''),    '#a00', false, "Clear")}
        {btn('⚡ Simplify',    handleSimplify,    '#1a6bcc', !ast || loading, !ast ? "Fix syntax errors first" : "Simplify to minimal SOP")}
        {btn('✓ Valid?',       handleValid,       '#6a2a9a', !ast || loading, !ast ? "Fix syntax errors first" : "Check if formula is a tautology")}
        {btn('? Satisfiable?', handleSatisfiable, '#7a4a00', !ast || loading, !ast ? "Fix syntax errors first" : "Check if formula has a satisfying assignment")}
        {btn("A'  Complement", handleComplement,  '#2a6a6a', !ast,            !ast ? "Fix syntax errors first" : "Show the complement as a nested box diagram")}
      </div>

      {/* Tip */}
      <div style={{ fontSize: 12, color: '#888', marginBottom: 10 }}>
        <code>·</code> or <code>*</code> = AND &nbsp;·&nbsp; <code>+</code> = OR &nbsp;·&nbsp;
        <code>'</code> after variable = complement &nbsp;·&nbsp; parentheses for grouping
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
                  ✓ Valid — tautology (all paths are complementary)
                  {validResult.coveringPairs?.length > 0 && (
                    <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>Covering complementary pairs: </span>
                      <b style={{ fontFamily: 'Georgia, serif' }}>
                        {validResult.coveringPairs.join(',  ')}
                      </b>
                    </span>
                  )}
                </span>
              : <span>✗ Not valid — uncomplimentary path: <b style={{ fontFamily: 'Georgia, serif' }}>{validResult.path}</b></span>}
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
              ? <span>✓ Satisfiable — uncomplimentary path in complement: <b style={{ fontFamily: 'Georgia, serif' }}>{satResult.path}</b></span>
              : <span>
                  ✗ Unsatisfiable — complement is a tautology (all paths are complementary)
                  {satResult.coveringPairs?.length > 0 && (
                    <span>
                      <br />
                      <span style={{ fontWeight: 'normal' }}>Covering complementary pairs: </span>
                      <b style={{ fontFamily: 'Georgia, serif' }}>
                        {satResult.coveringPairs.join(',  ')}
                      </b>
                    </span>
                  )}
                </span>}
        </div>
      )}

      {/* Examples */}
      <div style={{ display: 'flex', gap: 6, flexWrap: 'wrap', marginBottom: 24 }}>
        <span style={{ fontSize: 12, color: '#888', alignSelf: 'center', marginRight: 4 }}>Examples:</span>
        {EXAMPLES.map(({ label, f }) => (
          <button key={f} onClick={() => setInput(f)} style={{
            padding: '4px 11px', fontSize: 12, fontFamily: 'Georgia, serif',
            border: '1px solid #ccc', borderRadius: 4, cursor: 'pointer',
            background: input === f ? '#e8eeff' : '#fafafa', color: '#333',
          }}>
            {label}
          </button>
        ))}
      </div>

      {/* Diagrams */}
      {ast && (
        <>
          <div style={{ fontSize: 12, color: '#888', marginBottom: 10 }}>
            {simplified ? 'Original' : 'Diagram'}{error ? ' (last valid formula)' : ''} — border colors show nesting depth:
          </div>
          <div style={{
            background: '#f8f9fc', border: '1px solid #dde', borderRadius: 8,
            padding: 28, display: 'flex', justifyContent: 'center', alignItems: 'center',
            boxSizing: 'border-box', opacity: error ? 0.5 : 1, transition: 'opacity 0.15s',
          }}>
            <DiagramWithConnections
              node={ast}
              coveringPairs={validResult?.valid ? validResult.coveringPairs : null}
            />
          </div>

          {simplified && (
            <>
              <div style={{ fontSize: 12, color: '#888', marginTop: 20, marginBottom: 10 }}>
                Simplified — <span style={{ fontFamily: 'Georgia, serif' }}>{simplified.formula}</span>
              </div>
              <div style={{
                background: '#f0fff4', border: '1px solid #b2e0b2', borderRadius: 8,
                padding: 28, display: 'flex', justifyContent: 'center', alignItems: 'center',
                boxSizing: 'border-box',
              }}>
                <DiagramWithConnections node={simplified.ast} coveringPairs={null} />
              </div>
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
              <div style={{
                background: '#f0fafa', border: '1px solid #a0d4d4', borderRadius: 8,
                padding: 28, display: 'flex', justifyContent: 'center', alignItems: 'center',
                boxSizing: 'border-box',
              }}>
                <DiagramWithConnections
                  node={complementData.ast}
                  coveringPairs={satResult && !satResult.satisfiable ? satResult.coveringPairs : null}
                />
              </div>
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
