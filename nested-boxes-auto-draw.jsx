import { useState, useEffect, useRef } from "react";

// ─── Tokenizer ────────────────────────────────────────────────────────────────
function tokenize(str) {
  const tokens = [];
  let i = 0;
  while (i < str.length) {
    const ch = str[i];
    if (/\s/.test(ch)) { i++; continue; }
    if (ch === '(')              { tokens.push('('); i++; }
    else if (ch === ')')         { tokens.push(')'); i++; }
    else if (ch === '+')         { tokens.push('+'); i++; }
    else if ('·*.⋅'.includes(ch)){ tokens.push('·'); i++; }
    else if (/[A-Za-z0-9]/.test(ch)) {
      let name = ch; i++;
      while (i < str.length && str[i] === "'") { name += "'"; i++; }
      tokens.push({ v: name });
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
    while (peek() === '·') {
      eat();
      if (peek() === undefined) throw new Error("Expected factor after '·'");
      const right = parseFactor();
      left = left.t === 'AND'
        ? { t: 'AND', c: [...left.c, right] }
        : { t: 'AND', c: [left, right] };
    }
    return left;
  }

  function parseFactor() {
    const t = peek();
    if (t === undefined) throw new Error("Unexpected end of formula");
    if (t === ')') throw new Error("Unexpected ')'");
    if (t === '+') throw new Error("Unexpected '+' — did you forget a left operand?");
    if (t === '·') throw new Error("Unexpected '·' — did you forget a left operand?");
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

// ─── Box Renderer ─────────────────────────────────────────────────────────────
const PAD  = 10;
const GAP  =  8;
const BORDER_COLORS = ['#111', '#1a6bcc', '#b35000', '#2a7a2a', '#7a1a7a'];

function BoxNode({ node, depth = 0 }) {
  if (!node) return null;

  if (node.t === 'VAR') {
    return (
      <div style={{
        minWidth: 26,
        display: 'flex',
        alignItems: 'center',
        justifyContent: 'center',
        padding: '4px 6px',
        fontSize: 17,
        fontFamily: 'Georgia, serif',
        fontWeight: 'bold',
        lineHeight: 1,
        userSelect: 'none',
      }}>
        {node.n}
      </div>
    );
  }

  const isOR  = node.t === 'OR';
  const color = BORDER_COLORS[depth % BORDER_COLORS.length];

  return (
    <div style={{
      border: `2px solid ${color}`,
      borderRadius: 3,
      padding: PAD,
      display: 'inline-flex',
      flexDirection: isOR ? 'row' : 'column',
      alignItems: 'center',
      justifyContent: 'center',
      gap: GAP,
      boxSizing: 'border-box',
    }}>
      {node.c.map((child, i) => (
        <BoxNode key={i} node={child} depth={depth + 1} />
      ))}
    </div>
  );
}

// ─── Legend ───────────────────────────────────────────────────────────────────
function Legend() {
  const boxBase = {
    display: 'inline-flex', border: '2px solid', padding: '2px 8px',
    gap: 4, verticalAlign: 'middle', fontSize: 13, fontFamily: 'Georgia, serif',
    fontWeight: 'bold', borderRadius: 2,
  };
  return (
    <div style={{
      display: 'flex', gap: 24, flexWrap: 'wrap',
      fontSize: 13, color: '#444', marginBottom: 18,
      background: '#f0f4ff', padding: '10px 16px', borderRadius: 6,
    }}>
      <span style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
        <b>AND (·)</b> →
        <span style={{ ...boxBase, borderColor: '#111', flexDirection: 'column' }}>
          <span>A</span><span>B</span>
        </span>
        <span style={{ color: '#666' }}>stacked vertically</span>
      </span>
      <span style={{ display: 'flex', alignItems: 'center', gap: 8 }}>
        <b>OR (+)</b> →
        <span style={{ ...boxBase, borderColor: '#1a6bcc', flexDirection: 'row' }}>
          <span>A</span><span>B</span>
        </span>
        <span style={{ color: '#666' }}>side by side</span>
      </span>
    </div>
  );
}

// ─── Examples ─────────────────────────────────────────────────────────────────
const EXAMPLES = [
  { label: "From image",    f: "((A·B) + (A'+B')) · ((A'+B') + (A·B))" },
  { label: "Simple AND",    f: "A · B · C" },
  { label: "Simple OR",     f: "A + B + C" },
  { label: "Mixed",         f: "(A·B) + (C·D)" },
  { label: "XOR-like",      f: "(A·B') + (A'·B)" },
  { label: "Distributive",  f: "A · (B + C)" },
  { label: "De Morgan",     f: "(A'+B') · (A+B)" },
];

// ─── Main App ─────────────────────────────────────────────────────────────────
export default function App() {
  const [input,  setInput]  = useState(EXAMPLES[0].f);
  const [ast,    setAst]    = useState(null);
  const [error,  setError]  = useState('');
  const inputRef = useRef(null);

  // Live draw: re-parse on every keystroke
  useEffect(() => {
    try {
      setAst(parse(input));
      setError('');
    } catch (e) {
      setError(e.message);
      // Keep old diagram visible while user is mid-edit
    }
  }, [input]);

  // Insert special chars at cursor position
  const insertAt = (char) => {
    const el = inputRef.current;
    if (!el) return;
    const s = el.selectionStart, e = el.selectionEnd;
    const next = input.slice(0, s) + char + input.slice(e);
    setInput(next);
    setTimeout(() => { el.selectionStart = el.selectionEnd = s + char.length; el.focus(); }, 0);
  };

  const btnStyle = (bg = '#333') => ({
    padding: '9px 14px', background: bg, color: 'white',
    border: 'none', borderRadius: 5, cursor: 'pointer',
    fontSize: 15, fontFamily: 'Georgia, serif', fontWeight: 'bold',
    minWidth: 38, flexShrink: 0,
  });

  return (
    <div style={{
      fontFamily: 'system-ui, sans-serif',
      padding: 28,
      maxWidth: 900,
      margin: '0 auto',
      background: '#fff',
      minHeight: '100vh',
    }}>
      {/* Header */}
      <h2 style={{ margin: '0 0 4px', fontSize: 22, color: '#111' }}>
        Boolean Formula → Nested Box Diagram
      </h2>
      <p style={{ margin: '0 0 18px', color: '#666', fontSize: 13 }}>
        Diagram updates live as you type.
      </p>

      <Legend />

      {/* Input row */}
      <div style={{ display: 'flex', gap: 8, marginBottom: 8, flexWrap: 'wrap' }}>
        <input
          ref={inputRef}
          value={input}
          onChange={e => setInput(e.target.value)}
          style={{
            flex: '1 1 400px',
            padding: '9px 13px',
            fontSize: 15,
            fontFamily: 'Georgia, serif',
            border: `1.5px solid ${error ? '#c00' : '#bbb'}`,
            borderRadius: 5,
            outline: 'none',
            transition: 'border-color 0.2s',
          }}
          placeholder="Type a formula, e.g. (A·B) + (A'+B')"
          spellCheck={false}
          autoFocus
        />
        <button onClick={() => insertAt('·')}  title="Insert AND (·)" style={btnStyle('#555')}>·</button>
        <button onClick={() => insertAt("'")}  title="Insert complement (')" style={btnStyle('#555')}>'</button>
        <button onClick={() => setInput('')}    title="Clear" style={btnStyle('#a00')}>✕</button>
      </div>

      {/* Tip */}
      <div style={{ fontSize: 12, color: '#888', marginBottom: 12 }}>
        <code>·</code> or <code>*</code> = AND &nbsp;·&nbsp; <code>+</code> = OR &nbsp;·&nbsp;
        <code>'</code> after a variable = complement &nbsp;·&nbsp; parentheses for grouping
      </div>

      {/* Error message box */}
      <div style={{
        height: error ? 'auto' : 0,
        overflow: 'hidden',
        transition: 'height 0.2s',
        marginBottom: error ? 14 : 0,
      }}>
        {error && (
          <div style={{
            display: 'flex', alignItems: 'flex-start', gap: 10,
            color: '#8b0000', background: '#fff5f5',
            border: '1.5px solid #f5c2c2',
            padding: '10px 14px', borderRadius: 6, fontSize: 13,
          }}>
            <span style={{ fontSize: 16, lineHeight: 1.3 }}>⚠</span>
            <div>
              <b>Syntax error</b><br />
              {error}
            </div>
          </div>
        )}
      </div>

      {/* Examples */}
      <div style={{ display: 'flex', gap: 6, flexWrap: 'wrap', marginBottom: 24 }}>
        <span style={{ fontSize: 12, color: '#888', alignSelf: 'center', marginRight: 4 }}>Examples:</span>
        {EXAMPLES.map(({ label, f }) => (
          <button
            key={f}
            onClick={() => setInput(f)}
            style={{
              padding: '4px 11px', fontSize: 12, fontFamily: 'Georgia, serif',
              border: '1px solid #ccc', borderRadius: 4, cursor: 'pointer',
              background: input === f ? '#e8eeff' : '#fafafa',
              color: '#333',
            }}
          >
            {label}
          </button>
        ))}
      </div>

      {/* Diagram — stays visible even when there's a transient error */}
      {ast && (
        <>
          <div style={{ fontSize: 12, color: '#888', marginBottom: 10 }}>
            Diagram{error ? ' (showing last valid formula)' : ''} — border colors indicate nesting depth:
          </div>
          <div style={{
            background: '#f8f9fc',
            border: '1px solid #dde',
            borderRadius: 8,
            padding: 28,
            display: 'inline-block',
            minWidth: '100%',
            boxSizing: 'border-box',
            opacity: error ? 0.55 : 1,
            transition: 'opacity 0.15s',
          }}>
            <BoxNode node={ast} depth={0} />
          </div>
        </>
      )}
    </div>
  );
}
