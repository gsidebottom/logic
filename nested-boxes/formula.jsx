// ─── Tokenizer ────────────────────────────────────────────────────────────────
export function tokenize(str) {
  const tokens = [];
  let i = 0;
  while (i < str.length) {
    const ch = str[i];
    if (/\s/.test(ch)) { i++; continue; }
    if (ch === '(')               { tokens.push('('); i++; }
    else if (ch === ')')          { tokens.push(')'); i++; }
    else if (ch === '+')          { tokens.push('+'); i++; }
    else if ('·*.⋅'.includes(ch)) { tokens.push('·'); i++; }
    else if (ch === '⇒')                          { tokens.push('⇒'); i++; }
    else if ('⇔⊙'.includes(ch) || ch === '=')    { tokens.push('⇔'); i++; }
    else if ('⊕≠'.includes(ch))                   { tokens.push('⊕'); i++; }
    else if (/[A-Za-z]/.test(ch)) {
      let name = ch; i++;
      while (i < str.length && /[A-Za-z0-9_,]/.test(str[i])) { name += str[i]; i++; }
      while (i < str.length && /\s/.test(str[i])) { i++; }
      let primes = 0;
      while (i < str.length && str[i] === "'") { primes++; i++; }
      tokens.push({ v: name + (primes % 2 ? "'" : "") });
    } else if (ch === '0' || ch === '1') {
      let name = ch; i++;
      while (i < str.length && /\s/.test(str[i])) { i++; }
      let primes = 0;
      while (i < str.length && str[i] === "'") { primes++; i++; }
      tokens.push({ v: name + (primes % 2 ? "'" : "") });
    } else if (/[0-9]/.test(ch)) {
      throw new Error(`Variable names cannot start with a digit: '${ch}'`);
    } else if (ch === "'") { tokens.push("'"); i++;
    } else { i++; }
  }
  return tokens;
}

// ─── Recursive Descent Parser ─────────────────────────────────────────────────
// Precedence (loosest to tightest, all right-associative):
//   ⇒  ⊕  =  +  ·  '
// impl   := xor   ('⇒' impl)?         x⇒y  = x' + y
// xor    := equiv ('⊕' xor)?          x⊕y  = x·y' + x'·y
// equiv  := expr  ('⇔' equiv)?        x⇔y  = x·y + x'·y'
// expr   := term  ('+' term)*
// term   := factor ('·' factor)*
// factor := '(' impl ')' "'"* | VAR
export function parse(str) {
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
      const lc = left.t  === 'OR' ? left.c  : [left];
      const rc = right.t === 'OR' ? right.c : [right];
      left = { t: 'OR', c: [...lc, ...rc] };
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
      const lc = left.t  === 'AND' ? left.c  : [left];
      const rc = right.t === 'AND' ? right.c : [right];
      left = { t: 'AND', c: [...lc, ...rc] };
    }
    return left;
  }

  function parseEquiv() {
    const left = parseExpr();
    if (peek() !== '⇔') return left;
    eat();
    const right = parseEquiv(); // right-associative
    return { t: 'OR', c: [
      { t: 'AND', c: [left,                right               ] },
      { t: 'AND', c: [complementAst(left),  complementAst(right)] },
    ]};
  }

  function parseXor() {
    const left = parseEquiv();
    if (peek() !== '⊕') return left;
    eat();
    const right = parseXor(); // right-associative
    return { t: 'OR', c: [
      { t: 'AND', c: [left,                complementAst(right)] },
      { t: 'AND', c: [complementAst(left),  right              ] },
    ]};
  }

  function parseImpl() {
    const left = parseXor();
    if (peek() !== '⇒') return left;
    eat();
    const right = parseImpl(); // right-associative
    return { t: 'OR', c: [complementAst(left), right] };
  }

  function parseFactor() {
    const t = peek();
    if (t === undefined)  throw new Error("Unexpected end of formula");
    if (t === ')')        throw new Error("Unexpected ')'");
    if (t === '+')        throw new Error("Unexpected '+' — missing left operand?");
    if (t === '·')        throw new Error("Unexpected '·' — missing left operand?");
    if (t === "'") throw new Error("Unexpected ' — complement must follow a variable or closing ')'");
    if (t === '⇒' || t === '⇔' || t === '⊕') throw new Error(`Unexpected '${t}' — missing left operand`);
    if (t === '(') {
      eat();
      const expr = parseImpl();
      if (peek() !== ')') throw new Error("Missing closing ')'");
      eat();
      // Apply any trailing complement operators, pushing negation inward (De Morgan)
      let result = expr;
      while (peek() === "'") { eat(); result = complementAst(result); }
      return result;
    }
    if (typeof t === 'object') { eat(); return { t: 'VAR', n: t.v }; }
    throw new Error(`Unexpected token: ${JSON.stringify(t)}`);
  }

  const result = parseImpl();
  if (pos < tokens.length) {
    const leftover = tokens[pos];
    throw new Error(
      `Unexpected ${leftover === ')' ? "')'" : `'${leftover?.v ?? leftover}'`} — extra content after formula`
    );
  }
  return result;
}

// ─── Complement & display helpers ─────────────────────────────────────────────

export function complementAst(node) {
  if (node.t === 'VAR') {
    const n = node.n.endsWith("'") ? node.n.slice(0, -1) : node.n + "'";
    return { t: 'VAR', n };
  }
  if (node.t === 'AND') return { t: 'OR',  c: node.c.map(complementAst) };
  if (node.t === 'OR')  return { t: 'AND', c: node.c.map(complementAst) };
  return node;
}

export function astToString(node) {
  if (node.t === 'VAR') return node.n;
  if (node.t === 'AND') return node.c.map(c =>
    c.t === 'OR' ? `(${astToString(c)})` : astToString(c)
  ).join('·');
  if (node.t === 'OR')  return node.c.map(c =>
    c.t === 'AND' ? astToString(c) : astToString(c)
  ).join(' + ');
  return '';
}

// pairs is [[posA, posB], ...] where posA/posB are index arrays from the server.
export function parseCoveringPairs(pairs) {
  return pairs; // already parsed by JSON.parse; each element is [posA, posB]
}

// Walk ast by position (array of child indices); returns the node or null.
export function resolvePosition(ast, pos) {
  let node = ast;
  for (const i of pos) {
    if (!node?.c) return null;
    node = node.c[i];
  }
  return node;
}

// ─── Variable label with subscript support ────────────────────────────────────
// Renders "x_1'" as x<sub>1</sub>' (splits on first underscore).
export function VarLabel({ name }) {
  const primes = name.match(/'+$/)?.[0] ?? '';
  const base   = name.slice(0, name.length - primes.length);
  const uscore = base.indexOf('_');
  if (uscore === -1) return <>{name}</>;
  return <>{base.slice(0, uscore)}<span style={{ fontSize: '0.55em', position: 'relative', top: '0.5em' }}>{base.slice(uscore + 1)}</span>{primes}</>;
}

// ─── Box calls ─────────────────────────────────────────────────────────────────
// `name(a1, a2, …)` (or `name(a1; a2; …)`) refers to a compiled box (see
// doc/box_backend_design.md §5.2).  Expansion substitutes the arguments for the
// box's parameters in its definition, renames its projected internals per call
// site, and recurses — the server does exactly the same (logic::boxes::expand),
// so the diagram and the backends agree.  Unknown box / wrong arity ⇒ error.
// `name(` is a call when the parenthesised text is an argument list and the
// name is a known box, or there are ≥2 arguments (or none, or `;`); `A(B+C)`
// and `A(B)` stay ANDs.  In an argument list a comma continues a name only
// inside a numeric subscript (`d_0,1`); elsewhere it separates arguments.
const isNameChar = c => /[\p{L}\p{N}_,]/u.test(c);
function readName(str, i, inArgs) {
  let name = '', inSub = false;
  while (i < str.length) {
    const c = str[i];
    if (c === '_') inSub = true;
    else if (c === ',') { if (inArgs && !(inSub && /[0-9]/.test(str[i + 1] ?? ''))) break; }
    else if (!/[\p{L}\p{N}]/u.test(c)) break;
    name += c; i++;
  }
  return [name, i];
}
function parseArgs(str, i) {           // str[i] === '('
  i++;
  const args = []; let semi = false;
  for (;;) {
    while (i < str.length && /\s/.test(str[i])) i++;
    if (i >= str.length) return null;
    if (str[i] === ')') return args.length === 0 ? [args, i + 1, semi] : null;
    let name;
    if (/[A-Za-z]/.test(str[i])) { [name, i] = readName(str, i, true); }
    else if (str[i] === '0' || str[i] === '1') { name = str[i]; i++; }
    else return null;
    let k = i; while (k < str.length && /\s/.test(str[k])) k++;
    let primes = 0; while (k < str.length && str[k] === "'") { primes++; k++; }
    if (primes > 0) { i = k; if (primes % 2 === 1) name += "'"; }
    args.push(name);
    while (i < str.length && /\s/.test(str[i])) i++;
    if (i >= str.length) return null;
    if (str[i] === ')') return [args, i + 1, semi];
    if (str[i] === ',') i++;
    else if (str[i] === ';') { semi = true; i++; }
    else return null;
  }
}
function substitute(sig, args, k) {
  const map = new Map(sig.params.map((p, j) => [p, args[j]]));
  for (const v of sig.internals) if (!map.has(v)) map.set(v, `${v}__${k}`);
  let out = '', i = 0;
  const f = sig.formula;
  while (i < f.length) {
    const prevIsName = i > 0 && (isNameChar(f[i - 1]) || f[i - 1] === "'");
    if (/[A-Za-z]/.test(f[i]) && !prevIsName) { const [name, j] = readName(f, i, false); out += map.get(name) ?? name; i = j; }
    else { out += f[i]; i++; }
  }
  return out;
}
function expandRec(text, lookup, counter, depth) {
  if (depth > 16) throw new Error('box expansion nested more than 16 levels — is a box defined in terms of itself?');
  let out = '', i = 0;
  while (i < text.length) {
    const prevIsName = i > 0 && (isNameChar(text[i - 1]) || text[i - 1] === "'");
    if (/[A-Za-z]/.test(text[i]) && !prevIsName) {
      const [name, j] = readName(text, i, false);
      if (text[j] === '(') {
        const parsed = parseArgs(text, j);
        if (parsed) {
          const [args, after, semi] = parsed;
          const sig = lookup(name);
          if (sig || args.length !== 1 || semi) {
            if (!sig) throw new Error(`unknown box \`${name}\` — load and compile its library (jq panel), or check the spelling`);
            if (args.length !== sig.params.length)
              throw new Error(`box \`${name}\` expects ${sig.params.length} argument${sig.params.length === 1 ? '' : 's'} (${sig.params.join('; ')}), got ${args.length}`);
            counter.n++;
            out += '(' + expandRec(substitute(sig, args, counter.n), lookup, counter, depth + 1) + ')';
            i = after; continue;
          }
        }
      }
      out += name; i = j;
    } else { out += text[i]; i++; }
  }
  return out;
}
/** Expand box calls against `boxes` ([{name, vars, internals, formula}], as served by GET /boxes). */
export function expandBoxCalls(str, boxes) {
  const byName = new Map((boxes ?? []).map(b => [b.name, { params: b.vars, internals: b.internals ?? [], formula: b.formula }]));
  return expandRec(str, name => byName.get(name), { n: 0 }, 0);
}
