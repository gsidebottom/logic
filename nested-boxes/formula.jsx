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
      while (i < str.length && /[A-Za-z0-9_]/.test(str[i])) { name += str[i]; i++; }
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
// equiv  := xor  ('⇔' xor)*           x⇔y  = x·y + x'·y'
// xor    := impl ('⊕' impl)*          x⊕y  = x·y' + x'·y
// impl   := expr ('⇒' impl)?          x⇒y  = x' + y   (right-assoc)
// expr   := term ('+' term)*
// term   := factor ('·' factor)*
// factor := '(' equiv ')' "'"* | VAR
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

  function parseImpl() {
    const left = parseExpr();
    if (peek() !== '⇒') return left;
    eat();
    const right = parseImpl(); // right-associative
    return { t: 'OR', c: [complementAst(left), right] };
  }

  function parseXor() {
    let left = parseImpl();
    while (peek() === '⊕') {
      eat();
      const right = parseImpl();
      left = { t: 'OR', c: [
        { t: 'AND', c: [left,                complementAst(right)] },
        { t: 'AND', c: [complementAst(left),  right              ] },
      ]};
    }
    return left;
  }

  function parseEquiv() {
    let left = parseXor();
    while (peek() === '⇔') {
      eat();
      const right = parseXor();
      left = { t: 'OR', c: [
        { t: 'AND', c: [left,                right               ] },
        { t: 'AND', c: [complementAst(left),  complementAst(right)] },
      ]};
    }
    return left;
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
      const expr = parseEquiv();
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

  const result = parseEquiv();
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

export function parseCoveringPairs(pairs) {
  // Each pair string looks like "{A, A'}" — extract the two names
  return pairs.map(p => {
    const inner = p.replace(/^\{|\}$/g, '');
    return inner.split(',').map(s => s.trim());
  });
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
