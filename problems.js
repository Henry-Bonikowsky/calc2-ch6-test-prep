// Problem generators for the MA-172 Chapter 6 test (Briggs/Cochran 6.1-6.5, 6.7).
// Every problem carries: statement, steps (each checkable), worked solution, exact answer,
// and truth(): an independent numeric computation used by test/verify.js.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory(require('./vendor/math.js'), require('./check.js'));
  else root.Gen = factory(root.math, root.Check);
})(this, function (math, Check) {
  const T = s => Check.tex(s);

  // ---------- random ----------
  function rng(seed) {
    let a = seed >>> 0;
    const next = () => { a = (a + 0x6D2B79F5) >>> 0; let t = a; t = Math.imul(t ^ (t >>> 15), t | 1); t ^= t + Math.imul(t ^ (t >>> 7), t | 61); return ((t ^ (t >>> 14)) >>> 0) / 4294967296; };
    const r = { next, int: (lo, hi) => lo + Math.floor(next() * (hi - lo + 1)), pick: arr => arr[Math.floor(next() * arr.length)] };
    r.bool = () => next() < 0.5;
    return r;
  }

  // ---------- exact rationals ----------
  const gcd = (a, b) => { a = Math.abs(a); b = Math.abs(b); while (b) [a, b] = [b, a % b]; return a || 1; };
  class Q {
    constructor(n, d = 1) {
      if (!Number.isInteger(n) || !Number.isInteger(d) || d === 0) throw new Error('bad Q ' + n + '/' + d);
      if (d < 0) { n = -n; d = -d; }
      const g = gcd(n, d); this.n = n / g; this.d = d / g;
      if (!Number.isSafeInteger(this.n * 4) || !Number.isSafeInteger(this.d * 4)) throw new Error('Q overflow');
    }
    add(o) { o = q(o); return new Q(this.n * o.d + o.n * this.d, this.d * o.d); }
    sub(o) { return this.add(q(o).neg()); }
    neg() { return new Q(-this.n, this.d); }
    mul(o) { o = q(o); return new Q(this.n * o.n, this.d * o.d); }
    div(o) { o = q(o); return new Q(this.n * o.d, this.d * o.n); }
    get v() { return this.n / this.d; }
    isZero() { return this.n === 0; }
    eq(o) { o = q(o); return this.n === o.n && this.d === o.d; }
    lt(o) { return this.v < q(o).v; }
    str() { return this.d === 1 ? `${this.n}` : `${this.n}/${this.d}`; }
    pstr() { return this.d === 1 && this.n >= 0 ? this.str() : `(${this.str()})`; }
  }
  const q = (x, d) => x instanceof Q ? x : new Q(x, d === undefined ? 1 : d);
  const dec = x => { // terminating decimal -> Q
    let d = 1; while (!Number.isInteger(Math.round(x * d * 1e9) / 1e9)) d *= 10; return new Q(Math.round(x * d), d);
  };
  function nthRoot(n, k) { // exact integer k-th root or null
    if (n < 0) { if (k % 2 === 0) return null; const r = nthRoot(-n, k); return r === null ? null : -r; }
    const r = Math.round(Math.pow(n, 1 / k));
    for (const c of [r - 1, r, r + 1]) if (c >= 0 && Math.pow(c, k) === n) return c;
    return null;
  }
  function powQ(x, p) {
    x = q(x); p = q(p);
    if (x.isZero()) { if (p.v > 0) return q(0); throw new Error('0^neg'); }
    const rn = nthRoot(x.n, p.d), rd = nthRoot(x.d, p.d);
    if (rn === null || rd === null) throw new Error('irrational');
    let base = new Q(rn, rd), out = q(1);
    for (let i = 0; i < Math.abs(p.n); i++) out = out.mul(base);
    return p.n < 0 ? q(1).div(out) : out;
  }

  // ---------- generalized polynomials: sum of c * v^p, rational c and p ----------
  class GP {
    constructor(terms = []) {
      const m = new Map();
      for (const t of terms) { const k = t.p.str(); const prev = m.get(k); m.set(k, { p: t.p, c: prev ? prev.c.add(t.c) : t.c }); }
      this.t = [...m.values()].filter(t => !t.c.isZero()).sort((a, b) => b.p.v - a.p.v);
    }
    static k(c) { return new GP([{ p: q(0), c: q(c) }]); }
    static x(p = 1, c = 1) { return new GP([{ p: q(p), c: q(c) }]); }
    static poly(...cs) { return new GP(cs.map((c, i) => ({ p: q(cs.length - 1 - i), c: q(c) }))); } // highest power first
    add(o) { o = o instanceof GP ? o : GP.k(o); return new GP([...this.t, ...o.t]); }
    neg() { return new GP(this.t.map(t => ({ p: t.p, c: t.c.neg() }))); }
    sub(o) { o = o instanceof GP ? o : GP.k(o); return this.add(o.neg()); }
    scale(c) { return new GP(this.t.map(t => ({ p: t.p, c: t.c.mul(c) }))); }
    mul(o) { o = o instanceof GP ? o : GP.k(o); const out = []; for (const a of this.t) for (const b of o.t) out.push({ p: a.p.add(b.p), c: a.c.mul(b.c) }); return new GP(out); }
    sq() { return this.mul(this); }
    isZero() { return this.t.length === 0; }
    deriv() { return new GP(this.t.filter(t => !t.p.isZero()).map(t => ({ p: t.p.sub(1), c: t.c.mul(t.p) }))); }
    integ() { return new GP(this.t.map(t => { if (t.p.eq(-1)) throw new Error('ln term'); const p1 = t.p.add(1); return { p: p1, c: t.c.div(p1) }; })); }
    at(x) { x = q(x); let s = q(0); for (const t of this.t) s = s.add(t.c.mul(t.p.isZero() ? q(1) : powQ(x, t.p))); return s; }
    num(x) { let s = 0; for (const t of this.t) s += t.c.v * (t.p.isZero() ? 1 : t.p.d === 3 ? Math.pow(Math.cbrt(x), t.p.n) : Math.pow(x, t.p.v)); return s; }
    str(v) {
      if (!this.t.length) return '0';
      return this.t.map((t, i) => {
        const neg = t.c.n < 0, a = neg ? t.c.neg() : t.c;
        let s;
        const mono = p => p.eq(1) ? v : p.eq(new Q(1, 2)) ? `sqrt(${v})` : `${v}^${p.pstr()}`;
        if (t.p.isZero()) s = a.str();
        else if (t.p.v > 0) { const m = mono(t.p); s = (a.n === 1 ? m : `${a.n} ${m}`) + (a.d === 1 ? '' : ` / ${a.d}`); }
        else { const m = mono(t.p.neg()); s = `${a.n} / ${a.d === 1 ? m : '(' + a.d + ' ' + m + ')'}`; }
        return i === 0 ? (neg ? '-' + s : s) : (neg ? ' - ' : ' + ') + s;
      }).join('');
    }
    eq(o) { return this.sub(o).isZero(); }
  }

  // ---------- formatting helpers ----------
  const fmt = x => { const r = Math.round(x * 10000) / 10000; return Math.abs(x) >= 1e5 ? x.toExponential(4) : `${r}`; };
  function exactPi(Qv, pi) { // Q * (pi?) -> math.js string
    if (!pi) return Qv.str();
    if (Qv.isZero()) return '0';
    const n = Qv.n === 1 ? 'pi' : Qv.n === -1 ? '-pi' : `${Qv.n} pi`;
    return Qv.d === 1 ? n : `${n} / ${Qv.d}`;
  }
  const $ = s => `\\(${s}\\)`;
  const $$ = s => `\\[${s}\\]`;
  const pr = s => /^[-]?[\w.]+$/.test(s) ? s : `(${s})`;

  // ---------- worked-solution arithmetic: every operation written out ----------
  const tq = x => (x.n < 0 ? '-' : '') + (x.d === 1 ? `${Math.abs(x.n)}` : `\\frac{${Math.abs(x.n)}}{${x.d}}`);
  const ty = (x, v) => x.eq(1) ? v : `${tq(x)}\\,${v}`; // coefficient times a variable, 1y -> y
  const tqp = x => x.n < 0 || x.d !== 1 ? `\\left(${tq(x)}\\right)` : tq(x);
  const dn = x => { for (let k = 0; k <= 8; k++) if ((x.n * 10 ** k) % x.d === 0) return `${x.n * 10 ** k / x.d / 10 ** k}`; return tq(x); }; // decimal if it terminates
  const jn = parts => parts.length ? parts.map((s, i) => i === 0 ? s : s.startsWith('-') ? ` - ${s.slice(1)}` : ` + ${s}`).join('') : '0';
  const eqs = stages => stages.filter((s, i) => i === 0 || s !== stages[i - 1]).join(' = ');
  const tpow = (x, p) => p.eq(1) ? tqp(x) : p.eq(new Q(1, 2)) ? `\\sqrt{${tq(x)}}` : `(${tq(x)})^{${tq(p)}}`;
  const termT = (c, p, v) => (c.n < 0 ? '-' : '') + T(new GP([{ p, c: c.n < 0 ? c.neg() : c }]).str(v));
  const gpT = (g, v) => jn(g.t.map(t => termT(t.c, t.p, v)));
  const gpA = (g, v) => jn([...g.t].reverse().map(t => termT(t.c, t.p, v))); // lowest power first: 3 - y
  const piT = x => x.eq(1) ? '\\pi' : x.d === 1 ? `${x.n}\\pi` : `\\frac{${x.n}\\pi}{${x.d}}`;
  const gpP = (g, v) => g.t.length > 1 || (g.t[0] && g.t[0].c.n < 0) ? `\\left(${gpT(g, v)}\\right)` : gpT(g, v);
  // a1 + a2 + ... : common denominator, then the result
  function sumStages(qs) {
    const out = [jn(qs.map(tq))];
    if (qs.some(x => x.isZero()) && qs.some(x => !x.isZero())) { qs = qs.filter(x => !x.isZero()); out.push(jn(qs.map(tq))); }
    if (qs.length > 1) {
      const D = qs.reduce((d, x) => d * x.d / gcd(d, x.d), 1);
      if (D > 1 && qs.some(x => x.d !== D)) out.push(jn(qs.map(x => `${x.n < 0 ? '-' : ''}\\frac{${Math.abs(x.n) * D / x.d}}{${D}}`)));
      if (D > 1) { const N = qs.reduce((s, x) => s + x.n * D / x.d, 0); out.push(`\\frac{${N}}{${D}}`); }
      out.push(tq(qs.reduce((s, x) => s.add(x), q(0))));
    }
    return out;
  }
  // a · b : numerators and denominators multiplied, then reduced
  function mulStages(a, b) {
    const out = [`${tqp(a)}\\cdot ${tqp(b)}`];
    if (a.d !== 1 || b.d !== 1) out.push(`\\frac{${a.n}\\cdot ${tqp(q(b.n))}}{${[a.d, b.d].filter(d => d !== 1).join('\\cdot ')}}`,`\\frac{${a.n * b.n}}{${a.d * b.d}}`);
    out.push(tq(a.mul(b)));
    return out;
  }
  const mulLine = (a, b) => eqs(mulStages(a, b));
  // name(x) = substituted = powers worked out = products = sum
  function evalAt(Fg, x, name = 'F') {
    x = q(x);
    const head = `${name}(${tq(x)})`;
    if (!Fg.t.length) return `${head} = 0`;
    const coef = c => c.eq(1) ? '' : c.eq(-1) ? '-' : `${tq(c)}\\cdot `;
    const s1 = jn(Fg.t.map(t => t.p.isZero() ? tq(t.c) : coef(t.c) + tpow(x, t.p)));
    const pv = Fg.t.map(t => t.p.isZero() ? q(1) : powQ(x, t.p));
    const s2 = jn(Fg.t.map((t, i) => t.p.isZero() ? tq(t.c) : t.c.eq(1) || t.c.eq(-1) ? tq(t.c.mul(pv[i])) : `${tq(t.c)}\\cdot ${tqp(pv[i])}`));
    return `${head} = ${eqs([s1, s2, ...sumStages(Fg.t.map((t, i) => t.c.mul(pv[i])))])}`;
  }
  // (A)(B) = every pairwise product = like terms combined
  function mulGP(A, B, v) {
    const pairs = []; for (const a of A.t) for (const b of B.t) pairs.push(termT(a.c.mul(b.c), a.p.add(b.p), v));
    const l = gpP(A, v), r = gpP(B, v);
    return eqs([l.startsWith('\\left') && r.startsWith('\\left') ? l + r : `${l}\\cdot ${r}`, jn(pairs), gpT(A.mul(B), v)]);
  }
  // ∫ G dv term by term with the power rule
  function antiLine(G, v, asc) {
    const parts = (asc ? [...G.t].reverse() : G.t).map(t => { const p1 = t.p.add(1); const c = t.c.eq(1) ? '' : t.c.eq(-1) ? '-' : `${tq(t.c)}\\cdot `; return `${c}\\frac{${v}^{${p1.eq(1) ? '1' : tq(p1)}}}{${tq(p1)}}`; });
    return `\\int ${asc ? `\\left(${gpA(G, v)}\\right)` : gpP(G, v)}\\,d${v} = ${eqs([jn(parts), (asc ? gpA : gpT)(G.integ(), v)])}`;
  }
  // derivative term by term: d/dv (c v^p) = c·p v^(p-1)
  const derivLine = (f, v) => eqs([jn(f.t.map(t => t.p.isZero() ? '0' : `${tq(t.c)}\\cdot ${tqp(t.p)}\\,${v}^{${tq(t.p.sub(1))}}`)), gpT(f.deriv(), v)]);
  // F(b) - F(a), worked
  const diffLine = (Fb, Fa, b, a, name = 'F') => `${name}(${tq(q(b))}) - ${name}(${tq(q(a))}) = ${eqs([`${tq(Fb)} - ${tqp(Fa)}`, ...(Fa.isZero() ? [tq(Fb)] : sumStages([Fb, Fa.neg()]))])}`;
  // where the two boundary curves sit at each bound
  function boundsWork(top, bot, A, B, v, names) {
    return [A, B].map(x => { const d = top.sub(bot).at(x); return `At \\(${v} = ${tq(x)}\\): $$${evalAt(top, x, names[0])},\\qquad ${evalAt(bot, x, names[1])}$$ ${d.isZero() ? 'Equal, so the curves meet here.' : `Not equal, so the region is closed off by the line \\(${v} = ${tq(x)}\\) here.`}`; });
  }

  function finalize(p) {
    // Drop mistake candidates that are actually equivalent to the correct answer, and duplicates.
    for (const s of p.steps) {
      s.lo = s.lo ?? 0; s.hi = s.hi ?? 1;
      const kept = [];
      for (const m of s.mistakes || []) {
        let same = false;
        try {
          if (s.kind === 'num') same = Check.numEq(m.ans, s.ans) || kept.some(k => Check.numEq(m.ans, k.ans));
          else if (s.kind === 'expr') same = Check.exprEq(m.ans, s.ans, s.v, s.lo, s.hi) || kept.some(k => Check.exprEq(m.ans, k.ans, s.v, s.lo, s.hi));
          else same = Check.antiCheck(m.ans, s.integrand, s.v, s.lo, s.hi).ok;
        } catch (e) { same = true; }
        if (!same) kept.push(m);
      }
      s.mistakes = kept;
    }
    p.value = p.answer == null ? null : Check.evalNum(p.answer);
    return p;
  }

  // Standard integrate-and-evaluate steps + solution lines for factor * ∫_a^b G dv, G a GP.
  function integralSteps(o) {
    const { G, v, a, b, factor = '', factorQ = q(1), pi = false, what, unit = '', sym = 'V', anti = 'F', dec = false, asc = false } = o;
    const F = G.integ(), Fb = F.at(b), Fa = F.at(a), val = Fb.sub(Fa).mul(factorQ), Fd = asc ? { t: [...F.t].reverse() } : F;
    const lo = Math.min(a.v, b.v), hi = Math.max(a.v, b.v);
    const ans = exactPi(val, pi);
    const bare = exactPi(Fb.sub(Fa), false);
    const mistakes = [];
    if (pi || !factorQ.eq(1)) mistakes.push({ ans: bare, msg: `You dropped the constant out front (${factor || factorQ.str()}). Multiply your F(b) − F(a) by it.` });
    if (pi && factorQ.eq(2)) mistakes.push({ ans: exactPi(Fb.sub(Fa), true), msg: 'Shell method has 2π out front, not π.' });
    if (pi && factorQ.eq(1)) mistakes.push({ ans: exactPi(Fb.sub(Fa).mul(2), true), msg: 'Disk/washer has π out front, not 2π (2π is the shell method).' });
    if (!Fa.isZero()) mistakes.push({ ans: exactPi(Fb.mul(factorQ), pi), msg: `You forgot to subtract F(${a.str()}) = ${Fa.str()}. It's F(b) − F(a), and F(a) isn't 0 here.` });
    const steps = [
      { id: 'anti', label: `Antiderivative \\(F(${v})\\) of your integrand (any + C)`, kind: 'anti', v, lo, hi, integrand: G.str(v), ans: F.str(v), hint: 'Power rule backwards on every term: v^n → v^(n+1)/(n+1). Check by differentiating.' },
      { id: 'final', label: `${what} (exact, e.g. 8pi/27, or decimal to 4 significant digits)`, kind: 'num', ans, mistakes, hint: `Plug in: F(${b.str()}) − F(${a.str()}), then multiply by ${factor || 'the constant out front'}.` }
    ];
    const pre = factor ? factor : '';
    const D = Fb.sub(Fa), u = unit ? '\\ \\text{' + unit + '}' : '';
    const work = [
      `$$\\int_a^b (\\text{integrand})\\,d${v} = ${anti}(b) - ${anti}(a)$$`,
      `$$${sym} = ${pre}\\int_{${tq(a)}}^{${tq(b)}} \\left(${(asc ? gpA : gpT)(G, v)}\\right) d${v} = ${pre}\\Big[${anti}(${v})\\Big]_{${tq(a)}}^{${tq(b)}} = ${pre}\\big(${anti}(${tq(b)}) - ${anti}(${tq(a)})\\big)$$`,
      `Antiderivative, one term at a time (power rule \\(\\int ${v}^n\\,d${v} = \\frac{${v}^{n+1}}{n+1}\\)):`,
      `$$${anti}(${v}) = ${antiLine(G, v, asc)}$$`,
      `Plug in the top bound, then the bottom bound:`,
      `$$${evalAt(Fd, b, anti)}$$`, `$$${evalAt(Fd, a, anti)}$$`,
      `$$${diffLine(Fb, Fa, b, a, anti)}$$`,
    ];
    const ansT = dec ? `${dn(val)}${pi ? '\\pi' : ''}` : T(ans); // T() turns 117600 into 1.176e5
    // dec: 6.7 constants (62.5, 9800) read better as a decimal product when everything terminates
    const decMul = dec && ![factorQ, D, val].some(x => dn(x).includes('frac')) ? [`${dn(factorQ)} \\times ${D.n < 0 ? `(${dn(D)})` : dn(D)}${pi ? '\\,\\pi' : ''}`, `${dn(val)}${pi ? '\\pi' : ''}`] : null;
    if (pre) work.push(`Multiply by the constant out front, \\(${pre}\\):`, `$$${sym} = ${eqs([`${pre}\\cdot ${tqp(D)}`, ...(factorQ.eq(1) ? [] : decMul || mulStages(factorQ, D).map(s => pi ? `${s}\\cdot\\pi` : s)), ansT])}${u}$$`);
    else work.push(`$$${sym} = ${ansT}${u}$$`);
    const approx = Check.evalNum(ans), apT = dec ? `${+approx.toFixed(2)}` : fmt(approx);
    if (pi) work.push(`$$${ansT} = ${dn(val)}\\times 3.14159\\ldots \\approx ${apT}${u}$$`);
    else if (dn(val) !== apT) work.push(`$$${ansT} \\approx ${apT}${u}$$`);
    return { steps, work, ans, val };
  }

  // ---------- region bank (for 6.2-6.4) ----------
  // X: x in [a,b], bot <= y <= top.  Y: y in [c,d], left <= x <= right (only when every curve solves for x cleanly).
  // raw: independent closures in x used only by truth().
  const C = (t, e) => ({ t, e }); // curve "t = e"
  const REGIONS = [
    r => { const b = r.pick([1, 2, 3]); return { curves: [C('y', 'x^2'), C('y', '0'), C('x', `${b}`)], X: { a: q(0), b: q(b), top: GP.x(2), bot: GP.k(0) }, Y: { c: q(0), d: q(b * b), right: GP.k(b), left: GP.x(new Q(1, 2)) }, raw: { a: 0, b, top: x => x * x, bot: () => 0 } }; },
    r => { const b = r.pick([1, 4, 9]), s = Math.sqrt(b); return { curves: [C('y', 'sqrt(x)'), C('y', '0'), C('x', `${b}`)], X: { a: q(0), b: q(b), top: GP.x(new Q(1, 2)), bot: GP.k(0) }, Y: { c: q(0), d: q(s), right: GP.k(b), left: GP.x(2) }, raw: { a: 0, b, top: Math.sqrt, bot: () => 0 } }; },
    r => { const m = r.pick([1, 2, 3]); return { curves: [C('y', m === 1 ? 'x' : `${m} x`), C('y', 'x^2')], X: { a: q(0), b: q(m), top: GP.x(1, m), bot: GP.x(2) }, Y: { c: q(0), d: q(m * m), right: GP.x(new Q(1, 2)), left: GP.x(1, new Q(1, m)) }, raw: { a: 0, b: m, top: x => m * x, bot: x => x * x } }; },
    r => { const m = r.pick([1, 2, 3]); return { curves: [C('y', 'sqrt(x)'), C('y', m === 1 ? 'x' : `x / ${m}`)], X: { a: q(0), b: q(m * m), top: GP.x(new Q(1, 2)), bot: GP.x(1, new Q(1, m)) }, Y: { c: q(0), d: q(m), right: GP.x(1, m), left: GP.x(2) }, raw: { a: 0, b: m * m, top: Math.sqrt, bot: x => x / m } }; },
    r => { const b = r.pick([1, 2]); return { curves: [C('y', 'x^3'), C('y', '0'), C('x', `${b}`)], X: { a: q(0), b: q(b), top: GP.x(3), bot: GP.k(0) }, Y: { c: q(0), d: q(b ** 3), right: GP.k(b), left: GP.x(new Q(1, 3)) }, raw: { a: 0, b, top: x => x ** 3, bot: () => 0 } }; },
    r => { const b = r.pick([1, 2]); return { curves: [C('y', 'x^3'), C('y', `${b ** 3}`), C('x', '0')], X: { a: q(0), b: q(b), top: GP.k(b ** 3), bot: GP.x(3) }, Y: { c: q(0), d: q(b ** 3), right: GP.x(new Q(1, 3)), left: GP.k(0) }, raw: { a: 0, b, top: () => b ** 3, bot: x => x ** 3 } }; },
    r => { const s = r.pick([1, 2, 3]), c = s * s; return { curves: [C('y', `${c} - x^2`), C('y', '0'), C('x', '0')], quad: true, X: { a: q(0), b: q(s), top: GP.poly(-1, 0, c), bot: GP.k(0) }, Y: null, raw: { a: 0, b: s, top: x => c - x * x, bot: () => 0 } }; },
    r => { const p = r.pick([1, 2, 3]); return { curves: [C('y', p === 1 ? 'x - x^2' : `${p} x - x^2`), C('y', '0')], X: { a: q(0), b: q(p), top: GP.poly(-1, p, 0), bot: GP.k(0) }, Y: null, raw: { a: 0, b: p, top: x => p * x - x * x, bot: () => 0 } }; },
    r => { const n = r.pick([3, 4]); return { curves: [C('y', `x - x^${n}`), C('y', '0')], X: { a: q(0), b: q(1), top: GP.x(1).sub(GP.x(n)), bot: GP.k(0) }, Y: null, raw: { a: 0, b: 1, top: x => x - x ** n, bot: () => 0 } }; },
    r => { const n = r.pick([1, 2]), c = n * (n + 1); return { curves: [C('y', `${c} - x^2`), C('y', 'x'), C('x', '0')], quad: true, X: { a: q(0), b: q(n), top: GP.poly(-1, 0, c), bot: GP.x(1) }, Y: null, raw: { a: 0, b: n, top: x => c - x * x, bot: x => x } }; },
    r => { // two parabolas, like 6.4 #12
      const al = r.pick([0, 1, 2]), be = al + r.pick([2, 3]), h = r.int(al, be), m = r.pick([1, 2]);
      const bot = GP.poly(1, -2 * h, h * h + m), top = bot.add(GP.poly(-2, 2 * (al + be), -2 * al * be));
      return { curves: [C('y', top.str('x')), C('y', bot.str('x'))], X: { a: q(al), b: q(be), top, bot }, Y: null, raw: { a: al, b: be, top: x => (x - h) ** 2 + m + 2 * (x - al) * (be - x), bot: x => (x - h) ** 2 + m } };
    },
    r => { const c = r.pick([3, 4, 5, 6]), h = r.int(1, c - 2); return { curves: [C('y', `${c} - x`), C('y', `${h}`), C('x', '0')], X: { a: q(0), b: q(c - h), top: GP.poly(-1, c), bot: GP.k(h) }, Y: { c: q(h), d: q(c), right: GP.poly(-1, c), left: GP.k(0) }, raw: { a: 0, b: c - h, top: x => c - x, bot: () => h } }; },
    r => { const h = r.pick([1, 2, 3]), m = r.pick([1, 2, 3]), b = r.pick([2, 3, 4, 6]); return { curves: [C('y', `${h}`), C('y', `${m === 1 ? '' : m + ' '}x + ${h}`), C('x', `${b}`)], X: { a: q(0), b: q(b), top: GP.poly(m, h), bot: GP.k(h) }, Y: { c: q(h), d: q(m * b + h), right: GP.k(b), left: GP.poly(new Q(1, m), new Q(-h, m)) }, raw: { a: 0, b, top: x => m * x + h, bot: () => h } }; },
    r => { const j = r.pick([1, 2]); return { curves: [C('y', 'x^(1/3)'), C('y', j === 1 ? 'x' : `x / ${j * j}`)], quad: true, X: { a: q(0), b: q(j ** 3), top: GP.x(new Q(1, 3)), bot: GP.x(1, new Q(1, j * j)) }, Y: { c: q(0), d: q(j), right: GP.x(1, j * j), left: GP.x(3) }, raw: { a: 0, b: j ** 3, top: Math.cbrt, bot: x => x / (j * j) } }; },
  ];
  function regionText(R) {
    const cs = R.curves.map(c => $(`${c.t} = ${T(c.e)}`));
    const list = cs.length === 2 ? cs.join(' and ') : cs.slice(0, -1).join(', ') + ', and ' + cs[cs.length - 1];
    return `Let \\(R\\) be the region bounded by ${list}${R.quad ? ' in the first quadrant' : ''}`;
  }
  function yRange(R) { let lo = Infinity, hi = -Infinity; const { a, b, top, bot } = R.raw; for (let i = 0; i <= 400; i++) { const x = a + (b - a) * i / 400; lo = Math.min(lo, bot(x)); hi = Math.max(hi, top(x)); } return [lo, hi]; }
  const axisText = (kind, k) => kind === 'h' ? (k === 0 ? 'the \\(x\\)-axis' : `the line \\(y = ${k}\\)`) : (k === 0 ? 'the \\(y\\)-axis' : `the line \\(x = ${k}\\)`);

  // ---------- volumes ----------
  function volume(r, method, axisKind, shifted, R, kFix) {
    const formName = (method === 'washer') === (axisKind === 'h') ? 'X' : 'Y';
    while (!R || !R[formName]) R = r.pick(REGIONS)(r);
    const v = formName === 'X' ? 'x' : 'y', other = v === 'x' ? 'y' : 'x';
    const F = R[formName];
    const A = formName === 'X' ? F.a : F.c, B = formName === 'X' ? F.b : F.d;
    const lo = formName === 'X' ? F.bot : F.left, hi = formName === 'X' ? F.top : F.right;
    const [ymin, ymax] = yRange(R);
    const [pmin, pmax] = axisKind === 'h' ? [ymin, ymax] : [R.raw.a, R.raw.b]; // range of the coordinate the axis is measured in
    let k = 0, side = 'low';
    if (kFix !== undefined) { k = kFix; side = k <= pmin + 1e-9 ? 'low' : 'high'; }
    else if (shifted) {
      const opts2 = [];
      opts2.push(['low', Math.floor(pmin + 1e-9) - r.int(1, 3)]);
      if (pmin > 1e-9) opts2.push(['low', Math.round(pmin)]);
      opts2.push(['high', Math.ceil(pmax - 1e-9) + r.int(0, 2)]);
      [side, k] = r.pick(opts2);
      if (k === 0) k = side === 'low' ? -1 : k;
    }
    const kk = q(k);
    const axisLine = axisKind === 'h' ? `y = ${k}` : `x = ${k}`;
    const axisDesc = axisText(axisKind, k);
    const dv = `d${v}`;
    const steps = [];
    const sol = [];
    const isYform = formName === 'Y';
    // bounds
    const xb = R.X;
    const boundMistakes = which => isYform ? [{ ans: (which === 'a' ? xb.a : xb.b).str(), msg: `That's an x-value. You're integrating ${dv}, so the bounds are y-values: plug the x-intersection into a curve to get y.` }] : [];
    steps.push({ id: 'a', label: `Lower bound of ${v}`, kind: 'num', ans: A.str(), mistakes: boundMistakes('a'), hint: `Find where the curves meet (set them equal) and read off ${v}. Integrating ${dv} means ${v}-values.` });
    steps.push({ id: 'b', label: `Upper bound of ${v}`, kind: 'num', ans: B.str(), mistakes: boundMistakes('b'), hint: `Largest ${v} in the region: an intersection point or a given line.` });
    const L = Math.min(A.v, B.v), H = Math.max(A.v, B.v);
    const fn = (g) => T(g.str(v));
    const near = side === 'low' ? lo : hi, far = side === 'low' ? hi : lo;
    const dist = g => side === 'low' ? g.sub(kk) : kk.isZero() ? g.neg() : GP.k(k).sub(g);
    let G, factor, factorQ, what = 'Volume \\(V\\)';
    const swapDesc = isYform ? 'right/left' : 'top/bottom';
    const [hiN, loN] = isYform ? ['right', 'left'] : ['top', 'bottom'], [farN, nearN] = side === 'low' ? [hiN, loN] : [loN, hiN];
    if (method === 'washer') {
      const Rr = dist(far), rr = dist(near);
      const disk = rr.isZero();
      const shiftMs = (g, gd) => k === 0 ? [] : [
        { ans: g.str(v), msg: `You measured from the ${other === 'y' ? 'x' : 'y'}-axis. The axis is ${axisLine}: radius = distance from that line = ${side === 'low' ? `(curve) − (${k})` : `${k} − (curve)`}.` },
        { ans: side === 'low' ? g.add(kk).str(v) : g.sub(kk).str(v), msg: `Sign slip with the shift. Distance from ${axisLine} is ${side === 'low' ? `curve − (${k})` : `${k} − curve`}.` }];
      steps.push({ id: 'R', label: `Outer radius \\(R(${v})\\) (farther boundary to the axis)`, kind: 'expr', v, lo: L, hi: H, ans: Rr.str(v),
        mistakes: [{ ans: rr.str(v), msg: 'That is the inner radius (the boundary closer to the axis). R comes from the boundary farther from the axis.' }, ...shiftMs(far)],
        signHint: 'A radius is a distance: (farther coordinate) − (axis coordinate), always positive.', hint: `R = distance from the axis ${axisLine} out to the farther boundary${isYform ? ', written as x = (function of y)' : ''}.` });
      steps.push({ id: 'r', label: `Inner radius \\(r(${v})\\) (enter 0 if it's a disk)`, kind: 'expr', v, lo: L, hi: H, ans: rr.str(v),
        mistakes: [{ ans: Rr.str(v), msg: 'That is the outer radius. r is the distance to the closer boundary.' }, ...(disk ? [] : [{ ans: '0', msg: 'Not a disk: the region does not touch the axis along each slice, so there is a hole. r = distance to the closer boundary.' }]), ...(disk ? [] : shiftMs(near))],
        signHint: 'A radius is a distance, always positive.', hint: disk ? 'The region sits right on the axis, so there is no hole: r = 0.' : `r = distance from ${axisLine} to the closer boundary.` });
      G = Rr.sq().sub(rr.sq());
      factor = '\\pi'; factorQ = q(1);
      steps.push({ id: 'integrand', label: `Integrand: \\(V = \\pi\\int_a^b (\\;?\\;)\\,${dv}\\). Enter \\(R^2 - r^2\\).`, kind: 'expr', v, lo: L, hi: H, ans: G.str(v),
        mistakes: [
          { ans: `(${Rr.str(v)} - (${rr.str(v)}))^2`, msg: 'Square each radius separately: R² − r², not (R − r)².' },
          { ans: `(${Rr.str(v)})^2 + (${rr.str(v)})^2`, msg: 'Subtract the hole: R² − r², not R² + r².' },
          { ans: `${Rr.str(v)} - (${rr.str(v)})`, msg: 'The radii must be squared: area of a washer is π(R² − r²).' },
          { ans: `(${rr.str(v)})^2 - (${Rr.str(v)})^2`, msg: 'Backwards: outer squared minus inner squared.' },
          ...(disk ? [] : [{ ans: `(${Rr.str(v)})^2`, msg: 'You left out the hole: subtract r².' }])],
        hint: 'Square R, square r, subtract. Expanding is optional.' });
      sol.push(`${disk ? 'Disk' : 'Washer'} slices are perpendicular to the axis ${axisLine}, so they have thickness \\(${dv}\\); ${v} runs from \\(${T(A.str())}\\) to \\(${T(B.str())}\\).`);
      const distT = g => side === 'low' ? `${gpP(g, v)} - ${tqp(kk)}` : `${tq(kk)} - ${gpP(g, v)}`;
      sol.push(`Radius = distance from the axis ${axisLine} (so \\(k = ${k}\\)) to the boundary:`, side === 'low' ? `$$R(${v}) = \\text{${farN}}(${v}) - k,\\qquad r(${v}) = \\text{${nearN}}(${v}) - k$$` : `$$R(${v}) = k - \\text{${farN}}(${v}),\\qquad r(${v}) = k - \\text{${nearN}}(${v})$$`, `$$R(${v}) = ${distT(far)} = ${fn(Rr)},\\qquad r(${v}) = ${distT(near)} = ${fn(rr)}${disk ? '\\ (\\text{disk: no hole})' : ''}$$`);
      sol.push(`Square each radius, multiplying out every term:`, `$$R^2 = ${mulGP(Rr, Rr, v)}$$`, ...(disk ? [] : [`$$r^2 = ${mulGP(rr, rr, v)}$$`]));
      sol.push(`$$R^2 - r^2 = ${eqs([`${gpP(Rr.sq(), v)} - ${gpP(rr.sq(), v)}`, jn([...Rr.sq().t.map(t => termT(t.c, t.p, v)), ...rr.sq().t.map(t => termT(t.c.neg(), t.p, v))]), gpT(G, v)])}$$`);
      sol.push(`$$V = \\pi\\int_a^b \\left[R(${v})^2 - r(${v})^2\\right] ${dv}$$`, `$$V = \\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left[\\left(${fn(Rr)}\\right)^2 - \\left(${fn(rr)}\\right)^2\\right] ${dv} = \\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left(${fn(G)}\\right) ${dv}$$`);
    } else {
      const rad = side === 'low' ? GP.x(1).sub(kk) : (kk.isZero() ? GP.x(1).neg() : GP.k(k).sub(GP.x(1)));
      const height = hi.sub(lo);
      steps.push({ id: 'radius', label: `Shell radius in terms of \\(${v}\\) (distance from the axis)`, kind: 'expr', v, lo: L, hi: H, ans: rad.str(v),
        mistakes: [...(k === 0 ? [] : [{ ans: v, msg: `You used ${v}, the distance to the ${v === 'x' ? 'y' : 'x'}-axis. The axis is ${axisLine}, so radius = ${side === 'low' ? `${v} − (${k})` : `${k} − ${v}`}.` },
          { ans: side === 'low' ? `${v} + (${k})` : `${v} - ${k}`, msg: `Sign slip: distance from ${axisLine} to the shell at ${v} is ${side === 'low' ? `${v} − (${k})` : `${k} − ${v}`}.` }]),
          { ans: height.str(v), msg: 'That is the shell height. The radius is the distance from the axis to the shell.' }],
        signHint: 'A radius is a distance: always positive. Bigger coordinate minus smaller.', hint: `Distance from ${axisLine} to a shell at ${v}. Only the radius changes when the axis moves; the height never does.` });
      steps.push({ id: 'height', label: `Shell height \\(h(${v})\\) (${isYform ? 'right − left' : 'top − bottom'})`, kind: 'expr', v, lo: L, hi: H, ans: height.str(v),
        mistakes: [{ ans: hi.str(v), msg: `Height is ${isYform ? 'right minus left' : 'top minus bottom'}: you forgot to subtract the ${isYform ? 'left' : 'bottom'} curve.` }, { ans: rad.str(v), msg: 'That is the radius, not the height.' }],
        signHint: `Height = ${isYform ? 'right − left' : 'top − bottom'}.`, hint: isYform ? 'Solve every curve for x = g(y). Height = (right curve) − (left curve).' : 'Height = (top curve) − (bottom curve).' });
      G = rad.mul(height);
      factor = '2\\pi'; factorQ = q(2);
      steps.push({ id: 'integrand', label: `Integrand: \\(V = 2\\pi\\int_a^b (\\;?\\;)\\,${dv}\\). Enter radius × height.`, kind: 'expr', v, lo: L, hi: H, ans: G.str(v),
        mistakes: [{ ans: height.str(v), msg: 'You left out the radius. Shell integrand = (radius)(height).' }, { ans: rad.str(v), msg: 'You left out the height. Shell integrand = (radius)(height).' }, { ans: `(${rad.str(v)}) * (${height.str(v)})^2`, msg: 'Nothing is squared in the shell method: (radius)(height).' }],
        hint: 'Multiply your radius by your height (expanding is optional).' });
      sol.push(`Shells are parallel to the axis ${axisLine} (so \\(k = ${k}\\)), so they have thickness \\(${dv}\\); ${v} runs from \\(${T(A.str())}\\) to \\(${T(B.str())}\\).`);
      sol.push(`$$\\text{radius} = ${side === 'low' ? `${v} - k` : `k - ${v}`},\\qquad \\text{height} = \\text{${hiN}}(${v}) - \\text{${loN}}(${v})$$`);
      sol.push(`$$\\text{radius} = ${side === 'low' ? `${v} - ${tqp(kk)}` : `${tq(kk)} - ${v}`} = ${fn(rad)},\\qquad \\text{height} = ${gpP(hi, v)} - ${gpP(lo, v)} = ${fn(height)}$$`);
      sol.push(`Multiply radius by height, every term:`, `$$\\text{radius}\\cdot\\text{height} = ${mulGP(rad, height, v)}$$`);
      sol.push(`$$V = 2\\pi\\int_a^b (\\text{radius})(\\text{height})\\,${dv}$$`, `$$V = 2\\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left(${fn(rad)}\\right)\\left(${fn(height)}\\right) ${dv} = 2\\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left(${fn(G)}\\right) ${dv}$$`);
    }
    const I = integralSteps({ G, v, a: A, b: B, factor, factorQ: method === 'washer' ? q(1) : q(2), pi: true, what });
    steps.push(...I.steps);
    sol.push(...I.work);
    sol.splice(1, 0, ...boundsWork(hi, lo, A, B, v, isYform ? ['\\text{right}', '\\text{left}'] : ['\\text{top}', '\\text{bottom}']));
    if (isYform) sol.unshift(`Integrating \\(dy\\), so every boundary is written as \\(x = g(y)\\): right \\(x = ${fn(hi)}\\), left \\(x = ${fn(lo)}\\).`);
    const methodWord = method === 'washer' ? 'the disk/washer method' : 'the shell method';
    const raw = R.raw;
    return finalize({
      statement: `${regionText(R)}. Use ${methodWord} to find the volume of the solid generated when \\(R\\) is revolved about ${axisDesc}.`,
      steps, solution: sol, answer: I.ans, region: R, axis: { kind: axisKind, k }, form: formName, fac: method === 'washer' ? Math.PI : 2 * Math.PI,
      truth: () => axisKind === 'h'
        ? Check.simpson(x => Math.PI * Math.abs((raw.top(x) - k) ** 2 - (raw.bot(x) - k) ** 2), raw.a, raw.b, 20000)
        : Check.simpson(x => 2 * Math.PI * Math.abs(x - k) * (raw.top(x) - raw.bot(x)), raw.a, raw.b, 20000),
    });
  }

  // General slicing (6.3): known cross-sections on a base region, V = ∫ A(v) dv.
  const SHAPES = [
    { name: 'squares', desc: 'squares with a side in the base', f: '', fQ: q(1), pi: false, tex: 's^2', txt: 's²' },
    { name: 'semicircles', desc: 'semicircles with a diameter in the base', f: '\\frac{\\pi}{8}', fQ: new Q(1, 8), pi: true, tex: '\\tfrac{\\pi}{8}s^2', txt: 'πs²/8' },
    { name: 'isosceles right triangles', desc: 'isosceles right triangles with a leg in the base', f: '\\frac{1}{2}', fQ: new Q(1, 2), pi: false, tex: '\\tfrac12 s^2', txt: 's²/2' },
  ];
  function slicing(r) {
    let R = null; const perpY = r.bool();
    const formName = perpY ? 'Y' : 'X';
    while (!R || !R[formName]) R = r.pick(REGIONS)(r);
    const F = R[formName], v = perpY ? 'y' : 'x', sh = r.pick(SHAPES);
    const A = perpY ? F.c : F.a, B = perpY ? F.d : F.b, hi = perpY ? F.right : F.top, lo = perpY ? F.left : F.bot;
    const side = hi.sub(lo), G = side.sq(), L = Math.min(A.v, B.v), H = Math.max(A.v, B.v);
    const Atxt = sh.pi ? `pi / 8 * (${side.str(v)})^2` : sh.fQ.eq(1) ? `(${side.str(v)})^2` : `(${side.str(v)})^2 / 2`;
    const steps = [
      { id: 'a', label: `Lower bound of ${v}`, kind: 'num', ans: A.str(), mistakes: perpY ? [{ ans: R.X.a.str(), msg: `Slices are perpendicular to the y-axis, so you integrate dy: bounds are y-values.` }] : [], hint: `The base runs along the ${v}-axis; find its smallest ${v}.` },
      { id: 'b', label: `Upper bound of ${v}`, kind: 'num', ans: B.str(), mistakes: perpY ? [{ ans: R.X.b.str(), msg: `Slices are perpendicular to the y-axis, so you integrate dy: bounds are y-values.` }] : [], hint: `Largest ${v} in the base region.` },
      { id: 'side', label: `Length \\(s(${v})\\) of the slice across the base (${perpY ? 'right − left' : 'top − bottom'})`, kind: 'expr', v, lo: L, hi: H, ans: side.str(v), mistakes: [{ ans: hi.str(v), msg: `You forgot to subtract the ${perpY ? 'left' : 'bottom'} curve. s = ${perpY ? 'right − left' : 'top − bottom'}.` }], signHint: `s is a length: ${perpY ? 'right minus left' : 'top minus bottom'}.`, hint: `${perpY ? 'Right curve minus left curve, as functions of y' : 'Top curve minus bottom curve'}.` },
      { id: 'A', label: `Cross-section area \\(A(${v})\\) (${sh.name}: \\(A = ${sh.tex}\\))`, kind: 'expr', v, lo: L, hi: H, ans: Atxt,
        mistakes: [{ ans: `(${side.str(v)})^2`, msg: `That is a square's area. For ${sh.name}, A = ${sh.txt}.` }, { ans: `pi * (${side.str(v)})^2`, msg: 'The base length s is the diameter, not the radius: r = s/2, so a semicircle is ½π(s/2)² = πs²/8.' }, { ans: `pi / 2 * (${side.str(v)})^2`, msg: 'r = s/2, not s: ½π(s/2)² = πs²/8.' }, { ans: side.str(v), msg: 'Area needs s squared; you entered the length s.' }],
        hint: `Plug s(${v}) into the area formula for ${sh.name}.` },
      { id: 'integrand', label: `Integrand: \\(V = ${sh.f}\\int_a^b (\\;?\\;)\\,d${v}\\)`, kind: 'expr', v, lo: L, hi: H, ans: G.str(v), mistakes: [{ ans: side.str(v), msg: 'Square the slice length: the integrand is s².' }], hint: sh.f ? `A = ${sh.txt}: pull the constant out front; what is left is s².` : 'A = s².' },
    ];
    const I = integralSteps({ G, v, a: A, b: B, factor: sh.f, factorQ: sh.fQ, pi: sh.pi, what: 'Volume \\(V\\)' });
    steps.push(...I.steps);
    const raw = R.raw, sq = x => (raw.top(x) - raw.bot(x)) ** 2;
    return finalize({
      statement: `${regionText(R)}. \\(R\\) is the base of a solid whose cross-sections perpendicular to the ${v}-axis are ${sh.desc}. Find the volume of the solid.`,
      steps, answer: I.ans, region: R, fac: sh.fQ.v * (sh.pi ? Math.PI : 1),
      solution: [`Slices perpendicular to the ${v}-axis have thickness \\(d${v}\\); ${v} runs from \\(${T(A.str())}\\) to \\(${T(B.str())}\\).`,
        ...boundsWork(hi, lo, A, B, v, perpY ? ['\\text{right}', '\\text{left}'] : ['\\text{top}', '\\text{bottom}']),
        `$$s(${v}) = \\text{${perpY ? 'right' : 'top'}}(${v}) - \\text{${perpY ? 'left' : 'bottom'}}(${v}),\\qquad A(${v}) = ${sh.tex},\\qquad V = \\int_a^b A(${v})\\,d${v}$$`,
        `$$s(${v}) = ${gpP(hi, v)} - ${gpP(lo, v)} = ${T(side.str(v))},\\qquad A(${v}) = ${sh.f}\\left(${T(side.str(v))}\\right)^2$$`,
        `Square the slice length, every term:`, `$$s^2 = ${mulGP(side, side, v)}$$`,
        ...I.work],
      // Independent truth: integrate over x; for dy slices integrate the y-form side length numerically.
      truth: () => sh.fQ.v * (sh.pi ? Math.PI : 1) * (perpY ? Check.simpson(y => (F.right.num(y) - F.left.num(y)) ** 2, F.c.v, F.d.v, 20000) : Check.simpson(sq, raw.a, raw.b, 20000)),
    });
  }

  // Set up both ways, evaluate the easier (class format).
  function bothWays(r, R0, axisKind) {
    R0 = R0 || r.pick(REGIONS.filter((f, i) => [0, 1, 2, 3, 4, 5, 11, 12, 13].includes(i)))(r);
    axisKind = axisKind || (r.bool() ? 'h' : 'v');
    const W = volume(r, 'washer', axisKind, false, R0), S = volume(r, 'shell', axisKind, false, R0);
    const pickSteps = (P, tag) => P.steps.filter(s => ['a', 'b', 'integrand'].includes(s.id)).map(s => ({ ...s, id: tag + '-' + s.id, label: `${tag === 'w' ? 'Disk/washer' : 'Shell'}: ${s.label}` }));
    const steps = [...pickSteps(W, 'w'), ...pickSteps(S, 's'), { ...W.steps.find(s => s.id === 'final'), id: 'final', mistakes: W.steps.find(s => s.id === 'final').mistakes.concat(S.steps.find(s => s.id === 'final').mistakes) }];
    return finalize({
      statement: W.statement.replace('Use the disk/washer method to find', 'Set up the integral for') + ' Set it up with <b>both</b> the disk/washer method and the shell method, then evaluate the easier one.',
      steps, answer: W.answer, region: W.region, axis: W.axis,
      solution: ['<b>Disk/washer:</b>', ...W.solution, '<b>Shell:</b>', ...S.solution, 'Both give the same volume because they describe the same solid. Pick whichever integral is easier (bound at 0, fewer squares, no messy solving for x).'],
      truth: W.truth, twin: S.answer,
    });
  }

  // ---------- 6.2 area ----------
  function areaX(r) {
    let top, bot, a, b, curves, raw;
    if (r.bool()) { // parabola vs line with integer intersections
      const al = r.int(-2, 1), be = al + r.int(2, 4), h = r.int(-2, 2), s = r.int(-3, 3);
      bot = GP.poly(1, -2 * h, h * h + s);
      top = bot.add(GP.poly(-1, al + be, -al * be));
      a = q(al); b = q(be);
      raw = { top: x => (x - h) ** 2 + s + (x - al) * (be - x), bot: x => (x - h) ** 2 + s };
      curves = [C('y', top.str('x')), C('y', bot.str('x'))];
      if (r.bool()) curves.reverse();
    } else {
      const R = r.pick(REGIONS)(r);
      ({ top, bot, a, b } = R.X); raw = R.raw; curves = R.curves;
      return areaFromRegion(R, regionText(R));
    }
    return areaCore({ top, bot, a, b, v: 'x', raw, statement: `Find the area of the region bounded by ${curves.map(c => $(`${c.t} = ${T(c.e)}`)).join(' and ')}.` });
  }
  function areaFromRegion(R, text) { const { top, bot, a, b } = R.X; return areaCore({ top, bot, a, b, v: 'x', raw: R.raw, statement: `${text}. Find the area of \\(R\\).` }); }
  function areaCore({ top, bot, a, b, v, raw, statement, names = ['top', 'bottom'] }) {
    const D = top.sub(bot);
    const L = a.v, H = b.v;
    const steps = [
      { id: 'a', label: `Lower bound (smaller ${v} where the region starts)`, kind: 'num', ans: a.str(), hint: `Set the curves equal and solve for ${v}.` },
      { id: 'b', label: `Upper bound`, kind: 'num', ans: b.str(), hint: `Set the curves equal and solve for ${v}; or use the given line.` },
      { id: 'integrand', label: `Integrand: \\(A = \\int_a^b(\\;?\\;)\\,d${v}\\). Enter (${names[0]}) − (${names[1]}).`, kind: 'expr', v, lo: L, hi: H, ans: D.str(v),
        mistakes: [{ ans: top.str(v), msg: `You forgot to subtract the ${names[1]} curve.` }], signHint: `It's (${names[0]}) − (${names[1]}). Test a point between the bounds to see which curve is ${names[0] === 'top' ? 'higher' : 'farther right'}.`, hint: `(${names[0]} curve) − (${names[1]} curve), both in terms of ${v}.` },
    ];
    const I = integralSteps({ G: D, v, a, b, what: 'Area \\(A\\)', sym: 'A' });
    steps.push(...I.steps);
    return finalize({
      statement, steps, answer: I.ans,
      solution: [`The curves meet at \\(${v} = ${T(a.str())}\\) and \\(${v} = ${T(b.str())}\\). ${names[0] === 'top' ? 'Top' : 'Right'} curve \\(${T(top.str(v))}\\), ${names[1]} curve \\(${T(bot.str(v))}\\).`,
        ...boundsWork(top, bot, a, b, v, names.map(n => `\\text{${n}}`)),
        `$$A = \\int_a^b \\big(\\text{${names[0]}}(${v}) - \\text{${names[1]}}(${v})\\big)\\,d${v}$$`,
        `Subtract, distributing the minus sign to every term:`,
        `$$(\\text{${names[0]}}) - (\\text{${names[1]}}) = ${eqs([`${gpP(top, v)} - ${gpP(bot, v)}`, jn([...top.t.map(t => termT(t.c, t.p, v)), ...bot.t.map(t => termT(t.c.neg(), t.p, v))]), gpT(D, v)])}$$`,
        ...I.work],
      truth: () => Check.simpson(t => raw.top(t) - raw.bot(t), L, H, 20000),
    });
  }
  function areaY(r) {
    const al = r.int(-2, 1), be = al + r.int(2, 4), h = r.int(-1, 2), s = r.int(-2, 2);
    const left = GP.poly(1, -2 * h, h * h + s), right = left.add(GP.poly(-1, al + be, -al * be));
    const curves = [C('x', left.str('y')), C('x', right.str('y'))];
    if (r.bool()) curves.reverse();
    return areaCore({ top: right, bot: left, a: q(al), b: q(be), v: 'y', names: ['right', 'left'],
      raw: { top: y => (y - h) ** 2 + s + (y - al) * (be - y), bot: y => (y - h) ** 2 + s },
      statement: `Find the area of the region bounded by ${curves.map(c => $(`${c.t} = ${T(c.e)}`)).join(' and ')}. (Integrate with respect to \\(y\\).)` });
  }
  function areaSplit(r) {
    if (r.next() < 0.25) {
      const wide = r.bool(), b = wide ? 'pi' : 'pi/2';
      const A1 = 'sqrt(2) - 1', A2 = wide ? '1 + sqrt(2)' : 'sqrt(2) - 1', tot = wide ? '2 sqrt(2)' : '2 sqrt(2) - 2';
      const steps = [
        { id: 'c', label: 'Where do the curves cross inside the interval?', kind: 'num', ans: 'pi/4', hint: 'Solve sin x = cos x, i.e. tan x = 1.' },
        { id: 'A1', label: 'Area of the left piece (from 0 to the crossing)', kind: 'num', ans: A1, mistakes: [{ ans: '1 - sqrt(2)', msg: 'Negative: on the left piece cos x is on top, so integrate cos x − sin x.' }], hint: 'On [0, π/4], cos x ≥ sin x. Integrate cos x − sin x.' },
        { id: 'A2', label: `Area of the right piece (from the crossing to ${wide ? 'π' : 'π/2'})`, kind: 'num', ans: A2, hint: 'On the right piece sin x is on top. Integrate sin x − cos x.' },
        { id: 'final', label: 'Total area', kind: 'num', ans: tot, mistakes: [{ ans: wide ? '2' : '0', msg: 'You integrated without splitting, so the pieces cancelled. Area needs |top − bottom|: split at the crossing and add.' }], hint: 'Add the two pieces.' },
      ];
      return finalize({ statement: `Find the area of the region between \\(y = \\sin x\\) and \\(y = \\cos x\\) on \\([0, ${wide ? '\\pi' : '\\tfrac{\\pi}{2}'}]\\).`, steps, answer: tot,
        solution: ['The curves cross where \\(\\tan x = 1\\), at \\(x = \\pi/4\\). Left of it cos is on top; right of it sin is on top.', '$$A = \\int_a^c (\\text{top} - \\text{bottom})\\,dx + \\int_c^b (\\text{top} - \\text{bottom})\\,dx$$',
          `$$A = \\int_0^{\\pi/4}(\\cos x - \\sin x)\\,dx + \\int_{\\pi/4}^{${wide ? '\\pi' : '\\pi/2'}}(\\sin x - \\cos x)\\,dx$$`,
          'Values used: \\(\\sin 0 = 0,\\ \\cos 0 = 1,\\ \\sin\\frac{\\pi}{4} = \\cos\\frac{\\pi}{4} = \\frac{\\sqrt2}{2}\\), ' + (wide ? '\\(\\sin\\pi = 0,\\ \\cos\\pi = -1\\).' : '\\(\\sin\\frac{\\pi}{2} = 1,\\ \\cos\\frac{\\pi}{2} = 0\\).'),
          '$$\\int(\\cos x - \\sin x)\\,dx = \\sin x - (-\\cos x) = \\sin x + \\cos x$$',
          '$$\\Big[\\sin x + \\cos x\\Big]_0^{\\pi/4} = \\left(\\frac{\\sqrt2}{2} + \\frac{\\sqrt2}{2}\\right) - (0 + 1) = \\frac{2\\sqrt2}{2} - 1 = \\sqrt2 - 1$$',
          '$$\\int(\\sin x - \\cos x)\\,dx = -\\cos x - \\sin x$$',
          wide ? '$$\\Big[-\\cos x - \\sin x\\Big]_{\\pi/4}^{\\pi} = \\big(-(-1) - 0\\big) - \\left(-\\frac{\\sqrt2}{2} - \\frac{\\sqrt2}{2}\\right) = 1 - (-\\sqrt2) = 1 + \\sqrt2$$'
            : '$$\\Big[-\\cos x - \\sin x\\Big]_{\\pi/4}^{\\pi/2} = (-0 - 1) - \\left(-\\frac{\\sqrt2}{2} - \\frac{\\sqrt2}{2}\\right) = -1 - (-\\sqrt2) = \\sqrt2 - 1$$',
          `$$A = (${T(A1)}) + (${T(A2)}) = ${wide ? '\\sqrt2 - 1 + 1 + \\sqrt2 = 2\\sqrt2' : '\\sqrt2 - 1 + \\sqrt2 - 1 = 2\\sqrt2 - 2'} \\approx ${fmt(Check.evalNum(tot))}$$`],
        truth: () => Check.simpson(x => Math.abs(Math.sin(x) - Math.cos(x)), 0, Math.PI / 4, 4000) + Check.simpson(x => Math.abs(Math.sin(x) - Math.cos(x)), Math.PI / 4, wide ? Math.PI : Math.PI / 2, 4000) });
    }
    // y = x^2 vs a line crossing at c inside [a,b]; other root outside.
    const c = r.int(-1, 2), a = c - r.int(1, 2), b = c + r.int(1, 2), e = r.bool() ? a - r.int(1, 2) : b + r.int(1, 2);
    const f = GP.x(2), D = GP.poly(1, -(c + e), c * e), g = f.sub(D); // f - g = (x-c)(x-e)
    const left = D.integ(), I1 = left.at(c).sub(left.at(a)), I2 = left.at(b).sub(left.at(c));
    const A1 = I1.v < 0 ? I1.neg() : I1, A2 = I2.v < 0 ? I2.neg() : I2, tot = A1.add(A2), net = I1.add(I2);
    const topL = I1.v > 0 ? 'y = x^2' : `y = ${g.str('x')}`;
    const steps = [
      { id: 'c', label: 'Where do the curves cross inside the interval?', kind: 'num', ans: `${c}`, hint: 'Set the curves equal; keep the root that lies inside the interval.' },
      { id: 'A1', label: `Area of the left piece, \\([${a}, ${c}]\\)`, kind: 'num', ans: A1.str(), hint: 'Top minus bottom on this piece (test a point to see which is on top).' },
      { id: 'A2', label: `Area of the right piece, \\([${c}, ${b}]\\)`, kind: 'num', ans: A2.str(), hint: 'The curves switch: the other one is on top now.' },
      { id: 'final', label: 'Total area', kind: 'num', ans: tot.str(), mistakes: [{ ans: net.str(), msg: 'You integrated straight across without splitting, so the pieces partly cancelled. Split at the crossing and add the two positive areas.' }, { ans: net.v < 0 ? net.neg().str() : net.str(), msg: 'Taking |net integral| still lets the pieces cancel. Split at the crossing and add the two areas.' }], hint: 'Add the two pieces.' },
    ];
    return finalize({ statement: `Find the area of the region between \\(y = x^2\\) and \\(y = ${T(g.str('x'))}\\) on the interval \\([${a}, ${b}]\\).`, steps, answer: tot.str(),
      solution: [`Setting \\(x^2 = ${T(g.str('x'))}\\) gives \\(x = ${c}\\) and \\(x = ${e}\\); only \\(x = ${c}\\) is inside \\([${a},${b}]\\), so the curves switch there and the region must be split.`,
        '$$A = A_1 + A_2 = \\int_a^c (\\text{top} - \\text{bottom})\\,dx + \\int_c^b (\\text{top} - \\text{bottom})\\,dx$$',
        `Subtract, every term: $$x^2 - \\left(${gpT(g, 'x')}\\right) = ${gpT(D, 'x')} = (x ${c < 0 ? '+ ' + -c : '- ' + c})(x ${e < 0 ? '+ ' + -e : '- ' + e})$$ Antiderivative, one term at a time: $$F(x) = ${antiLine(D, 'x')}$$`,
        `Left piece \\([${a},${c}]\\):`, `$$${evalAt(left, c)}$$`, `$$${evalAt(left, a)}$$`, `$$${diffLine(left.at(c), left.at(a), c, a)}$$`,
        `${I1.v < 0 ? 'Negative, so the line is on top here; the area is its absolute value' : 'Positive, so \\(x^2\\) is on top here'}: \\(A_1 = ${T(A1.str())}\\).`,
        `Right piece \\([${c},${b}]\\):`, `$$${evalAt(left, b)}$$`, `$$${diffLine(left.at(b), left.at(c), b, c)}$$`,
        `${I2.v < 0 ? 'Negative, so the line is on top here; the area is its absolute value' : 'Positive, so \\(x^2\\) is on top here'}: \\(A_2 = ${T(A2.str())}\\).`,
        `$$A = A_1 + A_2 = ${eqs(sumStages([A1, A2]))}$$ (Integrating straight across would give \\(${T(net.str())}\\), which is wrong.)`],
      truth: () => Check.simpson(x => Math.abs(x * x - g.num(x)), a, c, 4000) + Check.simpson(x => Math.abs(x * x - g.num(x)), c, b, 4000) });
  }

  // ---------- 6.1 motion ----------
  function posFromV(r) {
    if (r.next() < 0.3) { // trig: classic +C trap
      const A = r.pick([2, 3, 4]), s0 = r.int(-3, 5), Tn = r.pick(['pi/2', 'pi', '3 pi/2']);
      const sExpr = `${s0 + A} - ${A} cos(t)`;
      const steps = [
        { id: 's', label: 'Position function \\(s(t)\\)', kind: 'expr', v: 't', lo: 0, hi: 4, ans: sExpr,
          mistakes: [{ ans: `-${A} cos(t) + ${s0}`, msg: `C is not just s(0): s(t) = −${A}cos t + C and s(0) = −${A} + C = ${s0}, so C = ${s0 + A}. cos 0 = 1, not 0.` }, { ans: `-${A} cos(t)`, msg: 'Add the constant: pick C so that s(0) matches the given starting position.' }, { ans: `${A} cos(t)`, msg: 'The antiderivative of sin t is −cos t.' }],
          hint: 'Antiderivative of v, plus C. Then solve s(0) = given value for C.' },
        { id: 'final', label: `\\(s(${T(Tn)})\\)`, kind: 'num', ans: `${s0 + A} - ${A} cos(${Tn})`, hint: 'Plug the time into your s(t).' },
      ];
      return finalize({ statement: `An object moves along a line with velocity \\(v(t) = ${A}\\sin t\\) and initial position \\(s(0) = ${s0}\\). Find its position function \\(s(t)\\) and its position at \\(t = ${T(Tn)}\\).`, steps, answer: steps[1].ans,
        solution: ['$$s(t) = \\int v(t)\\,dt + C$$', `$$s(t) = \\int ${A}\\sin t\\,dt = ${A}\\cdot(-\\cos t) + C = -${A}\\cos t + C$$`,
          `Use \\(s(0) = ${s0}\\) and \\(\\cos 0 = 1\\): $$s(0) = -${A}\\cdot 1 + C = -${A} + C = ${s0} \\;\\Rightarrow\\; C = ${s0} + ${A} = ${s0 + A}$$`,
          `$$s(t) = ${T(sExpr)}$$`,
          (() => { const cv = { 'pi/2': 0, 'pi': -1, '3 pi/2': 0 }[Tn], val = s0 + A - A * cv; return `Use \\(\\cos ${T(Tn)} = ${cv}\\): $$s(${T(Tn)}) = ${s0 + A} - ${A}\\cdot ${cv < 0 ? '(' + cv + ')' : cv} = ${s0 + A} - ${A * cv < 0 ? '(' + A * cv + ')' : A * cv} = ${val}$$`; })()],
        meta: { T: Check.evalNum(Tn), s0 }, truth: () => s0 + Check.simpson(t => A * Math.sin(t), 0, Check.evalNum(Tn), 2000) });
    }
    const v = GP.poly(...(r.bool() ? [r.pick([3, 6]), r.int(-6, 6), r.int(-5, 5)] : [r.int(1, 6), r.int(-8, 8)]));
    const s0 = r.int(-5, 10), Tn = r.int(1, 4);
    const S = v.integ().add(s0);
    const steps = [
      { id: 's', label: 'Position function \\(s(t)\\)', kind: 'expr', v: 't', lo: 0, hi: Tn, ans: S.str('t'),
        mistakes: [...(s0 ? [{ ans: v.integ().str('t'), msg: `Missing the constant: s(0) must equal ${s0}, so add ${s0}.` }] : []), { ans: v.deriv().str('t'), msg: 'That is the derivative (acceleration). Position is the antiderivative of velocity.' }],
        hint: 's(t) = s(0) + ∫₀ᵗ v(x) dx: antiderivative of v, then choose C so s(0) is right.' },
      { id: 'final', label: `Position at \\(t = ${Tn}\\)`, kind: 'num', ans: S.at(Tn).str(),
        mistakes: [...(s0 ? [{ ans: S.at(Tn).sub(s0).str(), msg: `That is the displacement. Position = s(0) + displacement = ${s0} + that.` }] : [])], hint: 'Plug t into s(t).' },
    ];
    return finalize({ statement: `An object moves along a line with velocity \\(v(t) = ${T(v.str('t'))}\\) (m/s) for \\(t \\ge 0\\), and \\(s(0) = ${s0}\\). Find the position function and the position at \\(t = ${Tn}\\).`, steps, answer: S.at(Tn).str(),
      solution: ['$$s(t) = \\int v(t)\\,dt + C,\\qquad C = s(0)$$', `Antiderivative of \\(v\\), one term at a time: $$${antiLine(v, 't')}$$`,
        `Add the constant so that \\(s(0) = ${s0}\\) (every \\(t\\) term is 0 at \\(t = 0\\), so \\(C = ${s0}\\)):`,
        `$$s(t) = ${T(v.integ().str('t'))} ${s0 < 0 ? '- ' + -s0 : '+ ' + s0} = ${T(S.str('t'))}$$`, `$$${evalAt(S, Tn, 's')}\\ \\text{m}$$`],
      meta: { T: Tn, s0 }, truth: () => s0 + Check.simpson(t => v.num(t), 0, Tn, 400) });
  }
  function posFromA(r) {
    const aQ = r.bool() ? GP.k(r.pick([q(-10), dec(-9.8), q(-4), q(2), q(6)])) : GP.poly(r.int(1, 4) * 2, r.pick([-4, -2, 1, 3]));
    const a = aQ;
    const v0 = r.int(-5, 20), s0 = r.int(0, 30), Tn = r.int(1, 4);
    const V = aQ.integ().add(v0), S = V.integ().add(s0);
    const steps = [
      { id: 'v', label: 'Velocity \\(v(t)\\)', kind: 'expr', v: 't', lo: 0, hi: Tn, ans: V.str('t'), mistakes: v0 ? [{ ans: aQ.integ().str('t'), msg: `Missing v(0): add ${v0} so that v(0) = ${v0}.` }] : [], hint: 'v(t) = v(0) + ∫ a.' },
      { id: 's', label: 'Position \\(s(t)\\)', kind: 'expr', v: 't', lo: 0, hi: Tn, ans: S.str('t'), mistakes: s0 ? [{ ans: V.integ().str('t'), msg: `Missing s(0): add ${s0}.` }] : [], hint: 's(t) = s(0) + ∫ v. Integrate your whole v(t), including the v(0) term (it becomes v(0)·t).' },
      { id: 'final', label: `Position at \\(t = ${Tn}\\)`, kind: 'num', ans: S.at(Tn).str(), hint: 'Plug t into s(t).' },
    ];
    return finalize({ statement: `An object has acceleration \\(a(t) = ${T(aQ.str('t'))}\\) (m/s²), initial velocity \\(v(0) = ${v0}\\) and initial position \\(s(0) = ${s0}\\). Find \\(v(t)\\), \\(s(t)\\), and the position at \\(t = ${Tn}\\).`, steps, answer: S.at(Tn).str(),
      solution: ['$$v(t) = \\int a(t)\\,dt + C,\\qquad C = v(0)$$', `Velocity: antiderivative of \\(a\\), one term at a time: $$${antiLine(aQ, 't')}$$`,
        `Every \\(t\\) term is 0 at \\(t = 0\\), so the constant is \\(v(0) = ${v0}\\): $$v(t) = ${T(V.str('t'))}$$`,
        '$$s(t) = \\int v(t)\\,dt + C,\\qquad C = s(0)$$', `Position: antiderivative of \\(v\\), one term at a time: $$${antiLine(V, 't')}$$`,
        `The constant is \\(s(0) = ${s0}\\): $$s(t) = ${T(S.str('t'))}$$`, `$$${evalAt(S, Tn, 's')}\\ \\text{m}$$`],
      meta: { T: Tn, s0 }, truth: () => { let s = s0, vv = v0; const n = 20000, h = Tn / n; for (let i = 0; i < n; i++) { const t = i * h; const k1 = a.num(t), k2 = a.num(t + h / 2); s += h * (vv + h / 2 * k1); vv += h * k2; } return s; } });
  }
  function dispDist(r) {
    if (r.next() < 0.2) {
      const A = r.pick([1, 2, 3]);
      const steps = [
        { id: 'z', label: 'Time in \\((0, \\pi)\\) where \\(v\\) changes sign', kind: 'num', ans: 'pi/2', hint: 'cos t = 0.' },
        { id: 'disp', label: 'Displacement on \\([0,\\pi]\\)', kind: 'num', ans: '0', hint: 'Integrate v straight across.' },
        { id: 'final', label: 'Distance traveled on \\([0,\\pi]\\)', kind: 'num', ans: `${2 * A}`, mistakes: [{ ans: '0', msg: 'That is the displacement. Distance integrates |v|: split at t = π/2 and add the absolute values.' }], hint: 'Split at the sign change; add |each piece|.' },
      ];
      return finalize({ statement: `An object moves with velocity \\(v(t) = ${A === 1 ? '' : A}\\cos t\\) on \\([0, \\pi]\\). Find the displacement and the total distance traveled.`, steps, answer: `${2 * A}`,
        solution: [`\\(\\cos t = 0\\) at \\(t = \\frac{\\pi}{2}\\): \\(v > 0\\) before it, \\(v < 0\\) after it. Antiderivative: \\(\\int ${A === 1 ? '' : A}\\cos t\\,dt = ${A === 1 ? '' : A}\\sin t\\). Values: \\(\\sin 0 = 0,\\ \\sin\\frac{\\pi}{2} = 1,\\ \\sin\\pi = 0\\).`,
          '$$\\text{displacement} = \\int_0^T v(t)\\,dt,\\qquad \\text{distance} = \\int_0^T |v(t)|\\,dt$$',
          `$$\\text{displacement} = \\Big[${A === 1 ? '' : A}\\sin t\\Big]_0^{\\pi} = ${A}\\cdot 0 - ${A}\\cdot 0 = 0$$`,
          `$$\\int_0^{\\pi/2} ${A === 1 ? '' : A}\\cos t\\,dt = ${A}\\cdot 1 - ${A}\\cdot 0 = ${A},\\qquad \\int_{\\pi/2}^{\\pi} ${A === 1 ? '' : A}\\cos t\\,dt = ${A}\\cdot 0 - ${A}\\cdot 1 = -${A}$$`,
          `$$\\text{distance} = |${A}| + |-${A}| = ${A} + ${A} = ${2 * A}$$`],
        truth: () => Check.simpson(t => Math.abs(A * Math.cos(t)), 0, Math.PI / 2, 2000) + Check.simpson(t => Math.abs(A * Math.cos(t)), Math.PI / 2, Math.PI, 2000) });
    }
    const two = r.bool();
    const r1 = r.int(1, 3), r2 = two ? r1 + r.int(1, 2) : -r.int(1, 3), Tn = (two ? r2 : r1) + r.int(1, 2), c = r.pick([1, 2, 3]) * (r.bool() ? 1 : -1);
    const v = GP.poly(1, -(r1 + r2), r1 * r2).scale(c);
    const F = v.integ(), roots = two ? [r1, r2] : [r1];
    const pts = [0, ...roots, Tn];
    let dist = q(0); const pieces = [];
    for (let i = 0; i < pts.length - 1; i++) { const I = F.at(pts[i + 1]).sub(F.at(pts[i])); pieces.push(I); dist = dist.add(I.v < 0 ? I.neg() : I); }
    const disp = F.at(Tn).sub(F.at(0));
    const steps = roots.map((z, i) => ({ id: 'z' + i, label: roots.length > 1 ? `${i ? 'Second' : 'First'} time in \\((0, ${Tn})\\) where \\(v = 0\\)` : `Time in \\((0, ${Tn})\\) where \\(v = 0\\)`, kind: 'num', ans: `${z}`, hint: 'Factor v(t) and keep roots inside the interval.' }));
    steps.push({ id: 'disp', label: `Displacement on \\([0, ${Tn}]\\)`, kind: 'num', ans: disp.str(), mistakes: [{ ans: dist.str(), msg: 'That is the distance. Displacement keeps signs: just integrate v from 0 to T.' }], hint: 'Integrate v(t) straight from 0 to T (no absolute values).' });
    steps.push({ id: 'final', label: `Total distance traveled on \\([0, ${Tn}]\\)`, kind: 'num', ans: dist.str(), mistakes: [{ ans: disp.str(), msg: 'That is the displacement. Distance = ∫|v| dt: split where v = 0 and add the absolute value of each piece.' }, { ans: (disp.v < 0 ? disp.neg() : disp).str(), msg: '|displacement| is not distance: backward motion cancels forward motion in it. Split at each zero of v and add |each piece|.' }], hint: 'Split at the zeros of v; add the absolute value of each piece.' });
    return finalize({ statement: `An object moves along a line with velocity \\(v(t) = ${T(v.str('t'))}\\) (m/s). Find the displacement and the total distance traveled on \\([0, ${Tn}]\\).`, steps, answer: dist.str(),
      solution: [`\\(v(t) = ${c === 1 ? '' : c === -1 ? '-' : c}(t - ${r1})(t ${r2 < 0 ? '+ ' + -r2 : '- ' + r2})\\) is zero at \\(t = ${roots.join(', ')}\\) inside the interval, so the motion changes direction there.`,
        `Check the factoring by multiplying out: $$${mulGP(GP.poly(1, -r1), GP.poly(1, -r2), 't')}$$${c === 1 ? '' : `$$${c}\\cdot\\left(${gpT(GP.poly(1, -(r1 + r2), r1 * r2), 't')}\\right) = ${gpT(v, 't')} = v(t)$$`}`,
        `Antiderivative of \\(v\\), one term at a time: $$F(t) = ${antiLine(v, 't')}$$`,
        `F at every split point:`, ...[...new Set(pts)].map(x => `$$${evalAt(F, x)}$$`),
        `Displacement keeps signs, straight from 0 to ${Tn}:`, '$$\\text{displacement} = \\int_0^T v(t)\\,dt = F(T) - F(0)$$', `$$\\text{displacement} = ${diffLine(F.at(Tn), F.at(0), Tn, 0)}\\ \\text{m}$$`,
        `Distance: one piece between each pair of split points.`, '$$\\text{distance} = \\int_0^T |v(t)|\\,dt = \\sum \\left|\\int_{t_i}^{t_{i+1}} v(t)\\,dt\\right|$$', ...pieces.map((p, i) => `$$\\int_{${pts[i]}}^{${pts[i + 1]}} v\\,dt = ${diffLine(F.at(pts[i + 1]), F.at(pts[i]), pts[i + 1], pts[i])}$$`),
        `$$\\text{distance} = ${pieces.map(p => `\\left|${tq(p)}\\right|`).join(' + ')} = ${eqs(sumStages(pieces.map(p => p.v < 0 ? p.neg() : p)))}\\ \\text{m}$$`],
      truth: () => { let d = 0; const n = 60000, h = Tn / n; for (let i = 1; i <= n; i++) { const t = i * h; d += Math.abs(Check.simpson(x => v.num(x), (i - 1) * h, t, 2)); } return d; } });
  }

  // ---------- 6.5 arc length ----------
  function sqrtSimp(m) { let out = 1, inn = m; for (let f = 2; f * f <= inn; f++) while (inn % (f * f) === 0) { inn /= f * f; out *= f; } return [out, inn]; }
  function arcLength(r, v = 'x') {
    const kind = r.pick(v === 'x' ? ['p32', 'p32', 'sq1', 'sq2', 'sq3', 'cosh', 'line', 'lnsq'] : ['p32', 'sq1', 'sq3']);
    const w = v === 'x' ? 'y' : 'x';
    const d = `d${v}`;
    let fE, dE, oneE, integrand, F, A, B, ansS, work, mistakesInt = [], antiE, truthF;
    if (kind === 'p32') {
      const m = r.pick([1, 4, 8, 9, 2, 3, 12]);
      const [so, si] = sqrtSimp(m);
      const sq = si === 1 ? `${so}` : (so === 1 ? `sqrt(${si})` : `${so} sqrt(${si})`); // sqrt(m)
      const cq = new Q(2 * so, 3);
      const lead = si === 1 ? (cq.d === 1 ? `${cq.n} ${v}^(3/2)` : `${cq.n} ${v}^(3/2) / 3`) : `${2 * so} sqrt(${si}) ${v}^(3/2) / 3`;
      const shift = r.int(-2, 3);
      const goodX = []; for (let s = 1; s <= 9; s++) { const x = new Q(s * s - 1, m); if (x.v <= 4) goodX.push(x); }
      A = r.pick(goodX.filter(x => x.v < 2)); B = r.pick(goodX.filter(x => x.v > A.v));
      if (r.next() < 0.3) { A = q(0); B = q(r.int(1, 4)); }
      fE = `${lead}${shift ? (shift > 0 ? ' + ' + shift : ' - ' + -shift) : ''}`;
      dE = sq === '1' ? `sqrt(${v})` : `${sq} sqrt(${v})`;
      oneE = `1 + ${m === 1 ? '' : m + ' '}${v}`;
      integrand = `sqrt(${oneE})`;
      antiE = `2 / ${3 * m} * (${oneE})^(3/2)`;
      const U1 = q(1).add(A.mul(m)), U2 = q(1).add(B.mul(m));
      const p = u => { try { return powQ(u, new Q(3, 2)).str(); } catch (e) { return `${u.pstr()}^(3/2)`; } };
      ansS = `2 / ${3 * m} * (${p(U2)} - ${p(U1)})`;
      try { ansS = powQ(U2, new Q(3, 2)).sub(powQ(U1, new Q(3, 2))).mul(new Q(2, 3 * m)).str(); } catch (e) { }
      mistakesInt = [{ ans: `sqrt(1 + ${dE})`, msg: "Square f' before adding 1: √(1 + (f')²)." }, { ans: `sqrt(${m} ${v})`, msg: "You lost the 1: it's √(1 + (f')²)." }];
      const sqT = T(sq), p32 = u => { try { const r = powQ(u, new Q(1, 2)); return `(\\sqrt{${tq(u)}})^3 = ${tqp(r)}^3 = ${tq(powQ(u, new Q(3, 2)))}`; } catch (e) { return `${tqp(u)}^{3/2}`; } };
      work = [`The constant ${shift ? `\\(${shift}\\)` : ''} drops out; power rule on the \\(${v}^{3/2}\\) term:`,
        `$$${w}' = \\frac{2${sq === '1' ? '' : sqT}}{3}\\cdot\\frac{3}{2}\\,${v}^{1/2} = ${sq === '1' ? '' : sqT}\\sqrt{${v}}$$`,
        `$$(${w}')^2 = ${sq === '1' ? '' : `(${sqT})^2`}(\\sqrt{${v}})^2 = ${m === 1 ? '' : m}${v},\\qquad 1 + (${w}')^2 = ${T(oneE)}$$`,
        `$$L = \\int_{${tq(A)}}^{${tq(B)}} \\sqrt{${T(oneE)}}\\,${d}$$`,
        '$$\\int u^{1/2}\\,du = \\frac{2}{3}u^{3/2}$$', `Substitute \\(u = ${T(oneE)}\\), \\(du = ${m}\\,${d}\\), so \\(${d} = \\frac{du}{${m}}\\). New bounds:`,
        `$$${[A, B].map(x => `u(${tq(x)}) = ${eqs([`1 + ${m}\\cdot ${tqp(x)}`, ...sumStages([q(1), x.mul(m)])])}`).join(',\\qquad ')}$$`,
        `$$L = \\frac{1}{${m}}\\int_{${tq(U1)}}^{${tq(U2)}} u^{1/2}\\,du = \\frac{1}{${m}}\\cdot\\frac{2}{3}\\Big[u^{3/2}\\Big]_{${tq(U1)}}^{${tq(U2)}} = \\frac{2}{${3 * m}}\\Big[u^{3/2}\\Big]_{${tq(U1)}}^{${tq(U2)}}$$`,
        `$$${tqp(U2)}^{3/2} = ${p32(U2)},\\qquad ${tqp(U1)}^{3/2} = ${p32(U1)}$$`,
        (() => { try { const a3 = powQ(U2, new Q(3, 2)), b3 = powQ(U1, new Q(3, 2)), df = a3.sub(b3); return `$$L = \\frac{2}{${3 * m}}\\left(${tq(a3)} - ${tqp(b3)}\\right) = \\frac{2}{${3 * m}}\\cdot ${tqp(df)} = ${eqs(mulStages(new Q(2, 3 * m), df))}$$`; } catch (e) { return `$$L = ${T(ansS)}$$`; } })()];
      truthF = t => (2 * Math.sqrt(m) / 3) * Math.pow(t, 1.5) + shift;
    } else if (kind === 'line') {
      const m = r.pick([2, -3, 1, 3, -2, 4]), c0 = r.int(-3, 4);
      A = q(r.int(-3, 1)); B = A.add(r.int(2, 5));
      fE = `${m} ${v}${c0 ? (c0 > 0 ? ' + ' + c0 : ' - ' + -c0) : ''}`; dE = `${m}`; oneE = `${1 + m * m}`; integrand = `sqrt(${1 + m * m})`; antiE = `sqrt(${1 + m * m}) ${v}`;
      ansS = `${B.sub(A).str()} sqrt(${1 + m * m})`;
      const dl = B.sub(A).v, rise = dl * Math.abs(m);
      work = [`$$${w}' = ${m},\\qquad (${w}')^2 = ${m < 0 ? `(${m})` : m}^2 = ${m * m},\\qquad 1 + (${w}')^2 = 1 + ${m * m} = ${1 + m * m}$$`,
        `The integrand \\(\\sqrt{${1 + m * m}}\\) is a constant, so its antiderivative is \\(\\sqrt{${1 + m * m}}\\,${v}\\):`,
        `$$L = \\int_{${tq(A)}}^{${tq(B)}} \\sqrt{${1 + m * m}}\\,${d} = \\sqrt{${1 + m * m}}\\,\\big(${tq(B)} - ${tqp(A)}\\big) = \\sqrt{${1 + m * m}}\\cdot ${dl} = ${T(ansS)}$$`,
        `Check with the distance formula: run \\(${dl}\\), rise \\(${dl}\\cdot ${Math.abs(m)} = ${rise}\\): $$\\sqrt{${dl}^2 + ${rise}^2} = \\sqrt{${dl * dl} + ${rise * rise}} = \\sqrt{${dl * dl + rise * rise}} = ${T(ansS)}\\ \\checkmark$$`];
      mistakesInt = [{ ans: `sqrt(${1 + Math.abs(m)})`, msg: "Square the slope: 1 + m², not 1 + m." }];
      truthF = t => m * t + c0;
    } else if (kind === 'cosh') {
      const lo = r.pick([0, -1, -2]), hi = r.pick([1, 2, 3]); // bounds ±ln(n)
      const bnd = n => n === 0 ? '0' : n < 0 ? `-ln(${-n + 1})` : `ln(${n + 1})`;
      const val = n => n === 0 ? q(0) : n < 0 ? new Q(-n + 1, 1).sub(new Q(1, -n + 1)).div(-2) : new Q(n + 1).sub(new Q(1, n + 1)).div(2);
      A = { str: () => bnd(lo), v: Check.evalNum(bnd(lo)) }; B = { str: () => bnd(hi), v: Check.evalNum(bnd(hi)) };
      fE = `(e^${v} + e^(-${v})) / 2`; dE = `(e^${v} - e^(-${v})) / 2`; oneE = `1 + ((e^${v} - e^(-${v})) / 2)^2`; integrand = `(e^${v} + e^(-${v})) / 2`; antiE = `(e^${v} - e^(-${v})) / 2`;
      ansS = val(hi).sub(val(lo)).str();
      const at = n => { if (n === 0) return `F(0) = \\frac{e^0 - e^0}{2} = \\frac{1 - 1}{2} = 0`; const k = Math.abs(n) + 1, s = n > 0 ? '' : '-', [p, m2] = n > 0 ? [`${k}`, `\\frac{1}{${k}}`] : [`\\frac{1}{${k}}`, `${k}`];
        return `F(${s}\\ln ${k}) = \\frac{e^{${s}\\ln ${k}} - e^{${n > 0 ? '-' : ''}\\ln ${k}}}{2} = \\frac{${p} - ${m2}}{2} = \\frac{${tq(n > 0 ? new Q(k * k - 1, k) : new Q(1 - k * k, k))}}{2} = ${tq(val(n))}`; };
      work = [`$$${w}' = \\frac{e^${v} - e^{-${v}}}{2},\\qquad (${w}')^2 = \\frac{e^{2${v}} - 2e^${v}e^{-${v}} + e^{-2${v}}}{4} = \\frac{e^{2${v}} - 2 + e^{-2${v}}}{4}$$`,
        `$$1 + (${w}')^2 = \\frac{4 + e^{2${v}} - 2 + e^{-2${v}}}{4} = \\frac{e^{2${v}} + 2 + e^{-2${v}}}{4} = \\left(\\frac{e^${v} + e^{-${v}}}{2}\\right)^2$$`,
        `So the square root is \\(\\frac{e^${v} + e^{-${v}}}{2}\\), with antiderivative \\(F(${v}) = \\frac{e^${v} - e^{-${v}}}{2}\\). Use \\(e^{\\ln k} = k\\) and \\(e^{-\\ln k} = \\frac1k\\):`,
        `$$${at(hi)}$$`, `$$${at(lo)}$$`,
        `$$L = ${eqs([`${tq(val(hi))} - ${tqp(val(lo))}`, ...sumStages([val(hi), val(lo).neg()])])}$$`];
      truthF = t => (Math.exp(t) + Math.exp(-t)) / 2;
    } else if (kind === 'lnsq') {
      A = q(1); const bb = r.pick([2, 3, 4, 'e']); B = bb === 'e' ? { str: () => 'e', v: Math.E } : q(bb);
      fE = `${v}^2 / 4 - ln(${v}) / 2`; dE = `${v} / 2 - 1 / (2 ${v})`; oneE = `1 + (${v} / 2 - 1 / (2 ${v}))^2`; integrand = `${v} / 2 + 1 / (2 ${v})`; antiE = `${v}^2 / 4 + ln(${v}) / 2`;
      ansS = bb === 'e' ? '(e^2 + 1) / 4' : `${new Q(bb * bb - 1, 4).str()} + ln(${bb}) / 2`;
      work = [`$$${w}' = \\frac{2${v}}{4} - \\frac{1}{2}\\cdot\\frac{1}{${v}} = \\frac{${v}}{2} - \\frac{1}{2${v}}$$`,
        `$$(${w}')^2 = \\frac{${v}^2}{4} - 2\\cdot\\frac{${v}}{2}\\cdot\\frac{1}{2${v}} + \\frac{1}{4${v}^2} = \\frac{${v}^2}{4} - \\frac{1}{2} + \\frac{1}{4${v}^2}$$`,
        `$$1 + (${w}')^2 = \\frac{${v}^2}{4} + \\frac{1}{2} + \\frac{1}{4${v}^2} = \\left(\\frac{${v}}{2} + \\frac{1}{2${v}}\\right)^2$$`,
        `So the integrand is \\(\\frac{${v}}{2} + \\frac{1}{2${v}}\\), with antiderivative \\(F(${v}) = \\frac{${v}^2}{4} + \\frac{\\ln ${v}}{2}\\) (\\(\\ln 1 = 0\\)${bb === 'e' ? ', \\(\\ln e = 1\\)' : ''}):`,
        `$$F(${bb}) = \\frac{${bb}^2}{4} + \\frac{\\ln ${bb}}{2}${bb === 'e' ? ' = \\frac{e^2}{4} + \\frac{1}{2}' : ` = \\frac{${bb * bb}}{4} + \\frac{\\ln ${bb}}{2}`},\\qquad F(1) = \\frac{1^2}{4} + \\frac{\\ln 1}{2} = \\frac{1}{4} + 0 = \\frac{1}{4}$$`,
        bb === 'e' ? `$$L = \\frac{e^2}{4} + \\frac{1}{2} - \\frac{1}{4} = \\frac{e^2}{4} + \\frac{2}{4} - \\frac{1}{4} = \\frac{e^2}{4} + \\frac{1}{4} = \\frac{e^2 + 1}{4}$$`
          : `$$L = \\frac{${bb * bb}}{4} - \\frac{1}{4} + \\frac{\\ln ${bb}}{2} = \\frac{${bb * bb} - 1}{4} + \\frac{\\ln ${bb}}{2} = ${T(ansS)}$$`];
      truthF = t => t * t / 4 - Math.log(t) / 2;
    } else { // perfect-square families: f' = P - N with 4PN = 1, integrand P + N
      const fam = { sq1: [GP.x(3, new Q(1, 6)), GP.x(-1, new Q(1, 2))], sq2: [GP.x(4, new Q(1, 8)), GP.x(-2, new Q(1, 4))], sq3: [GP.x(3, new Q(1, 3)), GP.x(-1, new Q(1, 4))] }[kind];
      const f = fam[0].add(fam[1]), fp = f.deriv();
      const P = new GP(fp.t.filter(t => t.c.v > 0)), N = new GP(fp.t.filter(t => t.c.v < 0)).neg();
      const G = P.add(N);
      A = q(r.int(1, 2)); B = A.add(r.int(1, 2));
      fE = f.str(v); dE = fp.str(v); oneE = `1 + (${fp.str(v)})^2`; integrand = G.str(v); antiE = G.integ().str(v);
      ansS = G.integ().at(B).sub(G.integ().at(A)).str();
      const Fi = G.integ(), sq1 = GP.k(1).add(fp.sq());
      work = [`Derivative, one term at a time: $$${w}' = ${derivLine(f, v)}$$`,
        `Square it, every term: $$(${w}')^2 = ${mulGP(fp, fp, v)}$$`,
        `$$1 + (${w}')^2 = ${eqs([`1 + ${gpP(fp.sq(), v)}`, gpT(sq1, v)])}$$`,
        `That is a perfect square (only the middle sign flips): $$${mulGP(G, G, v)}\\ \\checkmark$$ so \\(\\sqrt{1 + (${w}')^2} = ${gpT(G, v)}\\).`,
        `Antiderivative, one term at a time: $$F(${v}) = ${antiLine(G, v)}$$`,
        `$$${evalAt(Fi, B)}$$`, `$$${evalAt(Fi, A)}$$`, `$$L = ${diffLine(Fi.at(B), Fi.at(A), B, A)}$$`];
      mistakesInt = [{ ans: `sqrt(1 + ${fp.str(v)})`, msg: "Square f' before adding 1." }, { ans: fp.str(v), msg: "1 + (f')² is a perfect square of the SUM: (P + N)², not the difference. The √ gives P + N." }];
      truthF = t => f.num(t);
    }
    const at = { cosh: 3, lnsq: 4, sq1: 4, sq2: 4, sq3: 4 }[kind];
    if (at) work.splice(at, 0, `$$L = \\int_{${T(A.str())}}^{${T(B.str())}} ${T(integrand)}\\,${d}$$`);
    const power = `\\frac{d}{d${v}}\\left(c\\,${v}^n\\right) = c\\,n\\,${v}^{n-1}`;
    work.unshift(`$$L = \\int_a^b \\sqrt{1 + (${w}')^2}\\,${d}$$`, `$$${{ line: `\\frac{d}{d${v}}(m${v} + c) = m`, cosh: `\\frac{d}{d${v}}e^{${v}} = e^{${v}},\\qquad \\frac{d}{d${v}}e^{-${v}} = -e^{-${v}}`, lnsq: `${power},\\qquad \\frac{d}{d${v}}\\ln ${v} = \\frac{1}{${v}}` }[kind] || power}$$`);
    const lo = Math.min(A.v, B.v), hi = Math.max(A.v, B.v);
    const steps = [
      { id: 'd', label: `\\(${w}' = \\dfrac{d${w}}{${d}}\\)`, kind: 'expr', v, lo, hi, ans: dE, mistakes: [], hint: 'Differentiate the curve. Constants vanish; x^(3/2) → (3/2)x^(1/2).' },
      { id: 'one', label: `\\(1 + (${w}')^2\\) (simplified or not)`, kind: 'expr', v, lo, hi, ans: oneE, mistakes: [{ ans: `(${dE})^2`, msg: "You forgot the 1 +." }, { ans: `1 + ${pr(dE)}`, msg: "Square the derivative." }, { ans: `1 + (${fE})^2`, msg: `Use the derivative ${w}', not ${w} itself.` }], hint: "Square the whole derivative, then add 1." },
      { id: 'integrand', label: `Integrand: \\(L = \\int_a^b (\\;?\\;)\\,${d}\\)`, kind: 'expr', v, lo, hi, ans: integrand, mistakes: [...mistakesInt, { ans: oneE, msg: 'Take the square root: √(1 + (f\')²).' }], hint: "√(1 + (f')²). Look for a perfect square or a u-substitution." },
      { id: 'anti', label: `Antiderivative of the integrand (any + C)`, kind: 'anti', v, lo, hi, integrand, ans: antiE, hint: kind === 'p32' ? 'u = 1 + m·x, du = m dx, so ∫√u du/m = (2/(3m))u^{3/2}.' : 'Integrate term by term.' },
      { id: 'final', label: 'Arc length \\(L\\)', kind: 'num', ans: ansS, mistakes: [], hint: 'Evaluate F(b) − F(a).' },
    ];
    const lead = `${w} = ${T(fE)}`;
    return finalize({
      statement: `Find the length of the curve \\(${lead}\\) on \\([${T(A.str())}, ${T(B.str())}]\\)${v === 'y' ? ' (here \\(x\\) is a function of \\(y\\): integrate \\(dy\\))' : ''}.`,
      steps, answer: ansS,
      solution: [...work, `$$L = ${T(ansS)} \\approx ${fmt(Check.evalNum(ansS))}$$`],
      truth: () => { let s = 0; const n = 200000, h = (hi - lo) / n; let py = truthF(lo); for (let i = 1; i <= n; i++) { const t = lo + i * h, yv = truthF(t); s += Math.hypot(h, yv - py); py = yv; } return s; },
      curve: truthF, fE, dE, oneE, integrandE: integrand, v,
    });
  }
  function arcSetup(r) {
    const opts = [
      { f: 'x^3 + 2', d: '3 x^2', s: '9 x^4', i: 'sqrt(1 + 9 x^4)', a: -2, b: 5, g: x => x ** 3 + 2 },
      { f: '2 cos(3 x)', d: '-6 sin(3 x)', s: '36 sin(3 x)^2', i: 'sqrt(1 + 36 sin(3 x)^2)', a: '-pi', b: 'pi', g: x => 2 * Math.cos(3 * x) },
      { f: 'e^(-2 x)', d: '-2 e^(-2 x)', s: '4 e^(-4 x)', i: 'sqrt(1 + 4 e^(-4 x))', a: 0, b: 2, g: x => Math.exp(-2 * x) },
      { f: 'ln(x)', d: '1 / x', s: '1 / x^2', i: 'sqrt(1 + 1 / x^2)', a: 1, b: 10, g: Math.log },
      { f: 'x^2', d: '2 x', s: '4 x^2', i: 'sqrt(1 + 4 x^2)', a: 0, b: r.int(1, 3), g: x => x * x },
      { f: 'sin(x)', d: 'cos(x)', s: 'cos(x)^2', i: 'sqrt(1 + cos(x)^2)', a: 0, b: 'pi', g: Math.sin },
      (k => ({ f: `${k} x^2 - 1`, d: `${2 * k} x`, s: `${4 * k * k} x^2`, i: `sqrt(1 + ${4 * k * k} x^2)`, a: 0, b: 1, g: x => k * x * x - 1 }))(r.int(2, 4)),
      { f: 'tan(x)', d: 'sec(x)^2', s: 'sec(x)^4', i: 'sqrt(1 + sec(x)^4)', a: 0, b: 'pi/4', g: Math.tan },
      { f: '1 / x', d: '-1 / x^2', s: '1 / x^4', i: 'sqrt(1 + 1 / x^4)', a: 1, b: r.int(2, 5), g: x => 1 / x },
    ];
    const o = r.pick(opts);
    const a = Check.evalNum(`${o.a}`), b = Check.evalNum(`${o.b}`);
    const steps = [
      { id: 'd', label: "\\(f'(x)\\)", kind: 'expr', v: 'x', lo: a, hi: b, ans: o.d, hint: 'Chain rule where needed.' },
      { id: 'integrand', label: 'Integrand: \\(L = \\int_a^b(\\;?\\;)\\,dx\\)', kind: 'expr', v: 'x', lo: a, hi: b, ans: o.i, mistakes: [{ ans: `sqrt(1 + ${pr(o.d)})`, msg: "Square f'." }, { ans: `1 + (${o.d})^2`, msg: 'Missing the square root.' }, { ans: `sqrt(1 + (${o.f})^2)`, msg: "Use f', not f." }], hint: "√(1 + (f')²), simplified." },
      { id: 'a', label: 'Lower limit', kind: 'num', ans: `${o.a}` }, { id: 'b', label: 'Upper limit', kind: 'num', ans: `${o.b}` },
    ];
    return finalize({ statement: `Write and simplify, but do not evaluate, an integral with respect to \\(x\\) that gives the length of \\(y = ${T(o.f)}\\) on \\([${T(String(o.a))}, ${T(String(o.b))}]\\).`, steps, answer: null,
      solution: ["$$L = \\int_a^b \\sqrt{1 + (f'(x))^2}\\,dx$$", (() => { const k = o.f.match(/^(\d+) x\^2 - 1$/); const w = { 'x^3 + 2': ['3x^2 + 0', '3^2(x^2)^2'], '2 cos(3 x)': ['2\\cdot(-\\sin 3x)\\cdot 3', '(-6)^2\\sin^2 3x'], 'e^(-2 x)': ['e^{-2x}\\cdot(-2)', '(-2)^2(e^{-2x})^2'], 'ln(x)': ['\\frac{1}{x}', '\\frac{1^2}{x^2}'], 'x^2': ['2x', '2^2x^2'], 'sin(x)': ['\\cos x', '\\cos^2 x'], 'tan(x)': ['\\sec^2 x', '(\\sec^2 x)^2'], '1 / x': ['(x^{-1})\' = -1\\cdot x^{-2}', '(-1)^2(x^{-2})^2'] }[o.f] || [`${k[1]}\\cdot 2x`, `${2 * k[1]}^2x^2`];
          return `Derivative (chain rule where needed), then square it: $$f'(x) = ${w[0]} = ${T(o.d)},\\qquad (f')^2 = ${w[1]} = ${T(o.s)}$$`; })(),
        `$$L = \\int_{${T(String(o.a))}}^{${T(String(o.b))}} \\sqrt{1 + (f')^2}\\,dx = \\int_{${T(String(o.a))}}^{${T(String(o.b))}} ${T(o.i)}\\,dx$$`,`(Numerically \\(L \\approx ${fmt(Check.simpson(x => Check.evalNum(o.i, { x }), a, b, 4000))}\\) with a calculator; not needed here.)`],
      setupOnly: { integrand: o.i, a, b, g: o.g, f: o.f, d: o.d } });
  }

  // ---------- 6.7 physical applications ----------
  const G_M = new Q(49, 5); // 9.8 m/s^2
  function spring(r) {
    const kind = r.pick(['force', 'lengths', 'work']);
    let k, a, b, statement, kSol, bMistakes = [], kMistakes = [], aMistakes = [];
    if (kind === 'force') {
      const Fn = r.pick([10, 12, 20, 30, 40, 50, 60]), dcm = r.pick([2, 4, 5, 10, 20]);
      k = new Q(Fn * 100, dcm); const ac = r.pick([0, 0, dcm]), bc = ac + r.pick([5, 10, 15, 20]);
      a = new Q(ac, 100); b = new Q(bc, 100);
      statement = `A force of ${Fn} N is required to hold a spring stretched ${dcm} cm beyond its natural length. How much work is required to stretch it from ${ac} cm to ${bc} cm beyond its natural length?`;
      kMistakes = [{ ans: new Q(Fn, dcm).str(), msg: 'Convert cm to m first: k = F/x with x in meters.' }];
      bMistakes = [{ ans: `${bc}`, msg: 'Use meters: 1 cm = 0.01 m.' }]; aMistakes = [{ ans: `${ac}`, msg: 'Use meters.' }];
      kSol = [`Convert to meters: \\(${dcm}\\text{ cm} = ${dcm} \\div 100 = ${dn(new Q(dcm, 100))}\\text{ m}\\).`, `$$F = kx \\;\\Rightarrow\\; k = \\frac{F}{x}$$`, `$$${Fn} = k\\cdot ${dn(new Q(dcm, 100))} \\;\\Rightarrow\\; k = \\frac{${Fn}}{${dn(new Q(dcm, 100))}} = ${dn(k)}\\ \\text{N/m}$$`, `Limits in meters: \\(${ac} \\div 100 = ${dn(a)}\\), \\(${bc} \\div 100 = ${dn(b)}\\).`];
    } else if (kind === 'lengths') {
      const L0 = r.pick([10, 12, 20, 25, 30]), L1 = L0 + r.pick([2, 4, 5, 10]), Fn = r.pick([20, 25, 30, 40, 50]);
      const L2 = L0 + r.pick([0, 2, 5]), L3 = L2 + r.pick([3, 5, 10]);
      k = new Q(Fn * 100, L1 - L0); a = new Q(L2 - L0, 100); b = new Q(L3 - L0, 100);
      statement = `A spring has natural length ${L0} cm. A force of ${Fn} N holds it at a length of ${L1} cm. How much work is done stretching it from a length of ${L2} cm to a length of ${L3} cm?`;
      kMistakes = [{ ans: new Q(Fn * 100, L1).str(), msg: `x is the stretch beyond natural length: ${L1} − ${L0} = ${L1 - L0} cm, not ${L1} cm.` }, { ans: new Q(Fn, L1 - L0).str(), msg: 'Convert cm to m first.' }];
      aMistakes = [{ ans: new Q(L2, 100).str(), msg: `x is measured from the natural length: ${L2} − ${L0} = ${L2 - L0} cm.` }];
      bMistakes = [{ ans: new Q(L3, 100).str(), msg: `x is measured from the natural length: ${L3} − ${L0} = ${L3 - L0} cm = ${(L3 - L0) / 100} m.` }, { ans: `${L3 - L0}`, msg: 'Use meters: 1 cm = 0.01 m.' }];
      kSol = [`$$x = \\text{length} - \\text{natural length}$$`, `Stretch beyond natural length: \\(${L1} - ${L0} = ${L1 - L0}\\text{ cm} = ${L1 - L0} \\div 100 = ${dn(new Q(L1 - L0, 100))}\\text{ m}\\).`, `$$F = kx \\;\\Rightarrow\\; k = \\frac{F}{x}$$`, `$$${Fn} = k\\cdot ${dn(new Q(L1 - L0, 100))} \\;\\Rightarrow\\; k = \\frac{${Fn}}{${dn(new Q(L1 - L0, 100))}} = ${dn(k)}\\ \\text{N/m}$$`, `Limits, measured from the natural length: \\(${L2} - ${L0} = ${L2 - L0}\\text{ cm} = ${dn(a)}\\text{ m}\\), \\(${L3} - ${L0} = ${L3 - L0}\\text{ cm} = ${dn(b)}\\text{ m}\\).`];
    } else {
      const W0 = r.pick([2, 3, 4, 6, 8, 9]), d0 = r.pick([new Q(1, 10), new Q(1, 5), new Q(1, 2), q(1)]);
      k = q(2 * W0).div(d0.mul(d0)); const extra = r.pick([new Q(1, 10), new Q(1, 5), new Q(1, 2)]);
      a = d0; b = d0.add(extra);
      statement = `It takes ${W0} J of work to stretch a spring ${d0.v} m from its natural length. How much work is needed to stretch it an additional ${extra.v} m?`;
      kMistakes = [{ ans: q(W0).div(d0).str(), msg: 'Work is not force: W = ∫₀ᵈ kx dx = kd²/2, so k = 2W/d².' }, { ans: q(W0).div(d0.mul(d0)).str(), msg: 'W = kd²/2, so k = 2W/d² (you lost the 2).' }];
      bMistakes = [{ ans: extra.str(), msg: `"Additional" means it starts already stretched ${d0.v} m and ends at ${b.v} m.` }];
      kSol = [`$$W = \\int_0^{d} kx\\,dx = \\frac{k}{2}d^2 \\;\\Rightarrow\\; k = \\frac{2W}{d^2}$$`, `$$${W0} = \\int_0^{${dn(d0)}} kx\\,dx = \\frac{k}{2}(${dn(d0)})^2 = \\frac{k}{2}\\cdot ${dn(d0.mul(d0))} \\;\\Rightarrow\\; k = \\frac{2\\cdot ${W0}}{${dn(d0.mul(d0))}} = \\frac{${2 * W0}}{${dn(d0.mul(d0))}} = ${dn(k)}\\ \\text{N/m}$$`, `$$b = d + \\text{additional}$$`, `It starts already stretched \\(${dn(a)}\\) m and goes an additional \\(${dn(extra)}\\) m: \\(${dn(a)} + ${dn(extra)} = ${dn(b)}\\) m.`];
    }
    const W = k.div(2).mul(b.mul(b).sub(a.mul(a)));
    const steps = [
      { id: 'k', label: 'Spring constant \\(k\\) (N/m)', kind: 'num', ans: k.str(), mistakes: kMistakes, hint: "Hooke's law F = kx, x in meters measured from the natural length." },
      { id: 'a', label: 'Lower limit \\(x\\) (m, from natural length)', kind: 'num', ans: a.str(), mistakes: aMistakes, hint: 'Starting stretch beyond natural length, in meters.' },
      { id: 'b', label: 'Upper limit \\(x\\) (m)', kind: 'num', ans: b.str(), mistakes: bMistakes, hint: 'Final stretch beyond natural length, in meters.' },
      { id: 'integrand', label: 'Integrand \\(F(x)\\) in \\(W = \\int_a^b F(x)\\,dx\\)', kind: 'expr', v: 'x', lo: a.v, hi: b.v, ans: `${k.str()} * x`, hint: 'Hooke: F(x) = kx.' },
      { id: 'final', label: 'Work \\(W\\) (J)', kind: 'num', ans: W.str(), mistakes: [{ ans: k.mul(b.mul(b).sub(a.mul(a))).str(), msg: 'You forgot the 1/2: ∫kx dx = kx²/2.' }, { ans: k.div(2).mul(b.sub(a).mul(b.sub(a))).str(), msg: 'It is (k/2)(b² − a²), not (k/2)(b − a)².' }], hint: 'W = (k/2)(b² − a²).' },
    ];
    return finalize({ statement, steps, answer: W.str(),
      solution: [...kSol, `$$W = \\int_a^b kx\\,dx = k\\Big[\\frac{x^2}{2}\\Big]_a^b = \\frac{k}{2}\\left(b^2 - a^2\\right)$$`, `$$W = \\int_{${dn(a)}}^{${dn(b)}} ${dn(k)}\\,x\\,dx = ${dn(k)}\\Big[\\frac{x^2}{2}\\Big]_{${dn(a)}}^{${dn(b)}} = \\frac{${dn(k)}}{2}\\left(${dn(b)}^2 - ${dn(a)}^2\\right)$$`, `$$b^2 = ${dn(b)}^2 = ${dn(b.mul(b))},\\qquad a^2 = ${dn(a)}^2 = ${dn(a.mul(a))},\\qquad b^2 - a^2 = ${dn(b.mul(b))} - ${dn(a.mul(a))} = ${dn(b.mul(b).sub(a.mul(a)))}$$`, `$$\\frac{${dn(k)}}{2} = ${dn(k.div(2))},\\qquad W = ${dn(k.div(2))} \\times ${dn(b.mul(b).sub(a.mul(a)))} = ${dn(W)}\\ \\text{J}$$`],
      truth: () => Check.simpson(x => k.v * x, a.v, b.v, 100) });
  }
  function chain(r) {
    const us = r.next() < 0.35;
    const L = us ? r.pick([20, 30, 40, 50, 60]) : r.pick([10, 15, 20, 25, 30]);
    const rho = us ? r.pick([new Q(1, 2), q(1), q(2), new Q(3, 2)]) : r.pick([q(1), q(2), q(3), new Q(5, 2), q(4)]);
    const delta = us ? rho : rho.mul(G_M); // weight per length
    const variant = r.pick(['all', 'half', 'load']);
    const unitW = us ? 'ft·lb' : 'J', unitL = us ? 'ft' : 'm';
    const obj = us ? 'rope' : 'chain';
    const what = us ? `A ${L}-ft ${obj} weighing ${rho.v} lb/ft` : `A ${L}-m ${obj} with density ${rho.v} kg/m`;
    const load = us ? r.pick([5, 10, 20]) : r.pick([5, 10, 20]);
    let statement, steps, W, sol;
    const intY = (top, name, L_ = 'L') => [`$$${name} = \\int_0^{${L_}} \\delta\\,y\\,dy = \\delta\\Big[\\frac{y^2}{2}\\Big]_0^{${L_}} = \\delta\\cdot\\frac{${L_ === 'L' ? 'L^2' : `\\left(${L_}\\right)^2`}}{2}$$`, `$$${name} = \\int_0^{${dn(top)}} ${dn(delta)}\\,y\\,dy = ${dn(delta)}\\Big[\\frac{y^2}{2}\\Big]_0^{${dn(top)}} = ${dn(delta)}\\cdot\\frac{${dn(top)}^2}{2}$$`,
      `$$${dn(top)}^2 = ${dn(top)} \\times ${dn(top)} = ${dn(top.mul(top))},\\qquad \\frac{${dn(top.mul(top))}}{2} = ${dn(top.mul(top).div(2))},\\qquad ${name} = ${dn(delta)} \\times ${dn(top.mul(top).div(2))} = ${dn(delta.mul(top.mul(top).div(2)))}\\ \\text{${unitW}}$$`];
    const deltaStep = { id: 'delta', label: `Weight per unit length (${us ? 'lb/ft' : 'N/m'})`, kind: 'num', ans: delta.str(), mistakes: us ? [] : [{ ans: rho.str(), msg: 'Mass is not weight: multiply kg/m by g = 9.8 m/s² to get N/m.' }], hint: us ? 'Already given as a weight per foot.' : 'Weight = mass × g: ρ·9.8.' };
    const integrandStep = { id: 'integrand', label: `Integrand: \\(W = \\int_0^{?} (\\;?\\;)\\,dy\\), \\(y\\) = distance of a slice below the top`, kind: 'expr', v: 'y', lo: 0, hi: L, ans: `${delta.str()} * y`, mistakes: [{ ans: `${delta.str()} * (${L} - y)`, msg: `With y measured down from the top, a slice at depth y is lifted y, not ${L} − y.` }, { ans: `${rho.str()} * y`, msg: 'Use weight per length (ρg), not mass per length.' }], hint: 'Each slice (weight δ dy) at depth y rises y.' };
    if (variant === 'all') {
      W = delta.mul(L * L).div(2);
      statement = `${what} hangs from the top of a tall building. How much work is required to pull the entire ${obj} to the top?`;
      steps = [deltaStep, integrandStep, { id: 'final', label: `Work (${unitW})`, kind: 'num', ans: W.str(), mistakes: [{ ans: delta.mul(L * L).str(), msg: 'Forgot the 1/2: ∫₀ᴸ δy dy = δL²/2.' }, { ans: delta.mul(L).str(), msg: 'Each slice rises a different distance, so integrate: δ∫₀ᴸ y dy.' }], hint: 'δ L²/2.' }];
      sol = intY(q(L), 'W');
    } else if (variant === 'half') {
      const hq = new Q(L, 2), h = hq.v;
      const Wtop = delta.mul(hq).mul(hq).div(2), Wbot = delta.mul(hq).mul(hq);
      W = Wtop.add(Wbot);
      statement = `${what} hangs from the top of a tall building. How much work is required to wind up the top half of the ${obj}? (Winding up the top half also lifts the bottom half by ${h} ${unitL}.)`;
      steps = [deltaStep,
        { id: 'top', label: `Work to wind the top half (${unitW})`, kind: 'num', ans: Wtop.str(), hint: `δ∫₀^${h} y dy.` },
        { id: 'bot', label: `Work to lift the bottom half ${h} ${unitL} (${unitW})`, kind: 'num', ans: Wbot.str(), mistakes: [{ ans: delta.mul(q(L * L).sub(hq.mul(hq))).div(2).str(), msg: `The bottom half does not reach the top; every bottom slice rises exactly ${h} ${unitL}: (weight of bottom half)(${h}).` }], hint: `Weight of bottom half = δ·${h}; it all rises ${h}.` },
        { id: 'final', label: `Total work (${unitW})`, kind: 'num', ans: W.str(), mistakes: [{ ans: Wtop.str(), msg: 'Add the work of raising the bottom half too.' }], hint: 'Add the two parts.' }];
      sol = [`Top half: each slice at depth \\(y\\) from 0 to \\(${L} \\div 2 = ${dn(hq)}\\) rises \\(y\\).`, ...intY(hq, 'W_{\\text{top}}', '\\frac{L}{2}'),
        `Bottom half: it all rises exactly \\(${dn(hq)}\\) ${unitL}. Its weight is \\(${dn(delta)} \\times ${dn(hq)} = ${dn(delta.mul(hq))}\\) ${us ? 'lb' : 'N'}.`,
        `$$W_{\\text{bottom}} = \\left(\\delta\\cdot\\frac{L}{2}\\right)\\cdot\\frac{L}{2}$$`, `$$W_{\\text{bottom}} = ${dn(delta.mul(hq))} \\times ${dn(hq)} = ${dn(Wbot)}\\ \\text{${unitW}}$$`,
        `$$W = W_{\\text{top}} + W_{\\text{bottom}} = ${dn(Wtop)} + ${dn(Wbot)} = ${dn(W)}\\ \\text{${unitW}}$$`];
    } else {
      const Wc = delta.mul(L * L).div(2), Wl = us ? q(load).mul(L) : q(load).mul(G_M).mul(L);
      W = Wc.add(Wl);
      statement = `${what} hangs from the top of a tall building with a ${us ? load + '-lb' : load + '-kg'} weight attached to its lower end. How much work is required to pull the ${obj} and the weight to the top?`;
      steps = [deltaStep, integrandStep,
        { id: 'chainW', label: `Work for the ${obj} alone (${unitW})`, kind: 'num', ans: Wc.str(), hint: 'δL²/2.' },
        { id: 'loadW', label: `Work for the weight alone (${unitW})`, kind: 'num', ans: Wl.str(), mistakes: us ? [] : [{ ans: q(load * L).str(), msg: 'Weight = mass × 9.8.' }], hint: `Constant force × ${L} ${unitL}.` },
        { id: 'final', label: `Total work (${unitW})`, kind: 'num', ans: W.str(), mistakes: [], hint: 'Add them.' }];
      sol = [`The ${obj}:`, ...intY(q(L), `W_{\\text{${obj}}}`),
        `The weight: ${us ? `\\(${load}\\) lb` : `\\(${load} \\times 9.8 = ${dn(q(load).mul(G_M))}\\) N`}, lifted the full \\(${L}\\) ${unitL}:`,
        `$$W_{\\text{load}} = ${us ? '(\\text{weight})' : 'mg'}\\cdot L$$`, `$$W_{\\text{load}} = ${dn(us ? q(load) : q(load).mul(G_M))} \\times ${L} = ${dn(Wl)}\\ \\text{${unitW}}$$`,
        `$$W = W_{\\text{${obj}}} + W_{\\text{load}} = ${dn(Wc)} + ${dn(Wl)} = ${dn(W)}\\ \\text{${unitW}}$$`];
    }
    if (!us) steps[steps.length - 1].mistakes.push({ ans: W.div(G_M).str(), msg: 'You left out g = 9.8.' });
    return finalize({ statement: statement + (us ? '' : ' Use g = 9.8 m/s².'), steps, answer: W.str(), solution: [`\\(L\\) = length, \\(\\delta\\) = weight per unit length, \\(y\\) = depth below the top.`, ...(us ? [`Weight per foot: \\(\\delta = ${dn(delta)}\\) lb/ft (already a weight).`] : ['Weight per meter:', '$$\\delta = \\rho g$$', `$$\\delta = ${dn(rho)} \\times 9.8 = ${dn(delta)}\\ \\text{N/m}$$`]),
        `Measure \\(y\\) down from the top. A slice at depth \\(y\\) has weight \\(${dn(delta)}\\,dy\\) and rises \\(y\\), so the integrand is \\(${dn(delta)}\\,y\\).`, ...sol],
      truth: () => { // brute-force: sum over slices of weight * rise
        const n = 20000, h = L / n; let s = 0;
        for (let i = 0; i < n; i++) { const y = (i + 0.5) * h; const rise = variant === 'half' ? Math.min(y, L / 2) : y; s += delta.v * h * rise; }
        if (variant === 'load') s += (us ? load : load * 9.8) * L;
        return s;
      } });
  }
  function pump(r) {
    const shape = r.pick(['cyl', 'box', 'cone', 'trough', 'hemi']);
    const us = r.next() < 0.25;
    const wd = us ? q(125, 2) : q(9800); // weight density: 62.5 lb/ft^3 or 1000*9.8 N/m^3
    const u = us ? 'ft' : 'm';
    let A, H, desc, AT, In, raw, areaMistakes = [], isPi = false, areaWork;
    if (shape === 'cyl') { const rad = r.pick([1, 2, 3, 4]); H = r.pick([2, 4, 5, 6, 8]); A = GP.k(rad * rad); isPi = true; AT = piT(q(rad * rad)); desc = `A cylindrical tank (standing upright) has radius ${rad} ${u} and height ${H} ${u}`; raw = y => Math.PI * rad * rad; areaWork = ['\\(r\\) = radius.', 'A(y) = \\pi r^2', `A(y) = \\pi\\cdot ${rad}^2 = ${rad * rad === 1 ? '' : rad * rad}\\pi`]; }
    else if (shape === 'box') { const l = r.pick([2, 3, 4, 5]), w = r.pick([2, 3, 4]); H = r.pick([2, 3, 4, 5]); A = GP.k(l * w); AT = `${l * w}`; desc = `A rectangular tank has a base ${l} ${u} by ${w} ${u} and height ${H} ${u}`; raw = () => l * w; areaWork = ['A(y) = \\text{length}\\times\\text{width}', `A(y) = ${l}\\times ${w} = ${l * w}`]; }
    else if (shape === 'cone') { const R0 = r.pick([1, 2, 3, 4]); H = r.pick([2, 3, 4, 6]); A = GP.x(2, new Q(R0 * R0, H * H)); isPi = true; In = ty(new Q(R0 * R0, H * H), 'y^2'); AT = ty(new Q(R0 * R0, H * H), '\\pi y^2'); desc = `A conical tank with its vertex pointing down has radius ${R0} ${u} at the top and height ${H} ${u}`; raw = y => Math.PI * (R0 * y / H) ** 2; areaWork = ['Similar triangles: \\(r\\) = slice radius at height \\(y\\), \\(R\\) = top radius, \\(H\\) = height.', '\\frac{r}{y} = \\frac{R}{H} \\;\\Rightarrow\\; r = \\frac{R}{H}\\,y', `\\frac{r}{y} = \\frac{${R0}}{${H}} \\;\\Rightarrow\\; r = ${eqs([`\\frac{${R0}}{${H}}\\,y`, ty(new Q(R0, H), 'y')])}`, 'A(y) = \\pi r^2 = \\pi\\left(\\frac{R}{H}\\,y\\right)^2', `A(y) = \\pi\\left(\\frac{${R0}}{${H}}y\\right)^2 = \\pi\\cdot\\frac{${R0}^2}{${H}^2}y^2 = \\pi\\cdot\\frac{${R0 * R0}}{${H * H}}y^2`]; areaMistakes = [{ ans: `${R0 * R0}`, msg: `The radius shrinks toward the vertex: by similar triangles r(y) = (${R0}/${H})y, so A = π r² uses that.` }]; }
    else if (shape === 'trough') { const len = r.pick([4, 5, 6, 10]), w = r.pick([2, 3, 4]); H = r.pick([1, 2, 3]); A = GP.x(1, new Q(len * w, H)); In = AT = ty(new Q(len * w, H), 'y'); desc = `A trough ${len} ${u} long has cross-sections that are isosceles triangles (vertex down) ${w} ${u} wide at the top and ${H} ${u} tall`; raw = y => len * w * y / H; areaWork = ['Similar triangles: \\(w\\) = slice width at height \\(y\\), \\(b\\) = top width, \\(H\\) = height, \\(\\ell\\) = length.', '\\frac{w}{y} = \\frac{b}{H} \\;\\Rightarrow\\; w = \\frac{b}{H}\\,y', `\\frac{w}{y} = \\frac{${w}}{${H}} \\;\\Rightarrow\\; w = ${eqs([`\\frac{${w}}{${H}}\\,y`, ty(new Q(w, H), 'y')])}`, 'A(y) = \\ell\\cdot w = \\ell\\cdot\\frac{b}{H}\\,y', `A(y) = ${len}\\cdot\\frac{${w}}{${H}}y = \\frac{${len}\\cdot ${w}}{${H}}y = \\frac{${len * w}}{${H}}y`]; areaMistakes = [{ ans: `${len * w}`, msg: `The width shrinks toward the bottom: w(y) = (${w}/${H})y, so A(y) = ${len}·w(y).` }]; }
    else { const R0 = r.pick([1, 2, 3, 4]); H = R0; A = GP.poly(-1, 2 * R0, 0); isPi = true; In = `(${2 * R0}y - y^2)`; AT = `\\pi${In}`; desc = `A hemispherical bowl (flat side up) has radius ${R0} ${u}`; raw = y => Math.PI * (R0 * R0 - (R0 - y) ** 2); areaWork = [`Pythagoras: \\(r\\) = slice radius at height \\(y\\), \\(R\\) = bowl radius; the center is at \\(y = R = ${R0}\\).`, 'r^2 = R^2 - (R - y)^2', `r^2 = ${R0}^2 - (${R0} - y)^2 = ${R0 * R0} - (${R0 * R0} - ${2 * R0}y + y^2) = ${2 * R0}y - y^2`, 'A(y) = \\pi r^2', `A(y) = \\pi(${2 * R0}y - y^2)`]; areaMistakes = [{ ans: `${R0 * R0}`, msg: `The circle radius depends on height: r² = ${R0}² − (${R0} − y)².` }]; }
    const depthFrac = r.pick([1, 1, new Q(1, 2)]), D = q(H).mul(depthFrac);
    const out = r.pick([0, 0, 1, 2]);
    const top = H + out;
    const lift = GP.poly(-1, top);
    const Gint = A.mul(lift);
    const filled = depthFrac === 1 || (depthFrac.eq && depthFrac.eq(1)) ? 'is full of water' : `is filled with water to a depth of ${D.v} ${u}`;
    const dest = out ? `to an outlet ${out} ${u} above the top of the tank` : 'out over the top of the tank';
    const Aexpr = isPi ? `pi * (${A.str('y')})` : A.str('y'), wdT = us ? '62.5' : '9800';
    const F = Gint.integ(), raw0 = F.at(D).sub(F.at(0)), val = raw0.mul(wd);
    const ans = isPi ? exactPi(val, true) : val.str();
    const steps = [
      { id: 'A', label: `Cross-sectional area \\(A(y)\\) of a horizontal slice at height \\(y\\) (from the bottom)`, kind: 'expr', v: 'y', lo: 0, hi: H, ans: Aexpr, mistakes: areaMistakes.map(m => ({ ...m, ans: isPi ? `pi * ${m.ans}` : m.ans })).concat(isPi ? [{ ans: A.str('y'), msg: 'A circle\'s area is πr²: include π.' }] : []), hint: 'Slice horizontally; area of that slice as a function of its height y.' },
      { id: 'lift', label: `Distance the slice at height \\(y\\) must be lifted`, kind: 'expr', v: 'y', lo: 0, hi: H, ans: `${top} - y`, mistakes: [{ ans: 'y', msg: `y is how high the slice already is. It must rise to ${top}: distance = ${top} − y.` }, ...(out ? [{ ans: GP.poly(-1, H).str('y'), msg: `The water goes to the outlet ${out} ${u} above the top, so it rises to ${top}, not ${H}.` }] : [])], hint: `It must reach height ${top}.` },
      { id: 'a', label: 'Lower limit (y)', kind: 'num', ans: '0', hint: 'Bottom of the water.' },
      { id: 'b', label: 'Upper limit (y)', kind: 'num', ans: D.str(), mistakes: D.eq(H) ? [] : [{ ans: `${H}`, msg: `Only the water moves: it goes up to ${D.v}, not the tank height.` }], hint: 'Top of the water surface.' },
      { id: 'final', label: `Work (${us ? 'ft·lb' : 'J'})`, kind: 'num', ans: ans, mistakes: [{ ans: isPi ? exactPi(raw0, true) : raw0.str(), msg: `Multiply by the weight density ${us ? '62.5 lb/ft³' : 'ρg = 1000·9.8 = 9800 N/m³'}.` }, ...(us ? [] : [{ ans: isPi ? exactPi(raw0.mul(1000), true) : raw0.mul(1000).str(), msg: 'Mass is not weight: use ρg = 9800, not ρ = 1000.' }])], hint: `W = ${us ? '62.5' : '9800'}∫ A(y)·(lift) dy.` },
    ];
    return finalize({
      statement: `${desc} and ${filled}. How much work is required to pump all of the water ${dest}? Use ${us ? 'a weight density of 62.5 lb/ft³' : 'ρ = 1000 kg/m³ and g = 9.8 m/s²'}; measure \\(y\\) up from the bottom of the tank.`,
      steps, answer: ans,
      solution: [us ? 'Weight density: \\(62.5\\) lb/ft³ (already a weight).' : 'Weight density: \\(\\rho g = 1000 \\times 9.8 = 9800\\) N/m³.',
        `Slice the water horizontally at height \\(y\\). Its area:`, ...areaWork.map((l, i) => l.includes('\\(') ? l : `$$${l}${i === areaWork.length - 1 && !(shape === 'cyl' || shape === 'box') ? ` = ${T(Aexpr)}` : ''}$$`),
        `The water must reach height \\(${out ? `${H} + ${out} = ${top}` : top}\\), so a slice at height \\(y\\) is lifted \\(${top} - y\\):`,
        '$$D(y) = (\\text{height it must reach}) - y$$', `$$D(y) = ${top} - y$$`,
        `The water runs from \\(y = 0\\) to \\(y = ${depthFrac === 1 ? H : `\\frac{1}{2}\\cdot ${H} = ${dn(D)}`}\\). Each slice: weight \\(${us ? '62.5' : '9800'}\\,A(y)\\,dy\\) times distance lifted.`,
        `$$W = \\int_a^b \\rho g\\,A(y)\\,D(y)\\,dy$$`, `$$W = \\int_0^{${dn(D)}} ${wdT}\\cdot ${AT}\\cdot (${top} - y)\\,dy$$`,
        ...(A.t[0].p.isZero() ? (() => { const K = wd.mul(A.t[0].c), KT = `${dn(K)}${isPi ? '\\pi' : ''}`; // constant area: it comes out front with rho g
          return [`Pull the constants out front: \\(${wdT}\\cdot ${AT}\\).`, ...(A.t[0].c.eq(1) ? [] : [`$$${wdT}\\times ${dn(A.t[0].c)} = ${dn(K)}$$`]), `$$W = ${wdT}\\cdot ${AT}\\int_0^{${dn(D)}} (${top} - y)\\,dy = ${KT}\\int_0^{${dn(D)}} (${top} - y)\\,dy$$`,
            ...integralSteps({ G: lift, v: 'y', a: q(0), b: D, factor: KT, factorQ: K, pi: isPi, what: 'W', unit: us ? 'ft·lb' : 'J', sym: 'W', dec: true, asc: true }).work]; })()
        : [`Pull the constants out front (\\(${wdT}\\)${isPi ? ' and \\(\\pi\\)' : ''}):`, `$$W = ${wdT}${isPi ? '\\pi' : ''}\\int_0^{${dn(D)}} ${In}\\,(${top} - y)\\,dy$$`,
          `Multiply out, every term: $$${eqs([`${In}\\,(${top} - y)`, jn(A.t.flatMap(t => [termT(t.c.mul(top), t.p, 'y'), termT(t.c.neg(), t.p.add(1), 'y')])), gpA(Gint, 'y')])}$$`,
          ...integralSteps({ G: Gint, v: 'y', a: q(0), b: D, factor: wdT + (isPi ? '\\pi' : ''), factorQ: wd, pi: isPi, what: 'W', unit: us ? 'ft·lb' : 'J', sym: 'W', dec: true, asc: true }).work])],
      truth: () => { const n = 20000, h = D.v / n; let s = 0; for (let i = 0; i < n; i++) { const y = (i + 0.5) * h; s += wd.v * raw(y) * h * (top - y); } return s; },
    });
  }
  function force(r) {
    const shape = r.pick(['rect', 'triDown', 'triUp', 'trap']);
    const us = r.next() < 0.25;
    const wd = us ? q(125, 2) : q(9800), u = us ? 'ft' : 'm';
    const Hp = r.pick([1, 2, 3, 4]), s = r.pick([0, 0, 1, 2]);
    const a = Hp + s; // water surface height, y measured up from bottom of the plate
    let w, desc, raw;
    if (shape === 'rect') { const W = r.pick([2, 3, 4, 5]); w = GP.k(W); desc = `a rectangular plate ${W} ${u} wide and ${Hp} ${u} tall`; raw = () => W; }
    else if (shape === 'triDown') { const B = r.pick([2, 4, 6]); w = GP.x(1, new Q(B, Hp)); desc = `an isosceles triangular plate with base ${B} ${u} on top and height ${Hp} ${u} (vertex pointing down)`; raw = y => B * y / Hp; }
    else if (shape === 'triUp') { const B = r.pick([2, 4, 6]); w = GP.poly(new Q(-B, Hp), B); desc = `an isosceles triangular plate with base ${B} ${u} on the bottom and height ${Hp} ${u} (vertex pointing up)`; raw = y => B * (1 - y / Hp); }
    else { const b1 = r.pick([2, 4]), b2 = b1 + r.pick([2, 4]); w = GP.poly(new Q(b2 - b1, Hp), b1); desc = `a trapezoidal plate (dam face) ${b1} ${u} wide at the bottom, ${b2} ${u} wide at the top, and ${Hp} ${u} tall`; raw = y => b1 + (b2 - b1) * y / Hp; }
    const depth = GP.poly(-1, a), Gi = w.mul(depth), F = Gi.integ(), base = F.at(Hp).sub(F.at(0)), val = base.mul(wd);
    const steps = [
      { id: 'w', label: 'Width \\(w(y)\\) of the plate at height \\(y\\)', kind: 'expr', v: 'y', lo: 0, hi: Hp, ans: w.str('y'), mistakes: shape === 'rect' ? [] : [{ ans: `${Math.max(raw(0), raw(Hp))}`, msg: 'The width changes with y; use similar triangles / the side lines.' }], hint: 'Horizontal strip width as a function of height y from the bottom.' },
      { id: 'depth', label: 'Depth of the strip at height \\(y\\)', kind: 'expr', v: 'y', lo: 0, hi: Hp, ans: depth.str('y'), mistakes: [{ ans: 'y', msg: `y is height above the bottom; depth is measured down from the surface (at y = ${a}): ${a} − y.` }, ...(s ? [{ ans: GP.poly(-1, Hp).str('y'), msg: `The top of the plate is ${s} ${u} below the surface, so the surface is at y = ${a}.` }] : [])], hint: `Surface is at y = ${a}. Depth = ${a} − y.` },
      { id: 'a', label: 'Lower limit (y)', kind: 'num', ans: '0', hint: 'Bottom of the plate.' },
      { id: 'b', label: 'Upper limit (y)', kind: 'num', ans: `${Hp}`, mistakes: s ? [{ ans: `${a}`, msg: 'Integrate over the plate only (0 to its height), not up to the surface.' }] : [], hint: 'Top of the plate.' },
      { id: 'final', label: `Force (${us ? 'lb' : 'N'})`, kind: 'num', ans: val.str(), mistakes: [{ ans: base.str(), msg: `Multiply by the weight density ${us ? '62.5' : 'ρg = 9800'}.` }, ...(us ? [] : [{ ans: base.mul(1000).str(), msg: 'Use ρg = 9800 N/m³, not ρ = 1000.' }])], hint: `F = ${us ? '62.5' : '9800'}∫(depth)(width) dy.` },
    ];
    return finalize({ statement: `${desc[0].toUpperCase() + desc.slice(1)} is submerged vertically in water with its top edge ${s ? s + ' ' + u + ' below' : 'at'} the surface. Find the force on one side of the plate. Use ${us ? 'weight density 62.5 lb/ft³' : 'ρ = 1000 kg/m³, g = 9.8 m/s²'}; let \\(y\\) be the height above the bottom of the plate.`,
      steps, answer: val.str(),
      solution: [us ? 'Weight density: \\(62.5\\) lb/ft³ (already a weight).' : 'Weight density: \\(\\rho g = 1000 \\times 9.8 = 9800\\) N/m³.',
        `Cut the plate into horizontal strips. Pressure at depth \\(d\\) is \\(${us ? '62.5' : '9800'}\\,d\\); a strip's force is pressure times its area \\(w(y)\\,dy\\).`,
        ...(() => { const B = Math.max(raw(0), raw(Hp)), fr = `\\frac{${B}}{${Hp}}\\,y`, red = ty(new Q(B, Hp), 'y');
          return shape === 'rect' ? [`Width: the plate is \\(b = ${raw(0)}\\) wide everywhere.`, '$$w(y) = b$$', `$$w(y) = ${raw(0)}$$`]
          : shape === 'triDown' ? [`Width: \\(b\\) = base (on top), \\(h\\) = height; the width grows from 0 at the bottom vertex to \\(b\\) at the top.`, '$$w(y) = \\frac{b}{h}\\,y$$', `$$w(y) = ${eqs([fr, red])}$$`]
          : shape === 'triUp' ? [`Width: \\(b\\) = base (on the bottom), \\(h\\) = height; the width shrinks from \\(b\\) at the bottom to 0 at the top vertex.`, '$$w(y) = b - \\frac{b}{h}\\,y$$', `$$w(y) = ${eqs([`${B} - ${fr}`, `${B} - ${red}`])}$$`]
          : [`Width: \\(b_1\\) = bottom width, \\(b_2\\) = top width, \\(h\\) = height, changing in a straight line.`, '$$w(y) = b_1 + \\frac{b_2 - b_1}{h}\\,y$$', `$$w(y) = ${raw(0)} + \\frac{${raw(Hp)} - ${raw(0)}}{${Hp}}\\,y = ${raw(0)} + \\frac{${raw(Hp) - raw(0)}}{${Hp}}\\,y = ${T(w.str('y'))}$$`]; })(),
        `Depth: the top of the plate is at \\(y = ${Hp}\\) and the surface is ${s ? `\\(${s}\\) higher, at \\(y = ${Hp} + ${s} = ${a}\\)` : `right there, at \\(y = ${a}\\)`}. So a strip at height \\(y\\) is \\(${a} - y\\) deep.`,
        '$$\\text{depth} = (\\text{surface height}) - y$$', `$$\\text{depth} = ${a} - y$$`,
        `Integrate over the plate only, \\(y = 0\\) to \\(y = ${Hp}\\):`,
        '$$F = \\int_a^b \\rho g\\,(\\text{depth})\\,w(y)\\,dy$$', `$$F = \\int_0^{${Hp}} ${us ? '62.5' : '9800'}\\,(${a} - y)\\left(${T(w.str('y'))}\\right)dy$$`,
        `Multiply depth by width, every term: $$${mulGP(depth, w, 'y')}$$`,
        ...integralSteps({ G: Gi, v: 'y', a: q(0), b: q(Hp), factor: us ? '62.5' : '9800', factorQ: wd, what: 'F', unit: us ? 'lb' : 'N', sym: 'F', anti: 'G', dec: true }).work],
      truth: () => { const n = 20000, h = Hp / n; let S = 0; for (let i = 0; i < n; i++) { const y = (i + 0.5) * h; S += wd.v * (a - y) * raw(y) * h; } return S; } });
  }
  function mass(r) {
    const L = r.pick([1, 2, 3, 4]), c = r.int(1, 5), m = r.int(1, 4), p = r.pick([1, 2]);
    const rho = GP.k(c).add(GP.x(p, m)), F = rho.integ(), M = F.at(L).sub(F.at(0));
    const steps = [
      { id: 'integrand', label: 'Integrand: \\(m = \\int_0^L (\\;?\\;)\\,dx\\)', kind: 'expr', v: 'x', lo: 0, hi: L, ans: rho.str('x'), hint: 'Mass = ∫ density dx.' },
      { id: 'anti', label: 'Antiderivative', kind: 'anti', v: 'x', lo: 0, hi: L, integrand: rho.str('x'), ans: F.str('x') },
      { id: 'final', label: 'Mass (kg)', kind: 'num', ans: M.str(), mistakes: [{ ans: q(rho.at(L)).mul(L).str(), msg: 'Density varies along the bar: integrate it, don\'t multiply density at the end by length.' }], hint: 'F(L) − F(0).' },
    ];
    return finalize({ statement: `A thin bar on \\(0 \\le x \\le ${L}\\) (m) has density \\(\\rho(x) = ${T(rho.str('x'))}\\) kg/m. Find its mass.`, steps, answer: M.str(),
      solution: [`Mass is density integrated along the bar, from \\(x = 0\\) to \\(x = ${L}\\):`, '$$m = \\int_a^b \\rho(x)\\,dx$$',
        ...integralSteps({ G: rho, v: 'x', a: q(0), b: q(L), what: 'm', unit: 'kg', sym: 'm' }).work],
      truth: () => Check.simpson(x => rho.num(x), 0, L, 200) });
  }

  // ---------- shapes: width, radius and area of a horizontal slice at height y ----------
  // Every problem: what you know -> the equation it gives (letters, then numbers) -> solve for the unknown
  // -> A(y) -> A at one height. p.shape holds plain-geometry closures that test/verify.js checks the steps against.
  const about = (tex, val) => `,\\qquad ${tex} \\approx ${fmt(val)}`;
  const rev = g => ({ t: [...g.t].reverse() }); // evalAt lowest power first
  const ascS = (g, v) => [...g.t].reverse().map((t, i) => { const s = new GP([t]).str(v); return i === 0 ? s : s.startsWith('-') ? ' - ' + s.slice(1) : ' + ' + s; }).join('');
  const plain = s => s.replace(/\s+\*\s+/g, '').replace(/ \/ /g, '/'); // math.js string -> hint text
  function shapeProblem(o) {
    const { lo, hi, y0 } = o, v = 'y';
    const defined = ms => (ms || []).filter(m => Check.exprEq(m.ans, m.ans, v, lo, hi)); // a mistake can only be recognised where it exists
    const yT = tq(q(y0)), wdT = o.u === 'ft' ? '62.5' : '9800';
    const atY0 = s => s.replace(/\by\b/g, `(${y0})`);
    const finalMistakes = defined(o.area.mistakes).map(m => ({ ans: atY0(m.ans), msg: m.msg })).filter(m => isFinite(Check.evalNum(m.ans)));
    const steps = [
      { id: o.unk.id, label: o.unk.label, kind: 'expr', v, lo, hi, ans: o.unk.ans, mistakes: defined(o.unk.mistakes), hint: o.unk.hint },
      { id: 'A', label: 'Area \\(A(y)\\) of the horizontal slice at height \\(y\\)', kind: 'expr', v, lo, hi, ans: o.area.ans, mistakes: defined(o.area.mistakes), hint: o.area.hint },
      { id: 'final', label: `\\(A(${yT})\\): the slice area at \\(y = ${yT}\\) (${o.u}²)`, kind: 'num', ans: o.answer, mistakes: finalMistakes, hint: `Put y = ${y0} into your A(y).` },
    ];
    const W = o.area.tex ? [`In a pumping problem (water pumped out over the top, \\(y = ${hi}\\), \\(\\rho g = ${wdT}\\)) this slice goes straight into the book's integral:`,
      `$$W = \\int_{${lo}}^{${hi}} ${wdT}\\cdot A(y)\\cdot (${hi} - y)\\,dy = \\int_{${lo}}^{${hi}} ${wdT}\\cdot ${o.area.tex}\\cdot (${hi} - y)\\,dy$$`] : [];
    return finalize({ statement: `${o.statement} Find ${o.unk.ask} at height \\(y\\), the slice area \\(A(y)\\), and \\(A(${yT})\\).`, steps, answer: o.answer,
      solution: [...o.know, ...o.unk.lines, ...o.area.lines, `At \\(y = ${yT}\\):`, ...o.at, ...W],
      truth: () => o.area.raw(y0), shape: { unk: o.unk.raw, A: o.area.raw, lo, hi, y0 } });
  }
  // Circle of radius R with its centre at height c (c = 0: origin at the centre; c = R: origin at the bottom).
  // s names the unknown: x = half-width of a rectangle slice, r = radius of a circle slice.
  function circleRim(R, c, s) {
    const sh = c ? '(y - R)' : 'y', shN = c ? `(y - ${R})` : 'y', inner = c ? GP.poly(-1, 2 * R, 0) : GP.poly(-1, 0, R * R);
    const lines = [`The equation it gives (Pythagoras): a point on the circle at height \\(y\\) is \\(${s}\\) across from the centre line and \\(${c ? 'y - R' : 'y'}\\) up from the centre.`,
      `$$${s}^2 + ${sh}^2 = R^2$$`, `$$${s}^2 + ${shN}^2 = ${R}^2 = ${R * R}$$`,
      `Solve for \\(${s}\\): subtract \\(${sh}^2\\) from both sides, then take the square root.`,
      `$$${s} = \\sqrt{R^2 - ${sh}^2}$$`, `$$${s} = \\sqrt{${R * R} - ${shN}^2}$$`];
    if (c) lines.push(`Multiply out (optional): \\((y - ${R})^2 = y^2 - ${2 * R}y + ${R * R}\\), so \\(${R * R} - (y^2 - ${2 * R}y + ${R * R}) = ${gpA(inner, 'y')}\\) and \\(${s} = \\sqrt{${gpA(inner, 'y')}}\\).`);
    const at = y0 => { const d = y0 - c, m = R * R - d * d; return { m, line: `$$${s}(${y0})^2 = ${eqs([c ? `${R * R} - (${y0} - ${R})^2` : `${R * R} - ${tqp(q(y0))}^2`, ...(c ? [`${R * R} - ${tqp(q(d))}^2`] : []), `${R * R} - ${d * d}`, `${m}`])}$$` }; };
    const raw = y => R * Math.sin(Math.acos((y - c) / R)); // trig form, independent of the Pythagoras form above
    return { lines, ans: `sqrt(${R * R} - ${shN}^2)`, inner, at, raw, sh, shN };
  }

  function shBox(r) {
    const u = r.pick(['ft', 'm']);
    if (r.bool()) {
      const l = r.pick([4, 5, 6, 8, 10, 12]), w = r.pick([2, 3, 4, 5]), H = r.pick([3, 4, 5, 6]), y0 = r.int(1, H - 1);
      return shapeProblem({ u, y0, lo: 0, hi: H, answer: `${l * w}`,
        statement: `A rectangular tank is ${l} ${u} long, ${w} ${u} wide and ${H} ${u} tall. Put the origin at the bottom of the tank, \\(y\\) up.`,
        know: [`What you know: length \\(\\ell = ${l}\\), width \\(w = ${w}\\), height \\(H = ${H}\\). The walls go straight up, so every horizontal slice is the same \\(${l}\\) by \\(${w}\\) rectangle as the floor. Nothing depends on \\(y\\).`],
        unk: { id: 'len', ask: 'the length of a horizontal slice', label: 'Length of the slice at height \\(y\\) (the long side)', ans: `${l}`, raw: () => l, hint: 'Vertical walls: the slice is as long as the tank.',
          mistakes: [{ ans: `${H}`, msg: `${H} is the height. A horizontal slice is as long as the tank: ${l}.` }, { ans: `${w}`, msg: `${w} is the short side (the width). The long side is ${l}.` }],
          lines: ['$$\\text{length}(y) = \\ell$$', `$$\\text{length}(y) = ${l}$$`] },
        area: { ans: `${l * w}`, raw: () => l * w, hint: 'length × width', tex: `${l * w}`,
          mistakes: [{ ans: `${l * w * H}`, msg: 'That is the volume of the whole tank. A slice is a flat rectangle: length × width.' }, { ans: `${l + w}`, msg: 'Multiply length by width, don\'t add.' }],
          lines: ['A slice is a rectangle:', '$$A(y) = \\ell\\cdot w$$', `$$A(y) = ${l}\\times ${w} = ${l * w}$$`] },
        at: [`$$A(${y0}) = ${l}\\times ${w} = ${l * w}$$`, 'Same as every other height.'] });
    }
    // Pool whose floor slopes in a straight line from the shallow end down to the deep end.
    const L = r.pick([20, 24, 25, 30, 40]), W = r.pick([8, 10, 12, 15]), d1 = r.pick([1, 2, 3]), s = r.pick([2, 3, 4, 5]), d2 = d1 + s, y0 = r.int(1, s - 1);
    const k = new Q(L, s), lin = GP.x(1, k), Ak = k.mul(W), len0 = k.mul(y0), A0 = len0.mul(W);
    return shapeProblem({ u, y0, lo: 0, hi: s, answer: A0.str(),
      statement: `A swimming pool is ${L} ${u} long and ${W} ${u} wide. Its floor slopes in a straight line from a depth of ${d1} ${u} at the shallow end to ${d2} ${u} at the deep end, and the pool is full. Put the origin at the deepest point of the floor (the bottom of the deep-end wall), \\(y\\) up. Look only at the water below the level of the shallow end's floor, \\(0 \\le y \\le ${s}\\).`,
      know: [`What you know: pool length \\(L = ${L}\\), width \\(W = ${W}\\). The floor rises \\(s = ${d2} - ${d1} = ${s}\\) over the full length \\(L = ${L}\\). Below \\(y = ${s}\\) a horizontal slice of water starts at the deep-end wall and stops where it hits the sloped floor, so its length \\(\\ell\\) grows with \\(y\\).`],
      unk: { id: 'len', ask: 'the length \\(\\ell\\) of a horizontal slice of water', label: `Length \\(\\ell\\) of the slice at height \\(y\\) (for \\(0 \\le y \\le ${s}\\))`, ans: lin.str('y'), raw: y => y / (s / L),
        hint: `Similar triangles: ℓ/y = ${L}/${s}.`,
        mistakes: [{ ans: `${L}`, msg: `Below y = ${s} the slice does not reach the shallow wall: it stops at the floor. Similar triangles: ℓ/y = ${L}/${s}.` }, { ans: `${new Q(s, L).str()} * y`, msg: `Flipped. Length goes with length: ℓ/y = L/s = ${L}/${s}.` }],
        lines: ['The equation it gives (similar triangles: the wedge of water below height \\(y\\) has the same shape as the whole sloped part):', '$$\\frac{\\ell}{y} = \\frac{L}{s}$$', `$$\\frac{\\ell}{y} = \\frac{${L}}{${s}}$$`,
          'Solve for \\(\\ell\\): multiply both sides by \\(y\\).', '$$\\ell = \\frac{L}{s}\\,y$$', `$$\\ell = ${eqs([`\\frac{${L}}{${s}}\\,y`, ty(k, 'y')])}$$`] },
      area: { ans: GP.x(1, Ak).str('y'), raw: y => W * y / (s / L), hint: `A(y) = ${W}·ℓ.`,
        mistakes: [{ ans: `${L * W}`, msg: `That is the full ${L} × ${W} slice, true only above y = ${s}. Lower down the length is ℓ = (${L}/${s})y.` }, { ans: lin.str('y'), msg: `That is the length alone. Multiply by the width ${W}.` }],
        lines: ['A slice is a rectangle, \\(\\ell\\) long and \\(W\\) wide:', '$$A(y) = W\\cdot\\ell = W\\cdot\\frac{L}{s}\\,y$$', `$$A(y) = ${W}\\cdot ${ty(k, 'y')} = ${ty(Ak, 'y')}$$`, `$$${mulLine(q(W), k)}$$`, `(Above \\(y = ${s}\\) the slice is the full \\(${L}\\times ${W} = ${L * W}\\).)`] },
      at: [`$$\\ell(${y0}) = ${mulLine(k, q(y0))}$$`, `$$A(${y0}) = ${mulLine(q(W), len0)}$$`] });
  }

  function shCyl(r) {
    const u = r.pick(['ft', 'm']), R = r.pick([1, 2, 3, 4, 5, 6]), H = r.pick([4, 5, 6, 8, 10]), y0 = r.int(1, H - 1), byD = r.bool(), A0 = q(R * R);
    return shapeProblem({ u, y0, lo: 0, hi: H, answer: exactPi(A0, true),
      statement: `A cylindrical tank stands upright. It has ${byD ? 'diameter ' + 2 * R : 'radius ' + R} ${u} and height ${H} ${u}. Put the origin at the centre of the bottom, \\(y\\) up.`,
      know: [`What you know: ${byD ? `diameter \\(d = ${2 * R}\\), height \\(H = ${H}\\). The radius is half the diameter: $$r = \\frac{d}{2}$$ $$r = \\frac{${2 * R}}{2} = ${R}$$` : `radius \\(r = ${R}\\), height \\(H = ${H}\\).`} The wall goes straight up, so every horizontal slice is the same circle as the floor. Nothing depends on \\(y\\).`],
      unk: { id: 'rad', ask: 'the radius \\(r\\) of a horizontal slice', label: 'Radius \\(r\\) of the slice at height \\(y\\)', ans: `${R}`, raw: () => R, hint: byD ? 'Half the diameter.' : 'Straight walls: same radius at every height.',
        mistakes: [...(byD ? [{ ans: `${2 * R}`, msg: `${2 * R} is the diameter. The radius is half: ${2 * R}/2 = ${R}.` }] : []), { ans: `${H}`, msg: `${H} is the height, not the radius.` }],
        lines: ['$$r(y) = r$$', `$$r(y) = ${R}$$`] },
      area: { ans: exactPi(A0, true), raw: () => Math.PI * R * R, hint: 'A = π r²', tex: piT(A0),
        mistakes: [{ ans: `${R * R}`, msg: 'A circle\'s area is πr²: include π.' }, { ans: `2 * pi * ${R}`, msg: '2πr is the distance around the circle. Area is πr².' }, { ans: `pi * ${4 * R * R}`, msg: `Square the radius ${R}, not the diameter ${2 * R}.` }],
        lines: ['A slice is a circle:', '$$A(y) = \\pi r^2$$', `$$A(y) = \\pi\\cdot ${R}^2 = \\pi\\cdot ${R}\\times ${R} = ${piT(A0)}$$`] },
      at: [`$$A(${y0}) = \\pi\\cdot ${R}^2 = ${piT(A0)}${about(piT(A0), Math.PI * R * R)}$$`, 'Same as every other height.'] });
  }

  function shCone(r) {
    const u = r.pick(['ft', 'm']), R = r.pick([1, 2, 3, 4, 5, 6]), H = r.pick([2, 3, 4, 5, 6, 8, 10]), k = new Q(R, H), kk = k.mul(k), down = r.bool(), y0 = r.int(1, H - 1), byD = r.next() < 0.3;
    const lin = down ? GP.x(1, k) : GP.poly(k.neg(), R), ry0 = lin.at(y0), A0 = ry0.mul(ry0);
    const given = byD ? `diameter ${2 * R} ${u}` : `radius ${R} ${u}`;
    const half = byD ? [`The radius is half the diameter: $$R = \\frac{d}{2}$$ $$R = \\frac{${2 * R}}{2} = ${R}$$`] : [];
    const raw = down ? y => R * y / H : y => R * (H - y) / H; // cone edge: straight line from the point to the rim
    const common = { u, y0, lo: 0, hi: H, answer: exactPi(A0, true) };
    const area = (letters, nums, ans, tex, mistakes) => ({ ans, tex, raw: y => Math.PI * raw(y) ** 2, hint: 'A = π r², with your r.', mistakes: [{ ans: ans.replace('pi * ', ''), msg: 'A circle\'s area is πr²: include π.' }, { ans: `pi * ${R * R}`, msg: `That uses the full radius ${R} for every slice. Use your r at height y.` }, ...mistakes],
      lines: ['A slice is a circle:', `$$A(y) = \\pi r^2 = ${letters}$$`, `$$A(y) = ${nums}$$`] });
    const atLines = [`$$${evalAt(rev(lin), q(y0), 'r')}$$`, `$$A(${y0}) = \\pi r^2 = ${eqs([`\\pi\\cdot ${tqp(ry0)}^2`, `\\pi\\cdot ${tq(A0)}`, piT(A0)])}${about(piT(A0), Math.PI * A0.v)}$$`];
    if (down) return shapeProblem({ ...common,
      statement: `A conical tank has its point (vertex) at the bottom. It is ${H} ${u} tall and the circle at the top has ${given}. Put the origin at the vertex, \\(y\\) up.`,
      know: [`What you know: top radius \\(R = ${R}\\), height \\(H = ${H}\\), point at the bottom.`, ...half, `A horizontal slice is a circle. Its radius \\(r\\) grows from 0 at the point to \\(${R}\\) at the top.`],
      unk: { id: 'rad', ask: 'the radius \\(r\\) of a horizontal slice', label: 'Radius \\(r\\) of the slice at height \\(y\\)', ans: lin.str('y'), raw, hint: `Similar triangles: r/y = ${R}/${H}.`,
        mistakes: [{ ans: `${new Q(H, R).str()} * y`, msg: `Flipped. Radius goes with radius: r/y = R/H = ${R}/${H}.` }, { ans: `${R}`, msg: `${R} is the radius only at the top. Lower slices are smaller: r/y = ${R}/${H}.` }, { ans: `${2 * R}/${H} * y`, msg: `${2 * R} is the diameter. Use the radius ${R}: r/y = ${R}/${H}.` }, { ans: GP.poly(k.neg(), R).str('y'), msg: 'That is the point-up cone. Here the point is at the bottom, so r grows with y: r/y = R/H.' }],
        lines: ['The equation it gives (similar triangles: the cone of water below height \\(y\\) has the same shape as the whole cone):', '$$\\frac{r}{y} = \\frac{R}{H}$$', `$$\\frac{r}{y} = \\frac{${R}}{${H}}$$`,
          'Solve for \\(r\\): multiply both sides by \\(y\\).', '$$r = \\frac{R}{H}\\,y$$', `$$r = ${eqs([`\\frac{${R}}{${H}}\\,y`, ty(k, 'y')])}$$`] },
      area: area('\\pi\\left(\\frac{R}{H}\\,y\\right)^2', `\\pi\\left(${ty(k, 'y')}\\right)^2 = ${tqp(k)}^2\\,\\pi y^2 = ${ty(kk, '\\pi y^2')}$$ $$${tqp(k)}^2 = ${mulLine(k, k)}`, `pi * ${kk.str()} * y^2`, ty(kk, '\\pi y^2'),
        [{ ans: `pi * ${k.str()} * y`, msg: `Square the radius: A = π r² = π((${R}/${H})y)².` }]),
      at: atLines });
    return shapeProblem({ ...common,
      statement: `A conical tank has its point (vertex) at the top. It is ${H} ${u} tall and the circle at the bottom has ${given}. Put the origin at the centre of the bottom, \\(y\\) up.`,
      know: [`What you know: bottom radius \\(R = ${R}\\), height \\(H = ${H}\\), point at the top.`, ...half, `A horizontal slice is a circle. Its radius \\(r\\) shrinks from \\(${R}\\) at the bottom to 0 at the point. A slice at height \\(y\\) is \\(${H} - y\\) below the point.`],
      unk: { id: 'rad', ask: 'the radius \\(r\\) of a horizontal slice', label: 'Radius \\(r\\) of the slice at height \\(y\\)', ans: ascS(lin, 'y'), raw, hint: `Similar triangles from the point: r/(${H} − y) = ${R}/${H}.`,
        mistakes: [{ ans: `${k.str()} * y`, msg: `That is the point-down cone. Here the point is at the top, so r shrinks as y grows: r/(${H} − y) = ${R}/${H}.` }, { ans: `${R}`, msg: `${R} is the radius only at the bottom. Higher slices are smaller: r/(${H} − y) = ${R}/${H}.` }, { ans: `${new Q(H, R).str()} * (${H} - y)`, msg: `Flipped. Radius goes with radius: r/(${H} − y) = R/H = ${R}/${H}.` }],
        lines: ['The equation it gives (similar triangles, measured down from the point):', '$$\\frac{r}{H - y} = \\frac{R}{H}$$', `$$\\frac{r}{${H} - y} = \\frac{${R}}{${H}}$$`,
          'Solve for \\(r\\): multiply both sides by \\(H - y\\).', '$$r = \\frac{R}{H}(H - y)$$', `$$r = ${k.eq(1) ? '' : tq(k)}(${H} - y) = ${gpA(lin, 'y')}$$`, `$$${mulLine(k, q(H))}$$`] },
      area: area('\\pi\\left(\\frac{R}{H}(H - y)\\right)^2', `\\pi\\left(${gpA(lin, 'y')}\\right)^2`, `pi * (${ascS(lin, 'y')})^2`, `\\pi\\left(${gpA(lin, 'y')}\\right)^2`,
        [{ ans: `pi * ${kk.str()} * y^2`, msg: `That is the point-down cone. Here r = ${plain(ascS(lin, 'y'))}, so A = π(that)².` }]),
      at: atLines });
  }

  // Horizontal cylinder and semicircle-ended trough: the slice is a rectangle, L long and 2x wide.
  function roundTrough(r, kind) {
    const u = r.pick(['ft', 'm']), R = r.pick([2, 3, 4, 5, 6, 10]), L = r.pick([6, 8, 10, 12, 15, 20]), atBottom = r.bool(), c = atBottom ? R : 0;
    const lo = kind === 'hcyl' ? c - R : atBottom ? 0 : -R, hi = kind === 'hcyl' ? c + R : atBottom ? R : 0;
    const y0 = r.int(lo + 1, hi - 1), rim = circleRim(R, c, 'x'), { m, line } = rim.at(y0), n = nthRoot(m, 2);
    const A0 = n === null ? `${2 * L} * sqrt(${m})` : `${2 * L * n}`, A0T = n === null ? `${2 * L}\\sqrt{${m}}` : `${2 * L * n}`;
    const statement = kind === 'hcyl'
      ? `A cylindrical tank lies on its side. It is ${L} ${u} long and its circular ends have radius ${R} ${u}. Put the origin ${atBottom ? 'at the bottom of a circular end' : 'at the centre of a circular end'}, \\(y\\) up.`
      : `A trough is ${L} ${u} long. Its ends are semicircles of radius ${R} ${u} with the flat side on top. Put the origin ${atBottom ? 'at the lowest point of an end' : 'at the centre of the flat top edge of an end'}, \\(y\\) up${atBottom ? '' : ` (so the bottom is at \\(y = -${R}\\))`}.`;
    const other = c ? `sqrt(${R * R} - y^2)` : `sqrt(${R * R} - (y - ${R})^2)`;
    return shapeProblem({ u, y0, lo, hi, answer: A0,
      statement,
      know: [`What you know: radius \\(R = ${R}\\), length \\(L = ${L}\\). With this origin the centre of the circle is at \\(y = ${c}\\)${c ? ' (one radius up from the bottom)' : ''}. A horizontal slice is a rectangle, \\(L\\) long and \\(2x\\) wide, where \\(x\\) is the half-width (centre line to the curved edge) at height \\(y\\).`],
      unk: { id: 'half', ask: 'the half-width \\(x\\) of a horizontal slice', label: 'Half-width \\(x\\) of the slice at height \\(y\\) (centre line to the edge)', ans: rim.ans, raw: rim.raw, hint: `x² + ${rim.shN}² = ${R}².`,
        mistakes: [{ ans: other, msg: c ? `That puts the centre at y = 0. Here the origin is at the bottom, so the centre is at y = ${R}: x² + (y − ${R})² = ${R}².` : `That puts the centre at y = ${R}. Here the origin is at the centre: x² + y² = ${R}².` }, { ans: `${R * R} - ${rim.shN}^2`, msg: 'That is x². Take the square root.' }, { ans: `2 * ${rim.ans}`, msg: 'That is the full width. x is half of it (centre line to the edge).' }],
        lines: rim.lines },
      area: { ans: `${2 * L} * ${rim.ans}`, raw: y => L * 2 * rim.raw(y), hint: `A = L · 2x = ${L} · 2x.`, tex: `${2 * L}\\sqrt{${R * R} - ${rim.shN}^2}`,
        mistakes: [{ ans: `${L} * ${rim.ans}`, msg: 'x is only half the width. The slice is 2x wide: A = L·2x.' }, { ans: `2 * ${rim.ans}`, msg: `That is the width alone. Multiply by the length ${L}.` }, { ans: `pi * (${R * R} - ${rim.shN}^2)`, msg: `The slice is a rectangle (L long, 2x wide), not a circle. A = ${L}·2x.` }],
        lines: ['A slice is a rectangle, \\(L\\) long and \\(2x\\) wide:', '$$A(y) = L\\cdot 2x = 2L\\sqrt{R^2 - ' + rim.sh + '^2}$$', `$$A(y) = ${L}\\cdot 2\\sqrt{${R * R} - ${rim.shN}^2} = ${2 * L}\\sqrt{${R * R} - ${rim.shN}^2}$$`, `$$${L}\\times 2 = ${2 * L}$$`] },
      at: [line, `$$x(${y0}) = \\sqrt{${m}}${n === null ? '' : ` = ${n}`}$$`, `$$A(${y0}) = ${L}\\cdot 2\\cdot ${n === null ? `\\sqrt{${m}}` : n} = ${A0T}${n === null ? about(A0T, 2 * L * Math.sqrt(m)) : ''}$$`] });
  }

  function shSphere(r) {
    const u = r.pick(['ft', 'm']), R = r.pick([2, 3, 4, 5, 6, 10]), kind = r.pick(['sc', 'sb', 'bowl', 'bowlc', 'dome']);
    const c = kind === 'sb' || kind === 'bowl' ? R : 0;
    const [lo, hi] = { sc: [-R, R], sb: [0, 2 * R], bowl: [0, R], bowlc: [-R, 0], dome: [0, R] }[kind];
    const y0 = r.int(lo + 1, hi - 1), rim = circleRim(R, c, 'r'), { m, line } = rim.at(y0), A0 = q(m);
    const statement = {
      sc: `A spherical tank has radius ${R} ${u}. Put the origin at the centre of the sphere, \\(y\\) up (the tank runs from \\(y = -${R}\\) to \\(y = ${R}\\)).`,
      sb: `A spherical tank has radius ${R} ${u}. Put the origin at the bottom of the tank, \\(y\\) up (the top is at \\(y = ${2 * R}\\)).`,
      bowl: `A hemispherical bowl (flat side up) has radius ${R} ${u}. Put the origin at the bottom of the bowl, \\(y\\) up (the rim is at \\(y = ${R}\\)).`,
      bowlc: `A hemispherical bowl (flat side up) has radius ${R} ${u}. Put the origin at the centre of the flat top, \\(y\\) up (the bottom of the bowl is at \\(y = -${R}\\)).`,
      dome: `A hemispherical dome tank (flat side down) has radius ${R} ${u}. Put the origin at the centre of the flat floor, \\(y\\) up.`,
    }[kind];
    const other = c ? `sqrt(${R * R} - y^2)` : `sqrt(${R * R} - (y - ${R})^2)`;
    return shapeProblem({ u, y0, lo, hi, answer: exactPi(A0, true),
      statement,
      know: [`What you know: sphere radius \\(R = ${R}\\). With this origin the centre of the sphere is at \\(y = ${c}\\)${c ? ' (one radius up from the bottom)' : ''}. A horizontal slice is a circle; its radius \\(r\\) is the distance from the centre line to the curved wall at height \\(y\\).`],
      unk: { id: 'rad', ask: 'the radius \\(r\\) of a horizontal slice', label: 'Radius \\(r\\) of the slice at height \\(y\\)', ans: rim.ans, raw: rim.raw, hint: `r² + ${rim.shN}² = ${R}².`,
        mistakes: [{ ans: other, msg: c ? `That puts the centre at y = 0. Here the origin is at the bottom, so the centre is at y = ${R}: r² + (y − ${R})² = ${R}².` : `That puts the centre at y = ${R}. Here the origin is at the centre: r² + y² = ${R}².` }, { ans: `${R * R} - ${rim.shN}^2`, msg: 'That is r². Take the square root.' }, { ans: `${R}`, msg: `${R} is the radius only through the centre. Other slices are smaller: r² + ${rim.shN}² = ${R}².` }],
        lines: rim.lines },
      area: { ans: `pi * (${ascS(rim.inner, 'y')})`, raw: y => Math.PI * rim.raw(y) ** 2, hint: 'A = π r²; squaring removes the square root.', tex: `\\pi\\left(${R * R} - ${rim.shN}^2\\right)`,
        mistakes: [{ ans: ascS(rim.inner, 'y'), msg: 'A circle\'s area is πr²: include π.' }, { ans: `pi * ${rim.ans}`, msg: 'Square the radius: A = πr² = π(R² − …), no square root left.' }, { ans: `pi * ${R * R}`, msg: `That uses the sphere's radius ${R} for every slice. Use your r at height y.` }],
        lines: ['A slice is a circle. Squaring \\(r\\) undoes the square root:', `$$A(y) = \\pi r^2 = \\pi\\left(R^2 - ${rim.sh}^2\\right)$$`, `$$A(y) = \\pi\\left(${R * R} - ${rim.shN}^2\\right)${c ? ` = \\pi\\left(${gpA(rim.inner, 'y')}\\right)` : ''}$$`] },
      at: [line, `$$A(${y0}) = \\pi r^2 = \\pi\\cdot ${m} = ${piT(A0)}${about(piT(A0), Math.PI * m)}$$`] });
  }

  // Trough with flat (triangle or trapezoid) ends: slice = rectangle, length times the end's width at height y.
  function flatTrough(r, kind) {
    const u = r.pick(['ft', 'm']), len = r.pick([5, 6, 8, 10, 12, 20]), h = r.pick([1, 2, 3, 4]), y0 = r.int(1, Math.max(1, h - 1));
    let lin, raw, know, lines, wMistakes, statement;
    if (kind === 'tri') {
      const b = r.pick([2, 3, 4, 6]), k = new Q(b, h), down = r.bool();
      if (down) {
        lin = GP.x(1, k); raw = y => b * y / h;
        statement = `A trough is ${len} ${u} long. Its ends are triangles with the point down, ${b} ${u} across the top and ${h} ${u} deep. Put the origin at the point (the bottom of an end), \\(y\\) up.`;
        know = [`What you know: top width \\(b = ${b}\\), depth \\(h = ${h}\\), length \\(\\ell = ${len}\\). The width \\(w\\) of a slice grows from 0 at the point to \\(${b}\\) at the top.`];
        lines = ['The equation it gives (similar triangles: the triangle of water below height \\(y\\) has the same shape as the whole end):', '$$\\frac{w}{y} = \\frac{b}{h}$$', `$$\\frac{w}{y} = \\frac{${b}}{${h}}$$`,
          'Solve for \\(w\\): multiply both sides by \\(y\\).', '$$w = \\frac{b}{h}\\,y$$', `$$w = ${eqs([`\\frac{${b}}{${h}}\\,y`, ty(k, 'y')])}$$`];
        wMistakes = [{ ans: `${new Q(h, b).str()} * y`, msg: `Flipped. Width goes with width: w/y = b/h = ${b}/${h}.` }, { ans: `${b}`, msg: `${b} is the width only at the top. Lower down it is narrower: w/y = ${b}/${h}.` }, { ans: GP.poly(k.neg(), b).str('y'), msg: 'That is the point-up triangle. Here the point is at the bottom, so w grows with y: w/y = b/h.' }];
      } else {
        lin = GP.poly(k.neg(), b); raw = y => b * (h - y) / h;
        statement = `A tank is ${len} ${u} long. Its ends are triangles with the point up, ${b} ${u} across the bottom and ${h} ${u} tall. Put the origin at the middle of the bottom edge of an end, \\(y\\) up.`;
        know = [`What you know: bottom width \\(b = ${b}\\), height \\(h = ${h}\\), length \\(\\ell = ${len}\\). The width \\(w\\) of a slice shrinks from \\(${b}\\) at the bottom to 0 at the point. A slice at height \\(y\\) is \\(${h} - y\\) below the point.`];
        lines = ['The equation it gives (similar triangles, measured down from the point):', '$$\\frac{w}{h - y} = \\frac{b}{h}$$', `$$\\frac{w}{${h} - y} = \\frac{${b}}{${h}}$$`,
          'Solve for \\(w\\): multiply both sides by \\(h - y\\).', '$$w = \\frac{b}{h}(h - y)$$', `$$w = ${k.eq(1) ? '' : tq(k)}(${h} - y) = ${gpA(lin, 'y')}$$`, `$$${mulLine(k, q(h))}$$`];
        wMistakes = [{ ans: `${k.str()} * y`, msg: `That is the point-down triangle. Here the point is at the top, so w shrinks as y grows: w/(${h} − y) = ${b}/${h}.` }, { ans: `${b}`, msg: `${b} is the width only at the bottom: w/(${h} − y) = ${b}/${h}.` }];
      }
    } else {
      const b1 = r.pick([2, 3, 4, 6]), b2 = r.pick([2, 3, 4, 6, 8].filter(x => x !== b1)), k = new Q(b2 - b1, h);
      lin = GP.poly(k, b1); raw = y => b1 + (b2 - b1) * (y / h);
      statement = `A trough is ${len} ${u} long. Its ends are trapezoids ${b1} ${u} wide at the bottom, ${b2} ${u} wide at the top and ${h} ${u} tall. Put the origin at the middle of the bottom edge of an end, \\(y\\) up.`;
      know = [`What you know: bottom width \\(b_1 = ${b1}\\), top width \\(b_2 = ${b2}\\), height \\(h = ${h}\\), length \\(\\ell = ${len}\\). The width changes in a straight line from \\(${b1}\\) at \\(y = 0\\) to \\(${b2}\\) at \\(y = ${h}\\).`];
      lines = [`The equation it gives: over the height \\(h\\) the width changes by \\(b_2 - b_1\\), so it changes by \\(\\frac{b_2 - b_1}{h}\\) per unit of height, starting from \\(b_1\\):`, '$$w = b_1 + \\frac{b_2 - b_1}{h}\\,y$$',
        `$$w = ${b1} + \\frac{${b2} - ${b1}}{${h}}\\,y = ${gpA(lin, 'y')}$$`, `$$\\frac{${b2} - ${b1}}{${h}} = \\frac{${b2 - b1}}{${h}} = ${tq(k)}$$`,
        `Check the top: $$${evalAt(rev(lin), q(h), 'w')}$$ which is \\(b_2\\).`];
      wMistakes = [{ ans: `${new Q(b2, h).str()} * y`, msg: `That is a triangle (width 0 at the bottom). A trapezoid starts at b₁ = ${b1}: w = ${b1} + ((${b2} − ${b1})/${h})y.` }, { ans: `${b1} + ${new Q(b2, h).str()} * y`, msg: `Use the change in width, ${b2} − ${b1}, not ${b2}.` }, { ans: `${b2} + ${new Q(b1 - b2, h).str()} * y`, msg: `Upside down: at y = 0 (the bottom) the width is b₁ = ${b1}.` }];
    }
    const Ag = lin.scale(len), w0 = lin.at(y0), AgT = Ag.t.length > 1 ? `\\left(${gpA(Ag, 'y')}\\right)` : gpT(Ag, 'y');
    return shapeProblem({ u, y0, lo: 0, hi: h, answer: w0.mul(len).str(), statement, know,
      unk: { id: 'wid', ask: 'the width \\(w\\) of a horizontal slice', label: 'Width \\(w\\) of the slice at height \\(y\\) (across the end)', ans: ascS(lin, 'y'), raw, hint: kind === 'tri' ? 'Similar triangles.' : 'Bottom width plus (change in width ÷ height) times y.', mistakes: wMistakes, lines },
      area: { ans: ascS(Ag, 'y'), raw: y => len * raw(y), hint: `A = ${len}·w.`, tex: AgT,
        mistakes: [{ ans: lin.str('y'), msg: `That is the width alone. A slice is a rectangle: multiply by the length ${len}.` }, { ans: `${len * Math.max(raw(0), raw(h))}`, msg: 'The width changes with y; use your w(y), not the widest width.' }],
        lines: ['A slice is a rectangle, \\(\\ell\\) long and \\(w\\) wide:', '$$A(y) = \\ell\\cdot w$$', `$$A(y) = ${len}\\left(${gpA(lin, 'y')}\\right) = ${gpA(Ag, 'y')}$$`, ...rev(lin).t.map(t => `$$${mulLine(q(len), t.c)}$$`)] },
      at: [`$$${evalAt(rev(lin), q(y0), 'w')}$$`, `$$A(${y0}) = \\ell\\cdot w = ${mulLine(q(len), w0)}$$`] });
  }

  function shPara(r) {
    const u = r.pick(['ft', 'm']), len = r.pick([5, 6, 8, 10, 12]);
    const [a, N] = r.pick([[q(1), 2], [q(1), 3], [q(2), 2], [q(2), 1], [q(3), 1], [q(4), 1], [new Q(1, 4), 4], [new Q(1, 4), 2], [new Q(1, 2), 2], [new Q(1, 2), 4]]);
    const h = a.mul(N * N), inv = q(1).div(a), byWidth = r.bool();
    const ns = []; for (let i = 1; i < N; i++) if (a.mul(i * i).d === 1) ns.push(i);
    const n = ns.length ? r.pick(ns) : N, y0 = a.mul(n * n).v;
    const xS = inv.eq(1) ? 'sqrt(y)' : `sqrt(${inv.str()} * y)`, xT = `\\sqrt{${ty(inv, 'y')}}`;
    const eqT = `y = ${ty(a, 'x^2')}`;
    const solveA = byWidth ? [`First find \\(a\\): the top corners \\((\\pm\\frac{b}{2}, h) = (\\pm ${N}, ${h.v})\\) are on the parabola \\(y = ax^2\\).`, '$$h = a\\left(\\frac{b}{2}\\right)^2$$', `$$${h.v} = a\\cdot ${N}^2${N === 1 ? '' : ` = ${N * N}a`},\\qquad a = \\frac{${h.v}}{${N * N}} = ${tq(a)}$$`, `So the edge is \\(${eqT}\\).`] : [];
    return shapeProblem({ u, y0, lo: 0, hi: h.v, answer: `${2 * len * n}`,
      statement: byWidth
        ? `A trough is ${len} ${u} long. Its ends are parabolas \\(y = ax^2\\) (vertex down), ${2 * N} ${u} across the top and ${h.v} ${u} tall. Put the origin at the vertex, \\(y\\) up.`
        : `A trough is ${len} ${u} long. Its ends are the region between \\(${eqT}\\) and the line \\(y = ${h.v}\\) (units ${u}). The origin is at the vertex, \\(y\\) up.`,
      know: [`What you know: ${byWidth ? `top width \\(b = ${2 * N}\\), height \\(h = ${h.v}\\)` : `the edge is \\(${eqT}\\), the top is at \\(y = ${h.v}\\)`}, length \\(\\ell = ${len}\\). A horizontal slice is a rectangle, \\(\\ell\\) long and \\(2x\\) wide, where \\(x\\) is the half-width (centre line to the edge) at height \\(y\\).`, ...solveA],
      unk: { id: 'half', ask: 'the half-width \\(x\\) of a horizontal slice', label: 'Half-width \\(x\\) of the slice at height \\(y\\) (centre line to the edge)', ans: xS, raw: y => Math.sqrt(y / a.v), hint: `Solve y = ${a.eq(1) ? '' : `(${a.str()})`}x² for x.`,
        mistakes: [...(a.eq(1) ? [] : [{ ans: `sqrt(${a.str()} * y)`, msg: `Divide by a, don't multiply: y = ax² gives x² = y/a = ${inv.str()}y.` }]), { ans: inv.eq(1) ? 'y' : `${inv.str()} * y`, msg: 'That is x². Take the square root.' }, { ans: `2 * ${xS}`, msg: 'That is the full width. x is half of it (centre line to the edge).' }],
        lines: ['The equation it gives: the point on the edge at height \\(y\\) is on the parabola.', '$$y = ax^2$$', `$$${eqT}$$`, 'Solve for \\(x\\): divide by \\(a\\), then take the square root.',
          '$$x = \\sqrt{\\frac{y}{a}}$$', `$$x = ${inv.eq(1) ? '\\sqrt{y}' : `\\sqrt{\\frac{y}{${tq(a)}}} = ${xT}`}$$`] },
      area: { ans: `${2 * len} * ${xS}`, raw: y => len * 2 * Math.sqrt(y / a.v), hint: `A = ${len}·2x.`, tex: `${2 * len}${xT}`,
        mistakes: [{ ans: `${len} * ${xS}`, msg: 'x is only half the width. The slice is 2x wide: A = ℓ·2x.' }, { ans: `2 * ${xS}`, msg: `That is the width alone. Multiply by the length ${len}.` }],
        lines: ['A slice is a rectangle, \\(\\ell\\) long and \\(2x\\) wide:', '$$A(y) = \\ell\\cdot 2x = 2\\ell\\sqrt{\\frac{y}{a}}$$', `$$A(y) = ${len}\\cdot 2${xT} = ${2 * len}${xT}$$`, `$$${len}\\times 2 = ${2 * len}$$`] },
      at: [`$$x(${y0}) = \\sqrt{${y0} \\div ${tq(a)}} = \\sqrt{${n * n}} = ${n}$$`, `$$A(${y0}) = ${len}\\cdot 2\\cdot ${n} = ${2 * len * n}$$`] });
  }

  // ---------- assigned homework: the exact Briggs/Cochran problems (6.4, 6.5) ----------
  // seq() stands in for rng so the generators above build one fixed variant.
  const seq = (...vals) => { let i = 0; const nx = a => { const v = vals[i++]; return typeof v === 'function' ? v(a) : v; }; return { pick: nx, int: nx, bool: nx, next: nx }; };
  const reg = (i, ...vals) => REGIONS[i](seq(...vals));
  function hw24() {
    const b = Math.SQRT2, h = 'sqrt(4 - 2 x^2)', G = `x ${h}`;
    const steps = [
      { id: 'a', label: 'Lower bound of x', kind: 'num', ans: '0', hint: 'The region starts at x = 0 (the y-axis).' },
      { id: 'b', label: 'Upper bound of x', kind: 'num', ans: 'sqrt(2)', mistakes: [{ ans: '2', msg: 'Solve 4 − 2x² = 0: x² = 2, so x = √2, not 2.' }], hint: 'Where the curve meets y = 0: 4 − 2x² = 0.' },
      { id: 'radius', label: 'Shell radius in terms of \\(x\\) (distance from the axis)', kind: 'expr', v: 'x', lo: 0, hi: b, ans: 'x', mistakes: [{ ans: h, msg: 'That is the shell height. The radius is the distance from the axis to the shell.' }], signHint: 'A radius is a distance: always positive.', hint: 'Distance from the y-axis to a shell at x.' },
      { id: 'height', label: 'Shell height \\(h(x)\\) (top − bottom)', kind: 'expr', v: 'x', lo: 0, hi: b, ans: h, mistakes: [{ ans: '4 - 2 x^2', msg: 'Keep the square root: the top curve is y = √(4 − 2x²).' }, { ans: 'x', msg: 'That is the radius, not the height.' }], signHint: 'Height = top − bottom.', hint: 'Top curve √(4 − 2x²) minus bottom curve y = 0.' },
      { id: 'integrand', label: 'Integrand: \\(V = 2\\pi\\int_a^b (\\;?\\;)\\,dx\\). Enter radius × height.', kind: 'expr', v: 'x', lo: 0, hi: b, ans: G, mistakes: [{ ans: h, msg: 'You left out the radius. Shell integrand = (radius)(height).' }, { ans: 'x', msg: 'You left out the height. Shell integrand = (radius)(height).' }, { ans: 'x (4 - 2 x^2)', msg: 'Nothing is squared in the shell method, and the height keeps its square root: x·√(4 − 2x²).' }], hint: 'x · √(4 − 2x²).' },
      { id: 'anti', label: 'Antiderivative \\(F(x)\\) of your integrand (any + C)', kind: 'anti', v: 'x', lo: 0, hi: b, integrand: G, ans: '-(4 - 2 x^2)^(3/2) / 6', mistakes: [{ ans: '(4 - 2 x^2)^(3/2) / 6', msg: 'Sign: du = −4x dx, so x dx = −du/4 and the antiderivative is negative.' }], hint: 'u = 4 − 2x², du = −4x dx, so x dx = −du/4: ∫ −√u du/4 = −u^(3/2)/6.' },
      { id: 'final', label: 'Volume \\(V\\) (exact, e.g. 8pi/27, or decimal to 4 significant digits)', kind: 'num', ans: '8 pi / 3', mistakes: [{ ans: '4/3', msg: 'You dropped the constant out front (2π). Multiply your F(b) − F(a) by it.' }, { ans: '4 pi / 3', msg: 'Shell method has 2π out front, not π.' }], hint: 'F(√2) − F(0) = 0 − (−8/6) = 4/3, then multiply by 2π.' },
    ];
    return finalize({
      statement: 'Let \\(R\\) be the region bounded by \\(y = \\sqrt{4 - 2x^2}\\), \\(y = 0\\), and \\(x = 0\\) in the first quadrant. Use the shell method to find the volume of the solid generated when \\(R\\) is revolved about the \\(y\\)-axis.',
      steps, answer: '8 pi / 3', fac: 2 * Math.PI,
      solution: ['Shells are parallel to the \\(y\\)-axis (\\(x = k = 0\\)), so they have thickness \\(dx\\). The curve meets \\(y = 0\\) where:',
        '$$4 - 2x^2 = 0 \\;\\Rightarrow\\; 2x^2 = 4 \\;\\Rightarrow\\; x^2 = 4 \\div 2 = 2 \\;\\Rightarrow\\; x = \\sqrt 2$$ so \\(x\\) runs from \\(0\\) to \\(\\sqrt 2\\).',
        '$$\\text{radius} = x - k,\\qquad \\text{height} = \\text{top}(x) - \\text{bottom}(x)$$',
        '$$\\text{radius} = x - 0 = x,\\qquad \\text{height} = \\sqrt{4 - 2x^2} - 0 = \\sqrt{4 - 2x^2}$$',
        '$$V = 2\\pi\\int_a^b (\\text{radius})(\\text{height})\\,dx$$', '$$V = 2\\pi\\int_0^{\\sqrt 2} x\\sqrt{4 - 2x^2}\\,dx$$',
        'Substitute \\(u = 4 - 2x^2\\): \\(du = -2\\cdot 2x\\,dx = -4x\\,dx\\), so \\(x\\,dx = -\\frac{du}{4}\\).',
        '$$\\int x\\sqrt{4 - 2x^2}\\,dx = -\\frac{1}{4}\\int u^{1/2}\\,du = -\\frac{1}{4}\\cdot\\frac{u^{3/2}}{3/2} = -\\frac{1}{4}\\cdot\\frac{2}{3}u^{3/2} = -\\frac{2}{12}u^{3/2} = -\\frac{1}{6}(4 - 2x^2)^{3/2} = F(x)$$',
        '$$F(\\sqrt 2) = -\\frac{1}{6}\\big(4 - 2\\cdot(\\sqrt 2)^2\\big)^{3/2} = -\\frac{1}{6}(4 - 2\\cdot 2)^{3/2} = -\\frac{1}{6}\\cdot 0^{3/2} = 0$$',
        '$$F(0) = -\\frac{1}{6}(4 - 2\\cdot 0^2)^{3/2} = -\\frac{1}{6}\\cdot 4^{3/2} = -\\frac{1}{6}\\cdot(\\sqrt 4)^3 = -\\frac{1}{6}\\cdot 2^3 = -\\frac{8}{6} = -\\frac{4}{3}$$',
        '$$F(\\sqrt 2) - F(0) = 0 - \\left(-\\frac{4}{3}\\right) = \\frac{4}{3}$$',
        '$$V = 2\\pi\\cdot\\frac{4}{3} = \\frac{2\\cdot 4}{3}\\pi = \\frac{8\\pi}{3} \\approx 8.3776$$'],
      truth: () => Check.simpson(x => 2 * Math.PI * x * Math.sqrt(Math.max(0, 4 - 2 * x * x)), 0, b, 20000),
    });
  }
  const HW = [
    ['6.4 #5', 'shell', r => volume(r, 'shell', 'v', false, { curves: [C('y', '2 - x^2'), C('y', 'x')], quad: true, X: { a: q(0), b: q(1), top: GP.poly(-1, 0, 2), bot: GP.x(1) }, Y: null, raw: { a: 0, b: 1, top: x => 2 - x * x, bot: x => x } })],
    ['6.4 #6', 'shell', r => volume(r, 'shell', 'h', false, { curves: [C('y', '2 - sqrt(x)'), C('y', '2'), C('x', '4')], quad: true, X: { a: q(0), b: q(4), top: GP.k(2), bot: GP.k(2).sub(GP.x(new Q(1, 2))) }, Y: { c: q(0), d: q(2), right: GP.k(4), left: GP.poly(1, -4, 4) }, raw: { a: 0, b: 4, top: () => 2, bot: x => 2 - Math.sqrt(x) } })],
    ['6.4 #9', 'shell', r => volume(r, 'shell', 'v', false, reg(7, 1))],
    ['6.4 #12', 'shell', r => volume(r, 'shell', 'v', false, reg(10, 1, 3, 3, 1))],
    ['6.4 #13', 'shell', r => volume(r, 'shell', 'h', false, reg(1, 4))],
    ['6.4 #15', 'shell', r => volume(r, 'shell', 'h', false, reg(11, 4, 2))],
    ['6.4 #20', 'shell', r => volume(r, 'shell', 'v', false, reg(1, 1))],
    ['6.4 #22', 'shell', r => volume(r, 'shell', 'h', false, reg(5, 1))],
    ['6.4 #24', 'shell', hw24],
    ['6.4 #35', 'both', r => bothWays(r, reg(13, 1), 'h')],
    ...[['39', 'v', -2], ['40', 'v', 1], ['41', 'v', 2], ['42', 'h', 1], ['43', 'h', -2], ['44', 'h', 2]].map(([n, ax, k]) => [`6.4 #${n}`, 'shell', r => volume(r, 'shell', ax, false, reg(0, 1), k)]),
    ['6.4 #53', 'washer', r => { const p = volume(r, 'washer', 'h', false, reg(8, 4)); p.statement = p.statement.replace('Use the disk/washer method', 'Use the method of your choice (disks are easiest here)'); return p; }],
    ...[0, 1, 2, 3].map(i => [`6.5 #${i + 3}`, 'arc', () => arcSetup(seq(1, 2, 2, a => a[i]))]),
    ['6.5 #7', 'arc', () => arcLength(seq('line', 2, 1, 1, 4), 'x')],
    ['6.5 #8', 'arc', () => arcLength(seq('line', -3, 4, -3, 5), 'x')],
    ['6.5 #10', 'arc', () => arcLength(seq('cosh', -1, 1), 'x')],
  ];
  function homework(r, idx) {
    const [label, card, g] = idx === undefined ? r.pick(HW) : HW[idx];
    const p = g(r);
    p.statement = `<b>Book ${label}.</b> ` + p.statement; p.hw = label; p.card = card;
    return p;
  }

  // ---------- registry ----------
  const V = (method, axis, shifted) => r => volume(r, method, axis, shifted);
  const TYPES = [
    { id: 'pos-v', sec: '6.1', name: 'Position from velocity', card: 'motion', gen: posFromV },
    { id: 'pos-a', sec: '6.1', name: 'Velocity & position from acceleration', card: 'motion', gen: posFromA },
    { id: 'disp-dist', sec: '6.1', name: 'Displacement vs distance', card: 'distance', gen: dispDist },
    { id: 'area-x', sec: '6.2', name: 'Area between curves (dx)', card: 'area-x', gen: areaX },
    { id: 'area-y', sec: '6.2', name: 'Area between curves (dy)', card: 'area-y', gen: areaY },
    { id: 'area-split', sec: '6.2', name: 'Area: curves that cross (split)', card: 'area-split', gen: areaSplit },
    { id: 'washer-x', sec: '6.3', name: 'Disk/washer about the x-axis', card: 'washer', gen: V('washer', 'h', false) },
    { id: 'washer-h', sec: '6.3', name: 'Disk/washer about y = k', card: 'washer', gen: V('washer', 'h', true) },
    { id: 'washer-y', sec: '6.3', name: 'Disk/washer about the y-axis (dy)', card: 'washer', gen: V('washer', 'v', false) },
    { id: 'washer-v', sec: '6.3', name: 'Disk/washer about x = k (dy)', card: 'washer', gen: V('washer', 'v', true) },
    { id: 'shell-y', sec: '6.4', name: 'Shells about the y-axis', card: 'shell', gen: V('shell', 'v', false) },
    { id: 'shell-v', sec: '6.4', name: 'Shells about x = k', card: 'shell', gen: V('shell', 'v', true) },
    { id: 'shell-x', sec: '6.4', name: 'Shells about the x-axis (dy)', card: 'shell', gen: V('shell', 'h', false) },
    { id: 'shell-h', sec: '6.4', name: 'Shells about y = k (dy)', card: 'shell', gen: V('shell', 'h', true) },
    { id: 'slice', sec: '6.3', name: 'General slicing (known cross-sections)', card: 'slice', gen: slicing },
    { id: 'both', sec: '6.4', name: 'Set up both ways, evaluate one', card: 'both', gen: bothWays },
    { id: 'arc-x', sec: '6.5', name: 'Arc length y = f(x)', card: 'arc', gen: r => arcLength(r, 'x') },
    { id: 'arc-y', sec: '6.5', name: 'Arc length x = g(y)', card: 'arc', gen: r => arcLength(r, 'y') },
    { id: 'arc-setup', sec: '6.5', name: 'Arc length: set up only', card: 'arc', gen: arcSetup },
    { id: 'sh-box', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Rectangular tank / sloped pool', card: 'sh-box', gen: shBox },
    { id: 'sh-cyl', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Upright cylinder', card: 'sh-cyl', gen: shCyl },
    { id: 'sh-cone', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Cone (point down or up)', card: 'sh-cone', gen: shCone },
    { id: 'sh-hcyl', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Cylinder lying on its side', card: 'sh-hcyl', gen: r => roundTrough(r, 'hcyl') },
    { id: 'sh-sphere', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Sphere / hemisphere', card: 'sh-sphere', gen: shSphere },
    { id: 'sh-tri', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Trough: triangle ends (point up/down)', card: 'sh-tri', gen: r => flatTrough(r, 'tri') },
    { id: 'sh-trap', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Trough: trapezoid ends', card: 'sh-trap', gen: r => flatTrough(r, 'trap') },
    { id: 'sh-semi', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Trough: semicircle ends', card: 'sh-semi', gen: r => roundTrough(r, 'semi') },
    { id: 'sh-para', sec: 'Shapes', head: 'Shapes: width, radius and area at height y', name: 'Trough: parabola ends', card: 'sh-para', gen: shPara },
    { id: 'spring', sec: '6.7', name: 'Work: springs', card: 'spring', gen: spring },
    { id: 'chain', sec: '6.7', name: 'Work: lifting chains/ropes', card: 'chain', gen: chain },
    { id: 'pump', sec: '6.7', name: 'Work: pumping liquids', card: 'pump', gen: pump },
    { id: 'force', sec: '6.7', name: 'Force & pressure on a plate', card: 'force', gen: force },
    { id: 'mass', sec: '6.7', name: 'Mass of a thin bar', card: 'mass', gen: mass },
    { id: 'hw', sec: 'HW', name: 'Assigned homework (exact book problems)', card: 'shell', gen: homework },
  ];
  const byId = Object.fromEntries(TYPES.map(t => [t.id, t]));

  function make(typeId, seed) {
    const t = byId[typeId];
    const r = rng(seed);
    for (let i = 0; i < 60; i++) {
      try { const p = t.gen(r); p.type = typeId; p.seed = seed; p.name = t.name; p.sec = t.sec; p.card = p.card || t.card; return p; }
      catch (e) { if (!/irrational|overflow|bad Q|ln term|0\^neg/.test(e.message)) throw e; }
    }
    throw new Error('could not generate ' + typeId);
  }

  const hwProblem = i => { const p = homework(null, i); p.type = 'hw'; p.seed = 'hw' + i; p.name = byId.hw.name; p.sec = 'HW'; return p; };
  return { TYPES, byId, make, rng, Q, GP, REGIONS, HW_COUNT: HW.length, hwProblem, _internal: { regionText } };
});
