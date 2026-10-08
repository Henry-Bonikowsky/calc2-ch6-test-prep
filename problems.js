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
    const { G, v, a, b, factor = '', factorQ = q(1), pi = false, what, unit = '' } = o;
    const F = G.integ(), Fb = F.at(b), Fa = F.at(a), val = Fb.sub(Fa).mul(factorQ);
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
    const lines = [
      `${pre}\\int_{${T(a.str())}}^{${T(b.str())}} \\left(${T(G.str(v))}\\right) d${v} = ${pre}\\Big[${T(F.str(v))}\\Big]_{${T(a.str())}}^{${T(b.str())}}`,
      `= ${pre}\\left(${T(Fb.str())} - ${Fa.v < 0 ? '\\left(' + T(Fa.str()) + '\\right)' : T(Fa.str())}\\right) = ${T(ans)}${unit ? '\\ \\text{' + unit + '}' : ''} \\approx ${fmt(Check.evalNum(ans))}`
    ];
    return { steps, lines, ans, val };
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
      sol.push(`$$R(${v}) = ${fn(Rr)},\\qquad r(${v}) = ${fn(rr)}${disk ? '\\ (\\text{disk: no hole})' : ''}$$`);
      sol.push(`$$V = \\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left[\\left(${fn(Rr)}\\right)^2 - \\left(${fn(rr)}\\right)^2\\right] ${dv} = \\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left(${fn(G)}\\right) ${dv}$$`);
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
      sol.push(`Shells are parallel to the axis ${axisLine}, so they have thickness \\(${dv}\\); ${v} runs from \\(${T(A.str())}\\) to \\(${T(B.str())}\\).`);
      sol.push(`$$\\text{radius} = ${fn(rad)},\\qquad \\text{height} = ${fn(height)}$$`);
      sol.push(`$$V = 2\\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left(${fn(rad)}\\right)\\left(${fn(height)}\\right) ${dv} = 2\\pi\\int_{${T(A.str())}}^{${T(B.str())}} \\left(${fn(G)}\\right) ${dv}$$`);
    }
    const I = integralSteps({ G, v, a: A, b: B, factor, factorQ: method === 'washer' ? q(1) : q(2), pi: true, what });
    steps.push(...I.steps);
    sol.push(`$$\\begin{aligned}V &= ${I.lines[0]}\\\\ &${I.lines[1]}\\end{aligned}$$`);
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
        `$$s(${v}) = ${T(side.str(v))},\\qquad A(${v}) = ${sh.tex}$$`,
        `$$\\begin{aligned}V &= ${I.lines[0]}\\\\ &${I.lines[1]}\\end{aligned}$$`],
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
    const I = integralSteps({ G: D, v, a, b, what: 'Area \\(A\\)' });
    steps.push(...I.steps);
    return finalize({
      statement, steps, answer: I.ans,
      solution: [`The curves meet at \\(${v} = ${T(a.str())}\\) and \\(${v} = ${T(b.str())}\\). ${names[0] === 'top' ? 'Top' : 'Right'} curve \\(${T(top.str(v))}\\), ${names[1]} curve \\(${T(bot.str(v))}\\).`,
        `$$\\begin{aligned}A &= ${I.lines[0]}\\\\ &${I.lines[1]}\\end{aligned}$$`],
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
        solution: ['The curves cross where \\(\\tan x = 1\\), at \\(x = \\pi/4\\). Left of it cos is on top; right of it sin is on top.',
          `$$A = \\int_0^{\\pi/4}(\\cos x - \\sin x)\\,dx + \\int_{\\pi/4}^{${wide ? '\\pi' : '\\pi/2'}}(\\sin x - \\cos x)\\,dx = (${T(A1)}) + (${T(A2)}) = ${T(tot)}$$`],
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
        `On \\([${a},${c}]\\) the top curve is \\(${topL.replace(/^y = /, '')}\\): area \\(= ${T(A1.str())}\\). On \\([${c},${b}]\\) the other curve is on top: area \\(= ${T(A2.str())}\\).`,
        `$$A = ${T(A1.str())} + ${T(A2.str())} = ${T(tot.str())}$$ (Integrating straight across would give ${T(net.str())}, which is wrong.)`],
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
        solution: [`$$s(t) = \\int ${A}\\sin t\\,dt = -${A}\\cos t + C,\\quad s(0) = -${A} + C = ${s0} \\Rightarrow C = ${s0 + A}$$`, `$$s(t) = ${T(sExpr)},\\qquad s(${T(Tn)}) = ${T(steps[1].ans)} = ${fmt(Check.evalNum(steps[1].ans))}$$`],
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
      solution: [`$$s(t) = s(0) + \\int_0^t v(x)\\,dx = ${s0} + ${T(v.integ().str('t'))} = ${T(S.str('t'))}$$`, `$$s(${Tn}) = ${T(S.at(Tn).str())}\\ \\text{m}$$`],
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
      solution: [`$$v(t) = ${v0} + \\int_0^t a = ${T(V.str('t'))}$$`, `$$s(t) = ${s0} + \\int_0^t v = ${T(S.str('t'))}$$`, `$$s(${Tn}) = ${T(S.at(Tn).str())}$$`],
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
        solution: [`$$\\text{displacement} = \\int_0^\\pi ${A === 1 ? '' : A}\\cos t\\,dt = 0$$`, `$$\\text{distance} = \\int_0^{\\pi/2} ${A === 1 ? '' : A}\\cos t\\,dt - \\int_{\\pi/2}^{\\pi} ${A === 1 ? '' : A}\\cos t\\,dt = ${A} + ${A} = ${2 * A}$$`],
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
        `$$\\text{displacement} = \\int_0^{${Tn}} v\\,dt = ${T(disp.str())}\\ \\text{m}$$`,
        `Pieces: ${pieces.map((p, i) => `\\(\\int_{${pts[i]}}^{${pts[i + 1]}} v\\,dt = ${T(p.str())}\\)`).join(', ')}.`,
        `$$\\text{distance} = \\int_0^{${Tn}} |v|\\,dt = ${pieces.map(p => `\\left|${T(p.str())}\\right|`).join(' + ')} = ${T(dist.str())}\\ \\text{m}$$`],
      truth: () => { let d = 0; const n = 60000, h = Tn / n; for (let i = 1; i <= n; i++) { const t = i * h; d += Math.abs(Check.simpson(x => v.num(x), (i - 1) * h, t, 2)); } return d; } });
  }

  // ---------- 6.5 arc length ----------
  function sqrtSimp(m) { let out = 1, inn = m; for (let f = 2; f * f <= inn; f++) while (inn % (f * f) === 0) { inn /= f * f; out *= f; } return [out, inn]; }
  function arcLength(r, v = 'x') {
    const kind = r.pick(v === 'x' ? ['p32', 'p32', 'sq1', 'sq2', 'sq3', 'cosh', 'line', 'lnsq'] : ['p32', 'sq1', 'sq3']);
    const w = v === 'x' ? 'y' : 'x';
    const d = `d${v}`;
    let fE, dE, oneE, integrand, F, A, B, ansS, lines, mistakesInt = [], antiE, truthF;
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
      lines = [`u = ${T(oneE)},\\ du = ${m}\\,${d}:\\quad L = \\frac{1}{${m}}\\int_{${T(U1.str())}}^{${T(U2.str())}} u^{1/2}\\,du = \\frac{2}{${3 * m}}\\Big[u^{3/2}\\Big]_{${T(U1.str())}}^{${T(U2.str())}} = ${T(ansS)}`];
      truthF = t => (2 * Math.sqrt(m) / 3) * Math.pow(t, 1.5) + shift;
    } else if (kind === 'line') {
      const m = r.pick([2, -3, 1, 3, -2, 4]), c0 = r.int(-3, 4);
      A = q(r.int(-3, 1)); B = A.add(r.int(2, 5));
      fE = `${m} ${v}${c0 ? (c0 > 0 ? ' + ' + c0 : ' - ' + -c0) : ''}`; dE = `${m}`; oneE = `${1 + m * m}`; integrand = `sqrt(${1 + m * m})`; antiE = `sqrt(${1 + m * m}) ${v}`;
      ansS = `${B.sub(A).str()} sqrt(${1 + m * m})`;
      lines = [`L = \\sqrt{${1 + m * m}}\\,(${B.str()} - (${A.str()})) = ${T(ansS)}.\\ \\text{Check with the distance formula: } \\sqrt{(\\Delta ${v})^2 + (\\Delta ${w})^2} = \\sqrt{${B.sub(A).str()}^2 + ${B.sub(A).mul(Math.abs(m)).str()}^2}\\ \\checkmark`];
      mistakesInt = [{ ans: `sqrt(${1 + Math.abs(m)})`, msg: "Square the slope: 1 + m², not 1 + m." }];
      truthF = t => m * t + c0;
    } else if (kind === 'cosh') {
      const lo = r.pick([0, -1, -2]), hi = r.pick([1, 2, 3]); // bounds ±ln(n)
      const bnd = n => n === 0 ? '0' : n < 0 ? `-ln(${-n + 1})` : `ln(${n + 1})`;
      const val = n => n === 0 ? q(0) : n < 0 ? new Q(-n + 1, 1).sub(new Q(1, -n + 1)).div(-2) : new Q(n + 1).sub(new Q(1, n + 1)).div(2);
      A = { str: () => bnd(lo), v: Check.evalNum(bnd(lo)) }; B = { str: () => bnd(hi), v: Check.evalNum(bnd(hi)) };
      fE = `(e^${v} + e^(-${v})) / 2`; dE = `(e^${v} - e^(-${v})) / 2`; oneE = `1 + ((e^${v} - e^(-${v})) / 2)^2`; integrand = `(e^${v} + e^(-${v})) / 2`; antiE = `(e^${v} - e^(-${v})) / 2`;
      ansS = val(hi).sub(val(lo)).str();
      lines = [`1 + \\left(\\tfrac{e^${v} - e^{-${v}}}{2}\\right)^2 = \\left(\\tfrac{e^${v} + e^{-${v}}}{2}\\right)^2,\\ \\text{so}\\ L = \\Big[\\tfrac{e^${v} - e^{-${v}}}{2}\\Big]_{${T(A.str())}}^{${T(B.str())}} = ${T(ansS)}`];
      truthF = t => (Math.exp(t) + Math.exp(-t)) / 2;
    } else if (kind === 'lnsq') {
      A = q(1); const bb = r.pick([2, 3, 4, 'e']); B = bb === 'e' ? { str: () => 'e', v: Math.E } : q(bb);
      fE = `${v}^2 / 4 - ln(${v}) / 2`; dE = `${v} / 2 - 1 / (2 ${v})`; oneE = `1 + (${v} / 2 - 1 / (2 ${v}))^2`; integrand = `${v} / 2 + 1 / (2 ${v})`; antiE = `${v}^2 / 4 + ln(${v}) / 2`;
      ansS = bb === 'e' ? '(e^2 + 1) / 4' : `${new Q(bb * bb - 1, 4).str()} + ln(${bb}) / 2`;
      lines = [`1 + (f')^2 = \\left(\\tfrac{${v}}{2} + \\tfrac{1}{2${v}}\\right)^2,\\ L = \\Big[\\tfrac{${v}^2}{4} + \\tfrac{\\ln ${v}}{2}\\Big]_{1}^{${bb}} = ${T(ansS)}`];
      truthF = t => t * t / 4 - Math.log(t) / 2;
    } else { // perfect-square families: f' = P - N with 4PN = 1, integrand P + N
      const fam = { sq1: [GP.x(3, new Q(1, 6)), GP.x(-1, new Q(1, 2))], sq2: [GP.x(4, new Q(1, 8)), GP.x(-2, new Q(1, 4))], sq3: [GP.x(3, new Q(1, 3)), GP.x(-1, new Q(1, 4))] }[kind];
      const f = fam[0].add(fam[1]), fp = f.deriv();
      const P = new GP(fp.t.filter(t => t.c.v > 0)), N = new GP(fp.t.filter(t => t.c.v < 0)).neg();
      const G = P.add(N);
      A = q(r.int(1, 2)); B = A.add(r.int(1, 2));
      fE = f.str(v); dE = fp.str(v); oneE = `1 + (${fp.str(v)})^2`; integrand = G.str(v); antiE = G.integ().str(v);
      ansS = G.integ().at(B).sub(G.integ().at(A)).str();
      lines = [`1 + (f')^2 = \\left(${T(G.str(v))}\\right)^2 \\text{ (perfect square)},\\ L = \\int_{${A.str()}}^{${B.str()}} \\left(${T(G.str(v))}\\right) ${d} = \\Big[${T(G.integ().str(v))}\\Big]_{${A.str()}}^{${B.str()}} = ${T(ansS)}`];
      mistakesInt = [{ ans: `sqrt(1 + ${fp.str(v)})`, msg: "Square f' before adding 1." }, { ans: fp.str(v), msg: "1 + (f')² is a perfect square of the SUM: (P + N)², not the difference. The √ gives P + N." }];
      truthF = t => f.num(t);
    }
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
      solution: [`$$${w}' = ${T(dE)},\\qquad 1 + (${w}')^2 = ${T(oneE)}$$`, `$$L = \\int_{${T(A.str())}}^{${T(B.str())}} ${Check.tex(integrand)}\\,${d}$$`, `$$${lines[0]} \\approx ${fmt(Check.evalNum(ansS))}$$`],
      truth: () => { let s = 0; const n = 200000, h = (hi - lo) / n; let py = truthF(lo); for (let i = 1; i <= n; i++) { const t = lo + i * h, yv = truthF(t); s += Math.hypot(h, yv - py); py = yv; } return s; },
      curve: truthF, fE, dE, oneE, integrandE: integrand, v,
    });
  }
  function arcSetup(r) {
    const opts = [
      { f: 'x^3 + 2', d: '3 x^2', i: 'sqrt(1 + 9 x^4)', a: -2, b: 5, g: x => x ** 3 + 2 },
      { f: '2 cos(3 x)', d: '-6 sin(3 x)', i: 'sqrt(1 + 36 sin(3 x)^2)', a: '-pi', b: 'pi', g: x => 2 * Math.cos(3 * x) },
      { f: 'e^(-2 x)', d: '-2 e^(-2 x)', i: 'sqrt(1 + 4 e^(-4 x))', a: 0, b: 2, g: x => Math.exp(-2 * x) },
      { f: 'ln(x)', d: '1 / x', i: 'sqrt(1 + 1 / x^2)', a: 1, b: 10, g: Math.log },
      { f: 'x^2', d: '2 x', i: 'sqrt(1 + 4 x^2)', a: 0, b: r.int(1, 3), g: x => x * x },
      { f: 'sin(x)', d: 'cos(x)', i: 'sqrt(1 + cos(x)^2)', a: 0, b: 'pi', g: Math.sin },
      (k => ({ f: `${k} x^2 - 1`, d: `${2 * k} x`, i: `sqrt(1 + ${4 * k * k} x^2)`, a: 0, b: 1, g: x => k * x * x - 1 }))(r.int(2, 4)),
      { f: 'tan(x)', d: 'sec(x)^2', i: 'sqrt(1 + sec(x)^4)', a: 0, b: 'pi/4', g: Math.tan },
      { f: '1 / x', d: '-1 / x^2', i: 'sqrt(1 + 1 / x^4)', a: 1, b: r.int(2, 5), g: x => 1 / x },
    ];
    const o = r.pick(opts);
    const a = Check.evalNum(`${o.a}`), b = Check.evalNum(`${o.b}`);
    const steps = [
      { id: 'd', label: "\\(f'(x)\\)", kind: 'expr', v: 'x', lo: a, hi: b, ans: o.d, hint: 'Chain rule where needed.' },
      { id: 'integrand', label: 'Integrand: \\(L = \\int_a^b(\\;?\\;)\\,dx\\)', kind: 'expr', v: 'x', lo: a, hi: b, ans: o.i, mistakes: [{ ans: `sqrt(1 + ${pr(o.d)})`, msg: "Square f'." }, { ans: `1 + (${o.d})^2`, msg: 'Missing the square root.' }, { ans: `sqrt(1 + (${o.f})^2)`, msg: "Use f', not f." }], hint: "√(1 + (f')²), simplified." },
      { id: 'a', label: 'Lower limit', kind: 'num', ans: `${o.a}` }, { id: 'b', label: 'Upper limit', kind: 'num', ans: `${o.b}` },
    ];
    return finalize({ statement: `Write and simplify, but do not evaluate, an integral with respect to \\(x\\) that gives the length of \\(y = ${T(o.f)}\\) on \\([${T(String(o.a))}, ${T(String(o.b))}]\\).`, steps, answer: null,
      solution: [`$$f'(x) = ${T(o.d)},\\qquad L = \\int_{${T(String(o.a))}}^{${T(String(o.b))}} ${T(o.i)}\\,dx$$`, `(Numerically \\(L \\approx ${fmt(Check.simpson(x => Check.evalNum(o.i, { x }), a, b, 4000))}\\) with a calculator; not needed here.)`],
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
      kSol = `F = kx:\\ ${Fn} = k(${new Q(dcm, 100).str()}) \\Rightarrow k = ${T(k.str())}\\ \\text{N/m}`;
    } else if (kind === 'lengths') {
      const L0 = r.pick([10, 12, 20, 25, 30]), L1 = L0 + r.pick([2, 4, 5, 10]), Fn = r.pick([20, 25, 30, 40, 50]);
      const L2 = L0 + r.pick([0, 2, 5]), L3 = L2 + r.pick([3, 5, 10]);
      k = new Q(Fn * 100, L1 - L0); a = new Q(L2 - L0, 100); b = new Q(L3 - L0, 100);
      statement = `A spring has natural length ${L0} cm. A force of ${Fn} N holds it at a length of ${L1} cm. How much work is done stretching it from a length of ${L2} cm to a length of ${L3} cm?`;
      kMistakes = [{ ans: new Q(Fn * 100, L1).str(), msg: `x is the stretch beyond natural length: ${L1} − ${L0} = ${L1 - L0} cm, not ${L1} cm.` }, { ans: new Q(Fn, L1 - L0).str(), msg: 'Convert cm to m first.' }];
      aMistakes = [{ ans: new Q(L2, 100).str(), msg: `x is measured from the natural length: ${L2} − ${L0} = ${L2 - L0} cm.` }];
      bMistakes = [{ ans: new Q(L3, 100).str(), msg: `x is measured from the natural length: ${L3} − ${L0} = ${L3 - L0} cm = ${(L3 - L0) / 100} m.` }, { ans: `${L3 - L0}`, msg: 'Use meters: 1 cm = 0.01 m.' }];
      kSol = `x = \\text{stretch beyond natural length} = ${L1 - L0}\\text{ cm} = ${(L1 - L0) / 100}\\text{ m},\\ k = \\frac{${Fn}}{${(L1 - L0) / 100}} = ${T(k.str())}\\ \\text{N/m}`;
    } else {
      const W0 = r.pick([2, 3, 4, 6, 8, 9]), d0 = r.pick([new Q(1, 10), new Q(1, 5), new Q(1, 2), q(1)]);
      k = q(2 * W0).div(d0.mul(d0)); const extra = r.pick([new Q(1, 10), new Q(1, 5), new Q(1, 2)]);
      a = d0; b = d0.add(extra);
      statement = `It takes ${W0} J of work to stretch a spring ${d0.v} m from its natural length. How much work is needed to stretch it an additional ${extra.v} m?`;
      kMistakes = [{ ans: q(W0).div(d0).str(), msg: 'Work is not force: W = ∫₀ᵈ kx dx = kd²/2, so k = 2W/d².' }, { ans: q(W0).div(d0.mul(d0)).str(), msg: 'W = kd²/2, so k = 2W/d² (you lost the 2).' }];
      bMistakes = [{ ans: extra.str(), msg: `"Additional" means it starts already stretched ${d0.v} m and ends at ${b.v} m.` }];
      kSol = `${W0} = \\int_0^{${d0.v}} kx\\,dx = \\frac{k}{2}(${d0.v})^2 \\Rightarrow k = ${T(k.str())}\\ \\text{N/m}`;
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
      solution: [`$$${kSol}$$`, `$$W = \\int_{${a.v}}^{${b.v}} ${T(k.str())}x\\,dx = \\frac{${T(k.str())}}{2}\\left[x^2\\right]_{${a.v}}^{${b.v}} = ${T(W.str())}\\ \\text{J} \\approx ${fmt(W.v)}\\ \\text{J}$$`],
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
    const deltaStep = { id: 'delta', label: `Weight per unit length (${us ? 'lb/ft' : 'N/m'})`, kind: 'num', ans: delta.str(), mistakes: us ? [] : [{ ans: rho.str(), msg: 'Mass is not weight: multiply kg/m by g = 9.8 m/s² to get N/m.' }], hint: us ? 'Already given as a weight per foot.' : 'Weight = mass × g: ρ·9.8.' };
    const integrandStep = { id: 'integrand', label: `Integrand: \\(W = \\int_0^{?} (\\;?\\;)\\,dy\\), \\(y\\) = distance of a slice below the top`, kind: 'expr', v: 'y', lo: 0, hi: L, ans: `${delta.str()} * y`, mistakes: [{ ans: `${delta.str()} * (${L} - y)`, msg: `With y measured down from the top, a slice at depth y is lifted y, not ${L} − y.` }, { ans: `${rho.str()} * y`, msg: 'Use weight per length (ρg), not mass per length.' }], hint: 'Each slice (weight δ dy) at depth y rises y.' };
    if (variant === 'all') {
      W = delta.mul(L * L).div(2);
      statement = `${what} hangs from the top of a tall building. How much work is required to pull the entire ${obj} to the top?`;
      steps = [deltaStep, integrandStep, { id: 'final', label: `Work (${unitW})`, kind: 'num', ans: W.str(), mistakes: [{ ans: delta.mul(L * L).str(), msg: 'Forgot the 1/2: ∫₀ᴸ δy dy = δL²/2.' }, { ans: delta.mul(L).str(), msg: 'Each slice rises a different distance, so integrate: δ∫₀ᴸ y dy.' }], hint: 'δ L²/2.' }];
      sol = [`$$W = \\int_0^{${L}} ${T(delta.str())}\\,y\\,dy = ${T(delta.str())}\\cdot\\frac{${L}^2}{2} = ${T(W.str())}\\ \\text{${unitW}}$$`];
    } else if (variant === 'half') {
      const hq = new Q(L, 2), h = hq.v;
      const Wtop = delta.mul(hq).mul(hq).div(2), Wbot = delta.mul(hq).mul(hq);
      W = Wtop.add(Wbot);
      statement = `${what} hangs from the top of a tall building. How much work is required to wind up the top half of the ${obj}? (Winding up the top half also lifts the bottom half by ${h} ${unitL}.)`;
      steps = [deltaStep,
        { id: 'top', label: `Work to wind the top half (${unitW})`, kind: 'num', ans: Wtop.str(), hint: `δ∫₀^${h} y dy.` },
        { id: 'bot', label: `Work to lift the bottom half ${h} ${unitL} (${unitW})`, kind: 'num', ans: Wbot.str(), mistakes: [{ ans: delta.mul(q(L * L).sub(hq.mul(hq))).div(2).str(), msg: `The bottom half does not reach the top; every bottom slice rises exactly ${h} ${unitL}: (weight of bottom half)(${h}).` }], hint: `Weight of bottom half = δ·${h}; it all rises ${h}.` },
        { id: 'final', label: `Total work (${unitW})`, kind: 'num', ans: W.str(), mistakes: [{ ans: Wtop.str(), msg: 'Add the work of raising the bottom half too.' }], hint: 'Add the two parts.' }];
      sol = [`$$W_{\\text{top}} = \\int_0^{${h}} ${T(delta.str())}\\,y\\,dy = ${T(Wtop.str())},\\qquad W_{\\text{bottom}} = (${T(delta.str())}\\cdot ${h})(${h}) = ${T(Wbot.str())}$$`, `$$W = ${T(W.str())}\\ \\text{${unitW}}$$`];
    } else {
      const Wc = delta.mul(L * L).div(2), Wl = us ? q(load).mul(L) : q(load).mul(G_M).mul(L);
      W = Wc.add(Wl);
      statement = `${what} hangs from the top of a tall building with a ${us ? load + '-lb' : load + '-kg'} weight attached to its lower end. How much work is required to pull the ${obj} and the weight to the top?`;
      steps = [deltaStep, integrandStep,
        { id: 'chainW', label: `Work for the ${obj} alone (${unitW})`, kind: 'num', ans: Wc.str(), hint: 'δL²/2.' },
        { id: 'loadW', label: `Work for the weight alone (${unitW})`, kind: 'num', ans: Wl.str(), mistakes: us ? [] : [{ ans: q(load * L).str(), msg: 'Weight = mass × 9.8.' }], hint: `Constant force × ${L} ${unitL}.` },
        { id: 'final', label: `Total work (${unitW})`, kind: 'num', ans: W.str(), mistakes: [], hint: 'Add them.' }];
      sol = [`$$W_{${obj}} = \\int_0^{${L}} ${T(delta.str())}\\,y\\,dy = ${T(Wc.str())},\\qquad W_{\\text{load}} = ${us ? load : load + '(9.8)'}(${L}) = ${T(Wl.str())}$$`, `$$W = ${T(W.str())}\\ \\text{${unitW}}$$`];
    }
    if (!us) steps[steps.length - 1].mistakes.push({ ans: W.div(G_M).str(), msg: 'You left out g = 9.8.' });
    return finalize({ statement: statement + (us ? '' : ' Use g = 9.8 m/s².'), steps, answer: W.str(), solution: [`Measure \\(y\\) down from the top. A slice at depth \\(y\\) has weight \\(${T(delta.str())}\\,dy\\) and rises \\(y\\).`, ...sol],
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
    let A, H, desc, Atex, raw, areaMistakes = [], isPi = false;
    if (shape === 'cyl') { const rad = r.pick([1, 2, 3, 4]); H = r.pick([2, 4, 5, 6, 8]); A = GP.k(rad * rad); isPi = true; desc = `A cylindrical tank (standing upright) has radius ${rad} ${u} and height ${H} ${u}`; raw = y => Math.PI * rad * rad; }
    else if (shape === 'box') { const l = r.pick([2, 3, 4, 5]), w = r.pick([2, 3, 4]); H = r.pick([2, 3, 4, 5]); A = GP.k(l * w); desc = `A rectangular tank has a base ${l} ${u} by ${w} ${u} and height ${H} ${u}`; raw = () => l * w; }
    else if (shape === 'cone') { const R0 = r.pick([1, 2, 3, 4]); H = r.pick([2, 3, 4, 6]); A = GP.x(2, new Q(R0 * R0, H * H)); isPi = true; desc = `A conical tank with its vertex pointing down has radius ${R0} ${u} at the top and height ${H} ${u}`; raw = y => Math.PI * (R0 * y / H) ** 2; areaMistakes = [{ ans: `${R0 * R0}`, msg: `The radius shrinks toward the vertex: by similar triangles r(y) = (${R0}/${H})y, so A = π r² uses that.` }]; }
    else if (shape === 'trough') { const len = r.pick([4, 5, 6, 10]), w = r.pick([2, 3, 4]); H = r.pick([1, 2, 3]); A = GP.x(1, new Q(len * w, H)); desc = `A trough ${len} ${u} long has cross-sections that are isosceles triangles (vertex down) ${w} ${u} wide at the top and ${H} ${u} tall`; raw = y => len * w * y / H; areaMistakes = [{ ans: `${len * w}`, msg: `The width shrinks toward the bottom: w(y) = (${w}/${H})y, so A(y) = ${len}·w(y).` }]; }
    else { const R0 = r.pick([1, 2, 3, 4]); H = R0; A = GP.poly(-1, 2 * R0, 0); isPi = true; desc = `A hemispherical bowl (flat side up) has radius ${R0} ${u}`; raw = y => Math.PI * (R0 * R0 - (R0 - y) ** 2); areaMistakes = [{ ans: `${R0 * R0}`, msg: `The circle radius depends on height: r² = ${R0}² − (${R0} − y)².` }]; }
    const depthFrac = r.pick([1, 1, new Q(1, 2)]), D = q(H).mul(depthFrac);
    const out = r.pick([0, 0, 1, 2]);
    const top = H + out;
    const lift = GP.poly(-1, top);
    const Gint = A.mul(lift);
    const filled = depthFrac === 1 || (depthFrac.eq && depthFrac.eq(1)) ? 'is full of water' : `is filled with water to a depth of ${D.v} ${u}`;
    const dest = out ? `to an outlet ${out} ${u} above the top of the tank` : 'out over the top of the tank';
    const Aexpr = isPi ? `pi * (${A.str('y')})` : A.str('y');
    const F = Gint.integ(), raw0 = F.at(D).sub(F.at(0)), val = raw0.mul(wd);
    const ans = isPi ? exactPi(val, true) : val.str();
    const steps = [
      { id: 'A', label: `Cross-sectional area \\(A(y)\\) of a horizontal slice at height \\(y\\) (from the bottom)`, kind: 'expr', v: 'y', lo: 0, hi: H, ans: Aexpr, mistakes: areaMistakes.map(m => ({ ...m, ans: isPi ? `pi * ${m.ans}` : m.ans })).concat(isPi ? [{ ans: A.str('y'), msg: 'A circle\'s area is πr²: include π.' }] : []), hint: 'Slice horizontally; area of that slice as a function of its height y.' },
      { id: 'lift', label: `Distance the slice at height \\(y\\) must be lifted`, kind: 'expr', v: 'y', lo: 0, hi: H, ans: lift.str('y'), mistakes: [{ ans: 'y', msg: `y is how high the slice already is. It must rise to ${top}: distance = ${top} − y.` }, ...(out ? [{ ans: GP.poly(-1, H).str('y'), msg: `The water goes to the outlet ${out} ${u} above the top, so it rises to ${top}, not ${H}.` }] : [])], hint: `It must reach height ${top}.` },
      { id: 'a', label: 'Lower limit (y)', kind: 'num', ans: '0', hint: 'Bottom of the water.' },
      { id: 'b', label: 'Upper limit (y)', kind: 'num', ans: D.str(), mistakes: D.eq(H) ? [] : [{ ans: `${H}`, msg: `Only the water moves: it goes up to ${D.v}, not the tank height.` }], hint: 'Top of the water surface.' },
      { id: 'final', label: `Work (${us ? 'ft·lb' : 'J'})`, kind: 'num', ans: ans, mistakes: [{ ans: isPi ? exactPi(raw0, true) : raw0.str(), msg: `Multiply by the weight density ${us ? '62.5 lb/ft³' : 'ρg = 1000·9.8 = 9800 N/m³'}.` }, ...(us ? [] : [{ ans: isPi ? exactPi(raw0.mul(1000), true) : raw0.mul(1000).str(), msg: 'Mass is not weight: use ρg = 9800, not ρ = 1000.' }])], hint: `W = ${us ? '62.5' : '9800'}∫ A(y)·(lift) dy.` },
    ];
    return finalize({
      statement: `${desc} and ${filled}. How much work is required to pump all of the water ${dest}? Use ${us ? 'a weight density of 62.5 lb/ft³' : 'ρ = 1000 kg/m³ and g = 9.8 m/s²'}; measure \\(y\\) up from the bottom of the tank.`,
      steps, answer: ans,
      solution: [`Slice at height \\(y\\): area \\(A(y) = ${T(Aexpr)}\\), weight \\(${us ? '62.5' : '9800'}\\,A(y)\\,dy\\), lifted \\(${T(lift.str('y'))}\\).`,
        `$$W = ${us ? '62.5' : '9800'}\\int_0^{${T(D.str())}} ${T(Aexpr)}\\,(${T(lift.str('y'))})\\,dy = ${T(ans)}\\ \\text{${us ? 'ft·lb' : 'J'}} \\approx ${fmt(Check.evalNum(ans))}$$`],
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
      solution: [`Surface at \\(y = ${a}\\). Strip at height \\(y\\): width \\(${T(w.str('y'))}\\), depth \\(${T(depth.str('y'))}\\), pressure \\(${us ? '62.5' : '9800'}\\cdot\\text{depth}\\).`,
        `$$F = ${us ? '62.5' : '9800'}\\int_0^{${Hp}} (${T(depth.str('y'))})(${T(w.str('y'))})\\,dy = ${T(val.str())}\\ \\text{${us ? 'lb' : 'N'}}$$`],
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
      solution: [`$$m = \\int_0^{${L}} (${T(rho.str('x'))})\\,dx = \\Big[${T(F.str('x'))}\\Big]_0^{${L}} = ${T(M.str())}\\ \\text{kg}$$`],
      truth: () => Check.simpson(x => rho.num(x), 0, L, 200) });
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
      solution: ['Shells are parallel to the \\(y\\)-axis, so they have thickness \\(dx\\); \\(x\\) runs from \\(0\\) to \\(\\sqrt 2\\) (where \\(4 - 2x^2 = 0\\)).',
        '$$\\text{radius} = x,\\qquad \\text{height} = \\sqrt{4 - 2x^2}$$',
        '$$V = 2\\pi\\int_0^{\\sqrt 2} x\\sqrt{4 - 2x^2}\\,dx,\\quad u = 4 - 2x^2,\\ du = -4x\\,dx$$',
        '$$V = 2\\pi\\Big[-\\tfrac{1}{6}(4 - 2x^2)^{3/2}\\Big]_0^{\\sqrt 2} = 2\\pi\\left(0 + \\tfrac{8}{6}\\right) = \\frac{8\\pi}{3} \\approx 8.3776$$'],
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
