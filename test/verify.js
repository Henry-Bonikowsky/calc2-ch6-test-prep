// Verifies every generated problem: answer key vs independent numerical computation,
// step answers accepted by the checker, mistake hints rejected, internal consistency, KaTeX renders.
// Usage: node test/verify.js [problemsPerType=300]
const path = require('path');
const root = path.join(__dirname, '..');
const Check = require(path.join(root, 'check.js'));
const Gen = require(path.join(root, 'problems.js'));
const Drill = require(path.join(root, 'drill.js'));
const katex = require(path.join(root, 'vendor/katex/katex.min.js'));

const N = Number(process.argv[2] || 300);
const fails = [];
let checks = 0;
const fail = (p, msg) => { if (fails.length < 60) fails.push(`[${p.type} seed ${p.seed}] ${msg}`); else fails.length++; };
const ok = (cond, p, msg) => { checks++; if (!cond) fail(p, msg); };
const rel = (a, b, tol) => Math.abs(a - b) <= tol * Math.max(1, Math.abs(a), Math.abs(b));

function texSegments(html) {
  const out = [];
  const re = /\\\((.+?)\\\)|\\\[(.+?)\\\]|\$\$(.+?)\$\$/gs;
  let m; while ((m = re.exec(html))) out.push({ tex: m[1] || m[2] || m[3], display: !m[1] });
  return out;
}
function renders(p, html, where) {
  for (const s of texSegments(html)) {
    checks++;
    try { katex.renderToString(s.tex, { throwOnError: true, displayMode: s.display }); }
    catch (e) { fail(p, `KaTeX error in ${where}: ${e.message.slice(0, 120)} :: ${s.tex.slice(0, 120)}`); }
  }
}
const scope = (v, x) => ({ [v]: x });
const cache = new Map();
const fnOf = (expr, v) => { const key = expr + '|' + v; if (!cache.has(key)) { const f = Check.compile(String(expr)).fn; cache.set(key, x => f({ [v]: x })); } return cache.get(key); };
// Stop 1e-13 short of b: float sqrt(2) overshoots, and sqrt(4 - 2x^2) is NaN past the edge.
const integ = (f, a, b) => Check.simpson(f, a, b - (b - a) * 1e-13, 20000);
const numDeriv = (f, x) => { const h = 1e-5 * Math.max(1, Math.abs(x)); return (f(x + h) - f(x - h)) / (2 * h); };

function verifyRegion(p, R) {
  const { raw, X, Y, curves } = R;
  const onSomeCurve = (x, y) => curves.some(c => {
    const val = Check.evalNum(c.e, { x, y });
    return c.t === 'y' ? Math.abs(val - y) < 1e-7 * Math.max(1, Math.abs(y)) : Math.abs(val - x) < 1e-7 * Math.max(1, Math.abs(x));
  });
  for (const x of Check.samples(raw.a, raw.b, 7)) {
    ok(rel(X.top.num(x), raw.top(x), 1e-9) && rel(X.bot.num(x), raw.bot(x), 1e-9), p, `X form disagrees with raw closures at x=${x}`);
    ok(raw.top(x) >= raw.bot(x) - 1e-12, p, `top below bottom at x=${x}`);
    ok(onSomeCurve(x, raw.top(x)) && onSomeCurve(x, raw.bot(x)), p, `raw boundary at x=${x} is not one of the stated curves`);
  }
  if (Y) {
    for (const y of Check.samples(Y.c.v, Y.d.v, 7)) {
      ok(Y.right.num(y) >= Y.left.num(y) - 1e-12, p, `right < left at y=${y}`);
      ok(onSomeCurve(Y.right.num(y), y) && onSomeCurve(Y.left.num(y), y), p, `Y-form boundary at y=${y} not on a stated curve`);
    }
    // Same region both ways: area dx == area dy
    const ax = Check.simpson(x => raw.top(x) - raw.bot(x), raw.a, raw.b, 20000);
    const ay = Check.simpson(y => Y.right.num(y) - Y.left.num(y), Y.c.v, Y.d.v, 20000);
    ok(rel(ax, ay, 1e-5), p, `area dx ${ax} != area dy ${ay}`);
  }
}

function verifyProblem(p) {
  renders(p, p.statement, 'statement');
  for (const s of p.solution) renders(p, s, 'solution');
  verifyWork(p);
  const stepById = Object.fromEntries(p.steps.map(s => [s.id, s]));
  for (const s of p.steps) {
    renders(p, s.label, 'label ' + s.id);
    try { katex.renderToString(Check.tex(s.ans), { throwOnError: true }); checks++; } catch (e) { fail(p, `answer tex for ${s.id}: ${e.message.slice(0, 100)}`); }
    const g = Check.grade(s, s.ans);
    ok(g.ok, p, `correct answer rejected at step ${s.id}: ${s.ans} (${g.msg})`);
    for (const m of s.mistakes || []) {
      const gm = Check.grade(s, m.ans);
      ok(!gm.ok, p, `mistake accepted as correct at ${s.id}: ${m.ans}`);
      ok(gm.msg === m.msg, p, `mistake hint mismatch at ${s.id} for ${m.ans}: got "${gm.msg}"`);
    }
    if (s.kind !== 'num') ok(isFinite(s.lo) && isFinite(s.hi) && s.hi > s.lo, p, `bad sample range at ${s.id}`);
  }
  // Answer key vs independent truth.
  if (p.truth) {
    const t = p.truth();
    ok(isFinite(p.value) && rel(p.value, t, 2e-5), p, `ANSWER KEY ${p.answer} = ${p.value} but independent truth = ${t}`);
    const fin = stepById.final;
    if (fin) ok(rel(Check.evalNum(fin.ans), t, 2e-5), p, `final step answer ${fin.ans} != truth ${t}`);
  }
  // Integrand step x constant == final value (when the problem has integrand + bounds).
  const fac = p.fac || (p.type === 'hw' && p.curve ? 1 : 0) || { 'washer-x': Math.PI, 'washer-h': Math.PI, 'washer-y': Math.PI, 'washer-v': Math.PI, 'shell-y': 2 * Math.PI, 'shell-v': 2 * Math.PI, 'shell-x': 2 * Math.PI, 'shell-h': 2 * Math.PI, 'area-x': 1, 'area-y': 1, 'arc-x': 1, 'arc-y': 1, 'spring': 1 }[p.type];
  if (fac && stepById.integrand) {
    const s = stepById.integrand, a = Check.evalNum(stepById.a ? stepById.a.ans : p.steps.find(x => x.kind === 'anti') ? s.lo : s.lo), b = Check.evalNum(stepById.b ? stepById.b.ans : s.hi);
    const lo = stepById.a ? a : s.lo, hi = stepById.b ? b : s.hi;
    const I = integ(fnOf(s.ans, s.v), lo, hi);
    ok(rel(fac * I, p.value, 2e-5), p, `factor*∫integrand = ${fac * I} but value = ${p.value}`);
  }
  if (p.twin) {
    for (const [tag, f] of [['w', Math.PI], ['s', 2 * Math.PI]]) {
      const s = stepById[tag + '-integrand'], a = Check.evalNum(stepById[tag + '-a'].ans), b = Check.evalNum(stepById[tag + '-b'].ans);
      const I = integ(fnOf(s.ans, s.v), a, b);
      ok(rel(f * I, p.value, 2e-5), p, `${tag} setup gives ${f * I}, answer ${p.value}`);
    }
    ok(rel(Check.evalNum(p.twin), p.value, 1e-9), p, `washer ${p.answer} != shell ${p.twin}`);
  }
  // Anti step: F(b) - F(a) consistent with integrand over the bounds.
  if (stepById.anti && stepById.a && stepById.b) {
    const s = stepById.anti, a = Check.evalNum(stepById.a.ans), b = Check.evalNum(stepById.b.ans);
    const F = x => Check.evalNum(s.ans, scope(s.v, x));
    const I = integ(fnOf(s.integrand, s.v), a, b);
    ok(rel(F(b) - F(a), I, 1e-5), p, `F(b)-F(a) = ${F(b) - F(a)} but ∫ = ${I}`);
  }
  if (p.region) verifyRegion(p, p.region);
  // Volume radius / height sanity: positive on the interval.
  for (const id of ['R', 'r', 'radius', 'height', 'lift', 'depth', 'w', 'A', 'side', 'len', 'rad', 'half', 'wid']) {
    const s = stepById[id]; if (!s) continue;
    for (const x of Check.samples(s.lo, s.hi, 7)) ok(Check.evalNum(s.ans, scope(s.v, x)) >= -1e-12, p, `${id} negative at ${x}`);
  }
  if (stepById.R && stepById.r) for (const x of Check.samples(stepById.R.lo, stepById.R.hi, 7)) ok(Check.evalNum(stepById.R.ans, { [stepById.R.v]: x }) >= Check.evalNum(stepById.r.ans, { [stepById.r.v]: x }) - 1e-12, p, 'R < r');
  // Arc length internals.
  if (p.curve) {
    const v = p.v, f = x => Check.evalNum(p.fE, scope(v, x)), d = stepById.d, lo = d.lo, hi = d.hi;
    for (const x of Check.samples(lo, hi, 7)) {
      ok(rel(f(x), p.curve(x), 1e-9), p, `stated curve != closure at ${x}`);
      ok(rel(Check.evalNum(d.ans, scope(v, x)), numDeriv(f, x), 1e-5), p, `derivative step wrong at ${x}`);
      ok(rel(Check.evalNum(stepById.integrand.ans, scope(v, x)) ** 2, Check.evalNum(stepById.one.ans, scope(v, x)), 1e-9), p, `integrand^2 != 1+f'^2 at ${x}`);
    }
  }
  if (p.setupOnly) {
    const o = p.setupOnly, f = x => Check.evalNum(o.f, { x });
    for (const x of Check.samples(o.a, o.b, 7)) {
      ok(rel(f(x), o.g(x), 1e-9), p, 'setup curve mismatch');
      ok(rel(Check.evalNum(o.d, { x }), numDeriv(f, x), 1e-5), p, `setup derivative wrong at ${x}`);
    }
    const I = Check.simpson(fnOf(o.integrand, 'x'), o.a, o.b, 20000);
    let L = 0; const n = 200000, h = (o.b - o.a) / n; let py = o.g(o.a);
    for (let i = 1; i <= n; i++) { const y = o.g(o.a + i * h); L += Math.hypot(h, y - py); py = y; }
    ok(rel(I, L, 1e-5), p, `setup integral ${I} != polyline length ${L}`);
  }
  // Shapes: the width/radius and A(y) steps agree with plain-geometry closures at every sample height.
  if (p.shape) {
    const sh = p.shape, unk = p.steps[0];
    for (const y of Check.samples(sh.lo, sh.hi, 9)) {
      ok(rel(Check.evalNum(unk.ans, { y }), sh.unk(y), 1e-9), p, `${unk.id} step ${unk.ans} != geometry at y=${y}`);
      ok(rel(Check.evalNum(stepById.A.ans, { y }), sh.A(y), 1e-9), p, `A step ${stepById.A.ans} != geometry at y=${y}`);
    }
    ok(rel(Check.evalNum(stepById.A.ans, { y: sh.y0 }), p.value, 1e-9), p, 'A(y) step at y0 != final answer');
  }
  if (p.meta && stepById.s) ok(rel(Check.evalNum(stepById.s.ans, { t: p.meta.T }), p.value, 1e-9) && rel(Check.evalNum(stepById.s.ans, { t: 0 }), p.meta.s0, 1e-9), p, 's(t) step inconsistent with final or s(0)');
  if (p.meta && stepById.v && stepById.s) {
    for (const t of Check.samples(0, p.meta.T, 5)) ok(rel(numDeriv(x => Check.evalNum(stepById.s.ans, { t: x }), t), Check.evalNum(stepById.v.ans, { t }), 1e-5), p, "s' != v");
  }
}

// Worked solution arithmetic: in every equation chain, any two neighbouring all-number sides
// ("19.6 \times 450 = 8820", "-8\cdot 36 + 96\cdot 6 = -288 + 576") must be equal, and the solution
// must arrive at the answer key. Sides with letters (F(6), x^2, \sqrt, \approx, ...) are skipped.
function numSide(s) {
  // trailing unit dropped; a named function like \text{top}(4) is not a number
  let e = s.replace(/(\\ )*\\text\{(?! cm)[^{}]*\}\s*$/, '').replace(/\\text\{[^{}]*\}/g, 'T').replace(/\\left|\\right|\\big|\\Big|\\[,;!]|\\ |\\quad|\\qquad/g, ' ');
  e = e.replace(/\\sqrt\{([^{}]*)\}/g, '(($1)**0.5)').replace(/\\sqrt\s*(\d+)/g, '($1**0.5)');
  for (let k = 0; k < 4; k++) e = e.replace(/\\frac\{([^{}]*)\}\{([^{}]*)\}/g, '(($1)/($2))');
  e = e.replace(/\\pi/g, '(PI)').replace(/\\times|\\cdot/g, '*').replace(/\\div/g, '/').replace(/\^\{([^{}]*)\}/g, '**($1)').replace(/\^/g, '**').replace(/[{}]/g, m => m === '{' ? '(' : ')');
  e = e.replace(/([\d)])\s*\(/g, '$1*(').replace(/PI/g, String(Math.PI)).trim();
  if (!e || !/^[-\d.\s+*/()]+$/.test(e) || !/\d/.test(e)) return null;
  try { const v = Function(`return (${e})`)(); return isFinite(v) ? v : null; } catch (_) { return null; }
}
const workStats = {};
function verifyWork(p) {
  const st = workStats[p.type] = workStats[p.type] || { problems: 0, eqs: 0, reached: 0 };
  st.problems++;
  const blocks = []; const re = /\\\((.+?)\\\)|\$\$(.+?)\$\$/gs; let m;
  for (const x of p.solution.join(' ').matchAll(re)) blocks.push(x[1] || x[2]);
  let reached = p.value == null;
  ok(!/10\^\{\+|\de\+\d/.test(p.solution.join(' ')), p, 'worked solution shows a number in scientific notation');
  // ln / e / ^{3/2} answers are not parsed: there the rounded "\approx 2.2493" has to match instead.
  for (const b of blocks) for (const [, x] of b.matchAll(/\\approx\s*(-?\d+(?:\.\d+)?)/g)) if (p.value != null && rel(Number(x), p.value, 1e-4)) reached = true;
  for (const b of blocks) for (const chain of b.split(/,\s*\\qquad|\\qquad|\\quad|\\Rightarrow|\\checkmark|:/)) {
    const vals = chain.split('=').map(numSide);
    vals.forEach((v, i) => {
      if (v != null && p.value != null && rel(v, p.value, 1e-9)) reached = true;
      if (i && v != null && vals[i - 1] != null) { st.eqs++; ok(rel(vals[i - 1], v, 1e-9), p, `worked-solution arithmetic wrong: ${chain.split('=')[i - 1].trim()} = ${chain.split('=')[i].trim()}`); }
    });
  }
  if (reached) st.reached++;
  ok(reached, p, `worked solution never states the answer ${p.answer} as a number`);
}

const t0 = Date.now();
const perType = {};
for (const T of Gen.TYPES) {
  const variants = new Set();
  for (let seed = 1; seed <= N; seed++) {
    let p;
    try { p = Gen.make(T.id, seed * 7919 + 13); } catch (e) { fails.push(`[${T.id} seed ${seed}] generator threw: ${e.stack.split('\n').slice(0, 2).join(' ')}`); continue; }
    variants.add(p.statement);
    try { verifyProblem(p); } catch (e) { fail(p, 'verifier threw: ' + e.stack.split('\n').slice(0, 2).join(' ')); }
  }
  perType[T.id] = variants.size;
}

// Every assigned homework problem, explicitly (not left to random seeds).
const hwKeys = [];
for (let i = 0; i < Gen.HW_COUNT; i++) {
  const p = Gen.hwProblem(i);
  hwKeys.push(`${p.hw}: ${p.answer ?? 'setup only'}${p.value != null ? ' ≈ ' + p.value.toFixed(4) : ''}`);
  try { verifyProblem(p); } catch (e) { fail(p, 'verifier threw: ' + e.stack.split('\n').slice(0, 2).join(' ')); }
}

// Checker self-tests: equivalent forms accepted, wrong ones rejected.
const st = (kind, ans, extra = {}) => ({ kind, ans, v: 'x', lo: 0, hi: 2, ...extra });
const selfTests = [
  [st('num', '8 pi / 27'), '8pi/27', true], [st('num', '8 pi / 27'), '0.9308', true], [st('num', '8 pi / 27'), '0.93', false],
  [st('num', '13/6'), '2.1667', true], [st('num', '13/6'), '26/12', true], [st('num', '13/6'), '2', false],
  [st('expr', '(x - 1)^2'), 'x^2 - 2x + 1', true], [st('expr', '(x - 1)^2'), 'x^2 - 2x', false],
  [st('expr', 'sqrt(x)'), 'x^(1/2)', true], [st('expr', 'x + 2'), 'y + 2', false],
  [st('anti', '', { integrand: '3 x^2' }), 'x^3 + 7', true], [st('anti', '', { integrand: '3 x^2' }), '3 x^3', false],
  [st('expr', 'pi * (x + 1)'), 'pi*(x+1)', true], [st('expr', '2 x'), '2x', true],
  [st('expr', 'ln(x) / 2', { lo: 1, hi: 3 }), 'log(x)/2', true],
  [st('expr', 'x - x^2'), 'x(1-x)', true], [st('expr', 'x - x^2'), '2x(1-x)', false], [st('expr', 'y^2', { v: 'y' }), 'y(y)', true],
];
for (const [s, input, want] of selfTests) { checks++; const g = Check.grade(s, input); if (g.ok !== want) fails.push(`checker self-test: ${input} vs ${s.ans || s.integrand} expected ${want} got ${g.ok} (${g.msg})`); }

// Method drill: every generated question has exactly one correct option and renders.
let drillCount = 0;
for (let seed = 1; seed <= N * 3; seed++) {
  const d = Drill.make(seed);
  drillCount++;
  checks++;
  const fake = { type: 'drill:' + d.cat, seed };
  if (d.options.filter(o => o === d.correct).length !== 1 || new Set(d.options).size !== d.options.length) fail(fake, `drill options bad: ${JSON.stringify(d.options)} correct ${d.correct}`);
  renders(fake, d.q + d.options.join(' ') + d.why, 'drill');
}

// Worked solutions must actually be worked: at least 3 checked arithmetic steps per problem on average.
for (const [id, s] of Object.entries(workStats)) { checks++; if (!['arc-setup', 'hw'].includes(id) && s.eqs < 3 * s.problems) fails.push(`worked solution for ${id}: only ${s.eqs} checked arithmetic steps in ${s.problems} problems`); }

const secs = ((Date.now() - t0) / 1000).toFixed(1);
console.log('Checked arithmetic steps per worked solution: ' + Object.entries(workStats).map(([k, s]) => `${k} ${(s.eqs / s.problems).toFixed(1)}`).join(', '));
console.log(`Problem types: ${Gen.TYPES.length}, problems per type: ${N}, drill questions: ${drillCount}`);
console.log('Distinct statements per type: ' + Object.entries(perType).map(([k, v]) => `${k} ${v}`).join(', '));
console.log('Homework answer keys: ' + hwKeys.join(' | '));
console.log(`Checks run: ${checks}, failures: ${fails.length}, time ${secs}s`);
if (fails.length) { console.log(fails.slice(0, 60).join('\n')); process.exit(1); }
console.log('ALL PASS');
