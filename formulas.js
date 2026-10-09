// Basic integration formulas (Briggs/Cochran Table 8.1): data, typed-answer checking, multiple-choice options.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory(require('./check.js'));
  else root.Formulas = factory(root.Check);
})(this, function (Check) {
  const PI = Math.PI;
  // x-intervals (as functions of a) where the formula holds with no pole inside. Two intervals where
  // the sign inside |...| flips, so ln x passes only if it is ln|x|.
  const ALL = () => [[-2, 2]];
  const COS_POS = a => [[-1.2 / a, 1.2 / a], [(PI / 2 + 0.25) / a, (3 * PI / 2 - 0.25) / a]];
  const SIN_POS = a => [[0.25 / a, (PI - 0.25) / a], [(PI + 0.25) / a, (2 * PI - 0.25) / a]];
  // lhs/rhs: TeX. f: integrand, ans: antiderivative (math.js, variables x, a, k, p).
  // wrong: plausible wrong right-hand sides [TeX, math.js].
  const F = [
    { lhs: '\\int k\\,dx', rhs: 'kx + C', cond: '\\(k\\) real', f: 'k', ans: 'k x', dom: () => [[-2, 3]],
      wrong: [['\\frac{kx^2}{2} + C', 'k x^2 / 2'], ['k + C', 'k'], ['\\frac{k^2}{2} + C', 'k^2 / 2'], ['x + C', 'x']] },
    { lhs: '\\int x^p\\,dx', rhs: '\\frac{x^{p+1}}{p+1} + C', cond: '\\(p \\ne -1\\) real', f: 'x^p', ans: 'x^(p+1)/(p+1)', dom: () => [[0.3, 3]],
      wrong: [['p\\,x^{p-1} + C', 'p x^(p-1)'], ['\\frac{x^{p+1}}{p} + C', 'x^(p+1)/p'], ['(p+1)\\,x^{p+1} + C', '(p+1) x^(p+1)'], ['\\frac{x^{p-1}}{p-1} + C', 'x^(p-1)/(p-1)']] },
    { lhs: '\\int \\cos ax\\,dx', rhs: '\\frac{1}{a}\\sin ax + C', f: 'cos(a x)', ans: '1/a * sin(a x)', dom: ALL,
      wrong: [['-\\frac{1}{a}\\sin ax + C', '-1/a * sin(a x)'], ['\\sin ax + C', 'sin(a x)'], ['a\\sin ax + C', 'a sin(a x)'], ['\\frac{1}{a}\\cos ax + C', '1/a * cos(a x)']] },
    { lhs: '\\int \\sin ax\\,dx', rhs: '-\\frac{1}{a}\\cos ax + C', f: 'sin(a x)', ans: '-1/a * cos(a x)', dom: ALL,
      wrong: [['\\frac{1}{a}\\cos ax + C', '1/a * cos(a x)'], ['-\\cos ax + C', '-cos(a x)'], ['-a\\cos ax + C', '-a cos(a x)'], ['\\frac{1}{a}\\sin ax + C', '1/a * sin(a x)']] },
    { lhs: '\\int \\sec^2 ax\\,dx', rhs: '\\frac{1}{a}\\tan ax + C', f: 'sec(a x)^2', ans: '1/a * tan(a x)', dom: COS_POS,
      wrong: [['-\\frac{1}{a}\\tan ax + C', '-1/a * tan(a x)'], ['\\tan ax + C', 'tan(a x)'], ['a\\tan ax + C', 'a tan(a x)'], ['\\frac{1}{a}\\sec ax + C', '1/a * sec(a x)']] },
    { lhs: '\\int \\csc^2 ax\\,dx', rhs: '-\\frac{1}{a}\\cot ax + C', f: 'csc(a x)^2', ans: '-1/a * cot(a x)', dom: SIN_POS,
      wrong: [['\\frac{1}{a}\\cot ax + C', '1/a * cot(a x)'], ['-\\cot ax + C', '-cot(a x)'], ['-a\\cot ax + C', '-a cot(a x)'], ['\\frac{1}{a}\\tan ax + C', '1/a * tan(a x)']] },
    { lhs: '\\int \\sec ax\\tan ax\\,dx', rhs: '\\frac{1}{a}\\sec ax + C', f: 'sec(a x) tan(a x)', ans: '1/a * sec(a x)', dom: COS_POS,
      wrong: [['-\\frac{1}{a}\\sec ax + C', '-1/a * sec(a x)'], ['\\sec ax + C', 'sec(a x)'], ['a\\sec ax + C', 'a sec(a x)'], ['\\frac{1}{a}\\tan ax + C', '1/a * tan(a x)']] },
    { lhs: '\\int \\csc ax\\cot ax\\,dx', rhs: '-\\frac{1}{a}\\csc ax + C', f: 'csc(a x) cot(a x)', ans: '-1/a * csc(a x)', dom: SIN_POS,
      wrong: [['\\frac{1}{a}\\csc ax + C', '1/a * csc(a x)'], ['-\\csc ax + C', '-csc(a x)'], ['-a\\csc ax + C', '-a csc(a x)'], ['-\\frac{1}{a}\\cot ax + C', '-1/a * cot(a x)']] },
    { lhs: '\\int e^{ax}\\,dx', rhs: '\\frac{1}{a}e^{ax} + C', f: 'e^(a x)', ans: '1/a * e^(a x)', dom: ALL,
      wrong: [['a\\,e^{ax} + C', 'a e^(a x)'], ['e^{ax} + C', 'e^(a x)'], ['\\frac{e^{ax+1}}{ax+1} + C', 'e^(a x + 1)/(a x + 1)'], ['-\\frac{1}{a}e^{ax} + C', '-1/a * e^(a x)']] },
    { lhs: '\\int \\frac{dx}{x}', rhs: '\\ln|x| + C', f: '1/x', ans: 'ln(abs(x))', dom: () => [[0.3, 4], [-4, -0.3]],
      wrong: [['-\\frac{1}{x^2} + C', '-1/x^2'], ['\\frac{1}{x^2} + C', '1/x^2'], ['e^{x} + C', 'e^x'], ['\\frac{1}{\\ln|x|} + C', '1/ln(abs(x))']] },
    { lhs: '\\int \\frac{dx}{a^2 + x^2}', rhs: '\\frac{1}{a}\\tan^{-1}\\frac{x}{a} + C', f: '1/(a^2 + x^2)', ans: '1/a * atan(x/a)', dom: () => [[-3, 3]],
      wrong: [['\\tan^{-1}\\frac{x}{a} + C', 'atan(x/a)'], ['a\\tan^{-1}\\frac{x}{a} + C', 'a atan(x/a)'], ['\\frac{1}{a}\\sin^{-1}\\frac{x}{a} + C', '1/a * asin(x/a)'], ['\\ln(a^2 + x^2) + C', 'ln(a^2 + x^2)']] },
    { lhs: '\\int \\frac{dx}{\\sqrt{a^2 - x^2}}', rhs: '\\sin^{-1}\\frac{x}{a} + C', cond: '\\(a > 0\\)', f: '1/sqrt(a^2 - x^2)', ans: 'asin(x/a)', dom: a => [[-0.9 * a, 0.9 * a]],
      wrong: [['\\frac{1}{a}\\sin^{-1}\\frac{x}{a} + C', '1/a * asin(x/a)'], ['\\tan^{-1}\\frac{x}{a} + C', 'atan(x/a)'], ['\\frac{1}{a}\\tan^{-1}\\frac{x}{a} + C', '1/a * atan(x/a)'], ['\\sin^{-1}(ax) + C', 'asin(a x)']] },
    { lhs: '\\int \\frac{dx}{x\\sqrt{x^2 - a^2}}', rhs: '\\frac{1}{a}\\sec^{-1}\\left|\\frac{x}{a}\\right| + C', cond: '\\(a > 0\\)', f: '1/(x sqrt(x^2 - a^2))', ans: '1/a * asec(abs(x/a))', dom: a => [[1.15 * a, 4 * a], [-4 * a, -1.15 * a]],
      wrong: [['\\sec^{-1}\\left|\\frac{x}{a}\\right| + C', 'asec(abs(x/a))'], ['a\\sec^{-1}\\left|\\frac{x}{a}\\right| + C', 'a asec(abs(x/a))'], ['\\frac{1}{a}\\sin^{-1}\\frac{x}{a} + C', '1/a * asin(x/a)'], ['\\frac{1}{a}\\tan^{-1}\\frac{x}{a} + C', '1/a * atan(x/a)']] },
    { lhs: '\\int \\tan ax\\,dx', rhs: '\\frac{1}{a}\\ln|\\sec ax| + C', f: 'tan(a x)', ans: '1/a * ln(abs(sec(a x)))', dom: COS_POS,
      wrong: [['\\frac{1}{a}\\ln|\\cos ax| + C', '1/a * ln(abs(cos(a x)))'], ['\\ln|\\sec ax| + C', 'ln(abs(sec(a x)))'], ['\\frac{1}{a}\\sec^2 ax + C', '1/a * sec(a x)^2'], ['a\\ln|\\sec ax| + C', 'a ln(abs(sec(a x)))']] },
    { lhs: '\\int \\cot ax\\,dx', rhs: '\\frac{1}{a}\\ln|\\sin ax| + C', f: 'cot(a x)', ans: '1/a * ln(abs(sin(a x)))', dom: SIN_POS,
      wrong: [['-\\frac{1}{a}\\ln|\\sin ax| + C', '-1/a * ln(abs(sin(a x)))'], ['\\frac{1}{a}\\ln|\\cos ax| + C', '1/a * ln(abs(cos(a x)))'], ['\\ln|\\sin ax| + C', 'ln(abs(sin(a x)))'], ['-\\frac{1}{a}\\csc^2 ax + C', '-1/a * csc(a x)^2']] },
    { lhs: '\\int \\sec ax\\,dx', rhs: '\\frac{1}{a}\\ln|\\sec ax + \\tan ax| + C', f: 'sec(a x)', ans: '1/a * ln(abs(sec(a x) + tan(a x)))', dom: COS_POS,
      wrong: [['-\\frac{1}{a}\\ln|\\sec ax + \\tan ax| + C', '-1/a * ln(abs(sec(a x) + tan(a x)))'], ['\\ln|\\sec ax + \\tan ax| + C', 'ln(abs(sec(a x) + tan(a x)))'], ['\\frac{1}{a}\\sec ax\\tan ax + C', '1/a * sec(a x) tan(a x)'], ['\\frac{1}{a}\\ln|\\csc ax + \\cot ax| + C', '1/a * ln(abs(csc(a x) + cot(a x)))']] },
    { lhs: '\\int \\csc ax\\,dx', rhs: '-\\frac{1}{a}\\ln|\\csc ax + \\cot ax| + C', f: 'csc(a x)', ans: '-1/a * ln(abs(csc(a x) + cot(a x)))', dom: SIN_POS,
      wrong: [['\\frac{1}{a}\\ln|\\csc ax + \\cot ax| + C', '1/a * ln(abs(csc(a x) + cot(a x)))'], ['-\\ln|\\csc ax + \\cot ax| + C', '-ln(abs(csc(a x) + cot(a x)))'], ['-\\frac{1}{a}\\csc ax\\cot ax + C', '-1/a * csc(a x) cot(a x)'], ['-\\frac{1}{a}\\ln|\\sec ax + \\tan ax| + C', '-1/a * ln(abs(sec(a x) + tan(a x)))']] },
  ];
  const PARAMS = [{ a: 1.7, k: 2.3, p: 2.5 }, { a: 0.6, k: -1.4, p: -0.5 }];
  const VARS = new Set(['x', 'a', 'k', 'p']);

  // Book notation -> math.js: |u| -> abs(u), sin^-1 -> asin, "sin ax" -> sin(a x), "ax" -> a x, "1/a" -> (1/a), drop "+ C".
  function pre(s) {
    s = String(s).replace(/\+\s*C\s*$/, '').replace(/π/g, 'pi');
    for (let i = 0; i < 3; i++) s = s.replace(/\|([^|]+)\|/g, '(abs($1))');
    s = s.replace(/\b(sin|cos|tan|sec|csc|cot)\s*\^\s*\(?\s*-\s*1\s*\)?/g, 'a$1');
    s = s.replace(/\b(a?(?:sin|cos|tan|sec|csc|cot)(?:\s*\^\s*2)?|ln)\s+([a-z0-9/.]+)/g, (m, fn, arg) => { const sq = /\^\s*2$/.test(fn); fn = fn.replace(/\s*\^\s*2$/, ''); return sq ? `${fn}(${arg})^2` : `${fn}(${arg})`; });
    s = s.replace(/\b([ak])x\b/g, '$1 x');
    s = s.replace(/(^|[^\w.)])1\s*\/\s*([a-z])\b(?!\s*\^)/g, '$1(1/$2)');
    return s;
  }

  // Typed answer: G(x) - G(x0) must equal F(x) - F(x0) for both parameter sets on every interval (any + C).
  function grade(k, input) {
    const f = F[k];
    let node;
    try { node = Check.parse(pre(input)); } catch (e) { return { ok: false, msg: e.message }; }
    const bad = Check.freeVars(node).filter(n => !VARS.has(n));
    if (bad.length) return { ok: false, msg: `Unknown name(s): ${bad.join(', ')}. Use x, a, k, p and write a*x or a x, not ax with other letters.` };
    const G = Check.compile(node).fn, A = Check.compile(f.ans).fn;
    const ratios = [];
    let ok = true;
    for (const P of PARAMS) for (const [lo, hi] of f.dom(P.a)) {
      const pts = Check.samples(lo, hi, 6), x0 = pts[0], rs = [];
      for (const x of pts.slice(1)) {
        const got = G({ ...P, x }) - G({ ...P, x: x0 }), want = A({ ...P, x }) - A({ ...P, x: x0 });
        if (!isFinite(got)) return { ok: false, msg: 'Not defined everywhere it should be. ' + (f.rhs.includes('|') ? 'Did you leave out the absolute value bars?' : 'Check your answer.') };
        if (!Check.close(got, want, 1e-6)) ok = false;
        if (Math.abs(want) > 1e-9) rs.push(got / want);
      }
      ratios.push({ a: P.a, rs });
    }
    if (ok) return { ok: true };
    const all = (t) => ratios.every(({ a, rs }) => rs.length && rs.every(r => Check.close(r, t(a), 1e-5)));
    if (all(() => -1)) return { ok: false, msg: 'Sign error: your answer is the negative of the right one.' };
    if (all(a => a)) return { ok: false, msg: 'Missing the \\(\\frac{1}{a}\\) (your answer is \\(a\\) times too big).' };
    if (all(a => a * a)) return { ok: false, msg: 'You multiplied by \\(a\\) instead of dividing by it.' };
    if (all(a => -a)) return { ok: false, msg: 'Sign error, and missing the \\(\\frac{1}{a}\\).' };
    if (f.rhs.includes('|') && ratios.some(({ rs }) => rs.length && rs.every(r => Check.close(r, 1, 1e-5)))) return { ok: false, msg: 'Right on one side only: you need the absolute value bars.' };
    return { ok: false, msg: 'Not right. Differentiate your answer: you must get back the integrand.' };
  }

  // Multiple choice: the right side plus 3 of its plausible wrong versions, shuffled.
  function options(k, rand = Math.random) {
    const w = F[k].wrong.map(x => x[0]);
    for (let i = w.length - 1; i > 0; i--) { const j = Math.floor(rand() * (i + 1)); [w[i], w[j]] = [w[j], w[i]]; }
    const o = [F[k].rhs, ...w.slice(0, 3)];
    for (let i = o.length - 1; i > 0; i--) { const j = Math.floor(rand() * (i + 1)); [o[i], o[j]] = [o[j], o[i]]; }
    return o;
  }

  return { F, grade, options, pre, PARAMS };
});
