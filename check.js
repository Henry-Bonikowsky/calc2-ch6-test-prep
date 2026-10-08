// Answer checking shared by the site and the verification test.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory(require('./vendor/math.js'));
  else root.Check = factory(root.math);
})(this, function (math) {
  math.import({ ln: math.log }, { override: false });
  const KNOWN = new Set(['pi', 'e']);

  function parse(s) {
    s = String(s).trim().replace(/\*\*/g, '^').replace(/π/g, 'pi').replace(/√/g, 'sqrt');
    if (!s) throw new Error('Empty answer.');
    let node;
    try { node = math.parse(s); } catch (e) { throw new Error("Can't read that: " + e.message); }
    // x(1 - x) means x·(1 - x), not a function named x.
    return node.transform(n => n.isFunctionNode && n.fn.isSymbolNode && n.args.length === 1 && typeof math[n.fn.name] !== 'function'
      ? new math.OperatorNode('*', 'multiply', [new math.SymbolNode(n.fn.name), new math.ParenthesisNode(n.args[0])]) : n);
  }

  // Free variables used (excluding function names and pi/e).
  function freeVars(node) {
    const out = new Set();
    node.traverse((n, path) => { if (n.isSymbolNode && path !== 'fn' && !KNOWN.has(n.name)) out.add(n.name); });
    return [...out];
  }

  function real(v) {
    if (typeof v === 'number') return v;
    if (v && typeof v.re === 'number') return Math.abs(v.im) < 1e-9 * (1 + Math.abs(v.re)) ? v.re : NaN;
    if (v && typeof v.toNumber === 'function') return v.toNumber();
    return NaN;
  }

  function compile(s) {
    const node = typeof s === 'string' || typeof s === 'number' ? parse(s) : s;
    const code = node.compile();
    return { node, fn: scope => { try { return real(code.evaluate(scope)); } catch (e) { return NaN; } } };
  }

  function evalNum(s, scope = {}) { return compile(s).fn(scope); }

  // Sample points strictly inside [lo,hi].
  function samples(lo, hi, n = 9) {
    const pts = [];
    for (let i = 0; i < n; i++) pts.push(lo + (hi - lo) * (0.07 + 0.86 * ((i * 0.6180339887) % 1)));
    return pts;
  }

  function close(a, b, rel = 1e-7) {
    if (!isFinite(a) || !isFinite(b)) return false;
    return Math.abs(a - b) <= rel * Math.max(1, Math.abs(a), Math.abs(b));
  }

  // Numeric answer. Exact forms must match tightly; decimals need 4 significant digits.
  function numEq(input, expected) {
    const a = evalNum(input), b = evalNum(expected);
    if (!isFinite(a)) return false;
    if (close(a, b, 1e-9)) return true;
    const typedDecimal = /\d\.\d/.test(String(input));
    return typedDecimal && Math.abs(a - b) <= 5e-4 * Math.max(Math.abs(b), 1e-3);
  }

  function exprEq(input, expected, v, lo, hi) {
    const A = compile(input).fn, B = compile(expected).fn;
    let good = 0;
    for (const x of samples(lo, hi)) {
      const b = B({ [v]: x });
      if (!isFinite(b)) continue;
      if (!close(A({ [v]: x }), b, 1e-7)) return false;
      good++;
    }
    return good >= 4;
  }

  function simpson(f, a, b, n = 400) {
    if (a === b) return 0;
    const h = (b - a) / n;
    let s = f(a) + f(b);
    for (let i = 1; i < n; i++) s += f(a + i * h) * (i % 2 ? 4 : 2);
    return (s * h) / 3;
  }

  // Antiderivative: F(p) - F(p0) must equal the integral of f from p0 to p (any +C passes).
  // Returns {ok, factor}; factor is set when F is off by a constant multiple.
  function antiCheck(input, integrand, v, lo, hi) {
    const F = compile(input).fn, f = compile(integrand).fn;
    const pts = samples(lo, hi, 6), p0 = pts[0];
    const ratios = [];
    let ok = true;
    for (const p of pts.slice(1)) {
      const want = simpson(x => f({ [v]: x }), p0, p);
      const got = F({ [v]: p }) - F({ [v]: p0 });
      if (!isFinite(got)) return { ok: false };
      if (!close(got, want, 1e-6)) ok = false;
      if (Math.abs(want) > 1e-9) ratios.push(got / want);
    }
    if (ok) return { ok: true };
    const r = ratios[0];
    if (ratios.length >= 3 && isFinite(r) && Math.abs(r) > 1e-9 && ratios.every(x => close(x, r, 1e-5))) return { ok: false, factor: r };
    return { ok: false };
  }

  // Did they differentiate the integrand instead of integrating it?
  function isDerivativeOf(input, integrand, v, lo, hi) {
    const A = compile(input).fn, f = compile(integrand).fn;
    let good = 0;
    for (const x of samples(lo, hi, 6)) {
      const h = 1e-5 * Math.max(1, Math.abs(x));
      const d = (f({ [v]: x + h }) - f({ [v]: x - h })) / (2 * h);
      if (!isFinite(d)) continue;
      if (!close(A({ [v]: x }), d, 1e-4)) return false;
      good++;
    }
    return good >= 4;
  }

  function fmtFactor(r) {
    for (let d = 1; d <= 100; d++) { const n = Math.round(r * d); if (Math.abs(n / d - r) < 1e-9) return d === 1 ? `${n}` : `${n}/${d}`; }
    return r.toPrecision(4);
  }

  // Grade one step. Returns {ok, msg}. msg names the mistake when it can.
  function grade(step, input) {
    let node;
    try { node = parse(input); } catch (e) { return { ok: false, msg: e.message }; }
    const v = step.v;
    if (step.kind !== 'num') {
      const bad = freeVars(node).filter(n => n !== v);
      if (bad.length) {
        if (bad.length === 1 && bad[0].length === 1 && /[a-z]/.test(bad[0]))
          return { ok: false, msg: `Your answer uses ${bad[0]}, but this step is in terms of ${v}. ${v === 'y' ? 'Integrating dy means every curve must be solved for x = (something in y) first.' : 'Rewrite it using ' + v + '.'}` };
        return { ok: false, msg: `Unknown name(s): ${bad.join(', ')}. Use ${v}, pi, e, sqrt(), ln(), and * for multiplication (write pi*(x+1), not pi(x+1)).` };
      }
    } else if (freeVars(node).length) {
      return { ok: false, msg: `This answer is a number; it can't contain ${freeVars(node).join(', ')}.` };
    }
    const eq = (a, b) => step.kind === 'num' ? numEq(a, b) : exprEq(a, b, v, step.lo, step.hi);
    if (step.kind === 'anti') {
      const r = antiCheck(node, step.integrand, v, step.lo, step.hi);
      if (r.ok) return { ok: true };
      for (const m of step.mistakes || []) if (exprEq(node, m.ans, v, step.lo, step.hi)) return { ok: false, msg: m.msg };
      if (isDerivativeOf(node, step.integrand, v, step.lo, step.hi)) return { ok: false, msg: 'You differentiated. Integrate instead: raise each power by 1 and divide by the new power.' };
      if (r.factor) return { ok: false, msg: `Close: the derivative of your answer is ${fmtFactor(r.factor)} times the integrand. Check each 1/(n+1) and any u-substitution factor (dx = du/k).` };
      return { ok: false, msg: step.hint || 'Differentiate your answer: you must get back exactly the integrand.' };
    }
    let ok = false;
    try { ok = eq(node, step.ans); } catch (e) { ok = false; }
    if (ok) return { ok: true };
    for (const m of step.mistakes || []) { try { if (eq(node, m.ans)) return { ok: false, msg: m.msg }; } catch (e) {} }
    if (step.kind === 'num') {
      const a = evalNum(node), b = evalNum(step.ans);
      if (isFinite(a) && close(a, -b, 1e-6) && b !== 0) return { ok: false, msg: 'Right size, wrong sign. ' + (step.signHint || 'Check the order of subtraction (upper minus lower, top minus bottom).') };
      if (isFinite(a) && !/\d\.\d/.test(String(input)) && Math.abs(a - b) <= 5e-3 * Math.abs(b)) return { ok: false, msg: 'Very close. Check your arithmetic, or give the exact form.' };
    } else {
      try { if (exprEq(node, `-(${step.ans})`, v, step.lo, step.hi)) return { ok: false, msg: 'This is the negative of the answer. ' + (step.signHint || 'Distance/length = (bigger) minus (smaller).') }; } catch (e) {}
    }
    return { ok: false, msg: step.hint || 'Not right yet.' };
  }

  function tex(expr) {
    return math.parse(String(expr)).toTex({ parenthesis: 'auto', implicit: 'hide' })
      .replace(/~/g, '').replace(/\\mathrm\{pi\}/g, '\\pi').replace(/\\mathrm\{ln\}/g, '\\ln').replace(/\\mathrm\{([a-z])\}/g, '$1').replace(/\{ ([a-z])\}/g, '{$1}').replace(/(^|[^\\a-zA-Z]) ([a-z])/g, '$1$2');
  }

  return { parse, freeVars, evalNum, numEq, exprEq, antiCheck, grade, tex, simpson, samples, close, compile };
});
