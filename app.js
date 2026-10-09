(() => {
  // ---------- storage / tracking ----------
  const KEY = 'ma172ch6.v1';
  let store;
  try { store = JSON.parse(localStorage.getItem(KEY)) || {}; } catch (e) { store = {}; }
  store.types = store.types || {}; store.drill = store.drill || {};
  const save = () => localStorage.setItem(KEY, JSON.stringify(store));
  const ts = id => (store.types[id] = store.types[id] || { att: 0, clean: 0, streak: 0, miss: {} });
  // Table 8.1 formulas: per-formula stats; the pseudo-type 'tbl' stands for all of them in Smart and Mastery.
  store.formulas = store.formulas || {};
  const FN = Formulas.F.length;
  const fs = k => (store.formulas[k] = store.formulas[k] || { att: 0, right: 0, streak: 0 });
  const fMastered = k => (store.formulas[k] || {}).streak >= 3;
  const fCount = () => Formulas.F.filter((f, k) => fMastered(k)).length;
  function recordF(k, right) { const s = fs(k); s.att++; if (right) { s.right++; s.streak++; } else s.streak = 0; save(); }
  const mastered = id => id === 'tbl' ? fCount() === FN : (store.types[id] || {}).streak >= 3;
  const ON_TEST = Gen.TYPES.filter(t => !t.off);
  const SMART_IDS = [...ON_TEST.map(t => t.id), 'tbl'];
  // Weak formulas first, then untried, then mastered.
  function pickFormula(avoid) {
    const ks = Formulas.F.map((f, k) => k).filter(k => k !== avoid);
    return weightedPick(ks, ks.map(k => { const s = store.formulas[k]; return !s ? 2 : s.streak >= 3 ? 0.5 : 3 + (s.att - s.right); }));
  }
  function record(id, clean, missed) {
    const s = ts(id); s.att++;
    if (clean) { s.clean++; s.streak++; } else s.streak = 0;
    for (const m of missed) s.miss[m] = (s.miss[m] || 0) + 1;
    save();
  }
  const STEP_NAMES = { a: 'lower bound', b: 'upper bound', R: 'outer radius R', r: 'inner radius r', radius: 'shell radius', height: 'shell height', integrand: 'integrand', anti: 'antiderivative', final: 'final answer', s: 'position s(t)', v: 'velocity v(t)', z0: 'zero of v', z1: 'second zero of v', z: 'zero of v', disp: 'displacement', c: 'crossing point', A1: 'left piece area', A2: 'right piece area', d: 'derivative', one: "1 + (f')²", k: 'spring constant k', delta: 'weight per length', top: 'top-half work', bot: 'bottom-half work', chainW: 'chain work', loadW: 'load work', A: 'slice area A(y)', lift: 'lift distance', depth: 'depth', w: 'strip width', side: 'slice length s', len: 'slice length', rad: 'slice radius r', half: 'half-width x', wid: 'slice width w' };
  const stepName = id => id.startsWith('w-') ? 'washer ' + STEP_NAMES[id.slice(2)] : id.startsWith('s-') ? 'shell ' + STEP_NAMES[id.slice(2)] : STEP_NAMES[id] || id;

  function weightedPick(items, w) {
    const tot = w.reduce((a, b) => a + b, 0); let x = Math.random() * tot;
    for (let i = 0; i < items.length; i++) { x -= w[i]; if (x <= 0) return items[i]; }
    return items[items.length - 1];
  }
  // Weak spots first: missed-and-not-mastered > never tried > mastered (review only once everything is mastered).
  function smartType(ids, avoid) {
    ids = ids || SMART_IDS;
    let pool = ids.filter(id => !mastered(id));
    if (!pool.length) pool = ids.slice();
    if (pool.length > 1) pool = pool.filter(id => id !== avoid);
    const w = pool.map(id => {
      if (id === 'tbl') { const ss = Object.values(store.formulas); if (!ss.length) return 1.5; if (mastered(id)) return 1; return 4 + Math.min(ss.reduce((a, s) => a + s.att - s.right, 0), 8); }
      const s = store.types[id]; if (!s || !s.att) return 1.5; if (mastered(id)) return 1; const misses = Object.values(s.miss).reduce((a, b) => a + b, 0); return 4 + Math.min(misses, 8);
    });
    return weightedPick(pool, w);
  }
  const newSeed = () => Math.floor(Math.random() * 2 ** 31);

  // ---------- rendering helpers ----------
  const $ = (sel, el = document) => el.querySelector(sel);
  const h = (tag, attrs = {}, ...kids) => {
    const el = document.createElement(tag);
    for (const [k, v] of Object.entries(attrs)) { if (k === 'html') el.innerHTML = v; else if (k.startsWith('on')) el.addEventListener(k.slice(2), v); else if (v !== false && v != null) el.setAttribute(k, v); }
    for (const k of kids.flat()) if (k != null) el.append(k.nodeType ? k : document.createTextNode(k));
    return el;
  };
  const math = el => {
    // Phones: formulas joined by \qquad go on separate lines.
    if (matchMedia('(max-width: 600px)').matches) for (let w = document.createTreeWalker(el, NodeFilter.SHOW_TEXT), n; (n = w.nextNode());) n.data = n.data.replace(/,?\\qquad\s*/g, () => '$$$$');
    renderMathInElement(el, { delimiters: [{ left: '$$', right: '$$', display: true }, { left: '\\[', right: '\\]', display: true }, { left: '\\(', right: '\\)', display: false }], throwOnError: false }); return el; };
  // Phones: a formula chunk KaTeX can't wrap (one integral, one fraction) is shrunk to fit its box.
  function fitMath() {
    const ks = [...document.querySelectorAll('.katex')];
    ks.forEach(k => { if (k.style.fontSize) k.style.fontSize = ''; });
    const fits = ks.map(k => {
      let box = k.parentElement; while (getComputedStyle(box).display.startsWith('inline')) box = box.parentElement;
      const cs = getComputedStyle(box), avail = box.clientWidth - parseFloat(cs.paddingLeft) - parseFloat(cs.paddingRight);
      const w = Math.max(0, ...[...k.querySelectorAll('.katex-html > .katex-base')].map(b => b.getBoundingClientRect().width));
      return avail > 0 && w > avail ? Math.floor(parseFloat(getComputedStyle(k).fontSize) * avail / w * 0.97 * 10) / 10 + 'px' : '';
    });
    ks.forEach((k, i) => { if (fits[i]) k.style.fontSize = fits[i]; });
  }
  let fitQueued = false;
  const queueFit = () => { if (!fitQueued) { fitQueued = true; requestAnimationFrame(() => { fitQueued = false; fitMath(); }); } };
  new MutationObserver(queueFit).observe(document.body, { childList: true, subtree: true, attributes: true, attributeFilter: ['hidden', 'class'] });
  addEventListener('resize', queueFit);
  const texHTML = (expr, display) => { try { return katex.renderToString(Check.tex(expr), { throwOnError: false, displayMode: !!display }); } catch (e) { return String(expr); } };
  const dots = id => { if (id === 'tbl') return mastered(id) ? h('span', { class: 'mastered' }, `✓ ${FN}/${FN}`) : h('span', { class: 'dots' }, `${fCount()}/${FN}`); const s = store.types[id] || { streak: 0 }; const n = Math.min(3, s.streak || 0); return mastered(id) ? h('span', { class: 'mastered' }, '✓ 3/3') : h('span', { class: 'dots', html: '<span class="on">' + '●'.repeat(n) + '</span>' + '○'.repeat(3 - n) }); };
  const INPUT_HELP = 'Type math like 3x^2 - 2x, sqrt(x), x^(3/2), pi, e^x, ln(x), 8pi/27. Use * before a parenthesis after pi: pi*(x+1). The preview shows how your input was read.';

  function preview(input, box) {
    const v = input.value.trim();
    if (!v) { box.innerHTML = ''; return; }
    try { Check.parse(v); box.innerHTML = '= ' + texHTML(v.replace(/π/g, 'pi')); } catch (e) { box.textContent = '(can\'t read yet)'; }
  }

  // ---------- views ----------
  const views = ['cards', 'tbl', 'drill', 'practice', 'test', 'dash'];
  function show(view) {
    tblKeys = null;
    for (const v of views) { $('#view-' + v).classList.toggle('active', v === view); }
    document.querySelectorAll('nav button').forEach(b => b.classList.toggle('active', b.dataset.view === view));
    location.hash = view;
    ({ cards: renderCards, tbl: renderTbl, drill: renderDrill, practice: renderPractice, test: renderTest, dash: renderDash })[view]();
  }
  document.querySelectorAll('nav button').forEach(b => b.addEventListener('click', () => show(b.dataset.view)));

  // ---------- cards ----------
  function cardEl(c, withPractice) {
    return h('div', { class: 'panel card' },
      h('h2', {}, h('span', { class: 'tag' }, c.sec), c.title),
      h('div', { class: 'formula', html: c.formula }),
      h('p', { class: 'when', html: '<b>Use when:</b> ' + c.when }),
      h('ol', {}, c.steps.map(([s, m]) => h('li', { html: s + `<span class="mist">${m}</span>` }))),
      h('p', { class: 'chk', html: '<b>Sanity check:</b> ' + c.check }),
      withPractice ? h('button', { class: 'btn primary', onclick: () => { practice.sel = c.types; practice.p = null; show('practice'); } }, 'Practice this') : null);
  }
  function renderCards() {
    const v = $('#view-cards'); v.innerHTML = '';
    v.append(h('p', { class: 'help' }, 'Each card: the formula, the procedure in order, and (in red) the mistake to avoid at that step. 6.6 surface area is not on the test.'));
    const off = c => c.types.every(id => Gen.byId[id] && Gen.byId[id].off);
    v.append(math(h('div', { class: 'cards-grid' }, CARDS.filter(c => !off(c)).map(c => cardEl(c, true)))));
    v.append(math(h('details', { class: 'not-on-test' }, h('summary', {}, 'Not on the test'), h('div', { class: 'cards-grid' }, CARDS.filter(off).map(c => cardEl(c, true))))));
  }

  // ---------- Table 8.1 formulas ----------
  const tbl = { mode: 'mc', k: null };
  let tblKeys = null; // keyboard shortcuts of the formula question on screen
  document.addEventListener('keydown', e => { if (tblKeys && !/INPUT|SELECT|TEXTAREA/.test(e.target.tagName) && !e.ctrlKey && !e.metaKey && !e.altKey) tblKeys(e); });
  const fTex = (k, rhs) => { const f = Formulas.F[k]; return `\\[${f.lhs} = ${rhs === undefined ? f.rhs : rhs}\\]` + (f.cond ? `<div class="help">${f.cond}</div>` : ''); };
  // One formula question in the current mode. onAnswer(right) after it is graded; onNext for the next one.
  function formulaQ(k, onAnswer, onNext) {
    const f = Formulas.F[k], box = h('div', { class: 'fq' }), mode = tbl.mode === 'list' ? 'mc' : tbl.mode;
    const fb = h('div', { class: 'fb' }), full = h('div', { class: 'formula', hidden: true, html: fTex(k) });
    const next = h('button', { class: 'btn primary', hidden: true, onclick: onNext }, 'Next (Enter)');
    let graded = false;
    function grade(right, msg) {
      if (graded) return; graded = true;
      recordF(k, right); onAnswer && onAnswer(right);
      fb.className = 'fb ' + (right ? 'good' : 'bad'); fb.innerHTML = right ? `✓ Correct. Streak ${Math.min(fs(k).streak, 3)}/3` : '✗ ' + (msg || 'Not quite.') + ' The formula:'; math(fb);
      full.hidden = false; next.hidden = false;
      tblKeys = e => { if (e.key === 'Enter') { e.preventDefault(); onNext(); } };
      if (!matchMedia('(pointer: coarse)').matches) next.focus();
    }
    box.append(h('div', { class: 'formula q', html: fTex(k, '\\;?') }));
    if (mode === 'mc') {
      const opts = Formulas.options(k);
      const os = h('div', { class: 'opts' }, opts.map((o, i) => h('button', { class: 'opt', html: `<b>${i + 1}</b>&nbsp; \\(${o}\\)`, onclick: e => pickOpt(i) })));
      function pickOpt(i) {
        if (graded) return;
        os.querySelectorAll('.opt').forEach((b, j) => { b.disabled = true; if (opts[j] === f.rhs) b.classList.add('right'); else if (j === i) b.classList.add('wrong'); });
        grade(opts[i] === f.rhs);
      }
      box.append(os);
      tblKeys = e => { const i = +e.key - 1; if (i >= 0 && i < opts.length) pickOpt(i); };
    } else if (mode === 'type') {
      const input = h('input', { type: 'text', autocomplete: 'off', spellcheck: 'false', 'aria-label': 'right side', placeholder: 'e.g. 1/a sin(ax)' });
      const pv = h('div', { class: 'preview' });
      const check = () => {
        if (graded || !input.value.trim()) return;
        let readable = true; try { Check.parse(Formulas.pre(input.value)); } catch (e) { readable = false; }
        if (!readable) { fb.className = 'fb bad'; fb.textContent = "Can't read that yet."; return; }
        const g = Formulas.grade(k, input.value); input.disabled = true; grade(g.ok, g.msg);
      };
      input.addEventListener('input', () => { const v = input.value.trim(); if (!v) { pv.innerHTML = ''; return; } try { Check.parse(Formulas.pre(v)); pv.innerHTML = '= ' + texHTML(Formulas.pre(v)) + ' + C'; } catch (e) { pv.textContent = '(can\'t read yet)'; } });
      input.addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); if (graded) onNext(); else check(); } });
      box.append(h('div', { class: 'step' }, h('div', { class: 'row' }, input, h('button', { class: 'btn primary', onclick: check }, 'Check'), h('button', { class: 'btn', onclick: () => { input.disabled = true; grade(false, 'Shown.'); } }, 'Show')), pv),
        h('p', { class: 'help' }, 'Book notation works: 1/a sin ax, -1/a cos(ax), ln|sec ax|, tan^-1(x/a), sec^-1|x/a|, e^(ax)/a. The + C is optional. The preview shows how it was read.'));
      tblKeys = null;
      setTimeout(() => { if (!matchMedia('(pointer: coarse)').matches) input.focus({ preventScroll: true }); });
    } else {
      const back = h('div', { class: 'formula flip', hidden: true, html: `\\[= ${f.rhs}\\]` });
      const flip = h('button', { class: 'btn primary', onclick: () => doFlip() }, 'Flip (Space)');
      const self = h('div', { class: 'row', hidden: true }, h('button', { class: 'btn', onclick: () => selfGrade(true) }, 'Knew it (1)'), ' ', h('button', { class: 'btn', onclick: () => selfGrade(false) }, 'Missed it (2)'));
      function doFlip() { if (!back.hidden) return; back.hidden = false; flip.hidden = true; self.hidden = false; tblKeys = e => { if (e.key === '1') selfGrade(true); if (e.key === '2') selfGrade(false); }; }
      function selfGrade(right) { if (graded) return; self.hidden = true; back.hidden = true; grade(right, 'Keep drilling this one.'); }
      box.append(back, h('p', {}, flip), self);
      tblKeys = e => { if (e.key === ' ') { e.preventDefault(); doFlip(); } };
    }
    box.append(fb, full, h('p', {}, next));
    return math(box);
  }
  function formulaTable() {
    return math(h('table', {}, h('tr', {}, h('th', {}, '#'), h('th', {}, 'Formula'), h('th', {}, 'Streak'), h('th', {}, 'Right / tried')),
      Formulas.F.map((f, k) => { const s = store.formulas[k] || { att: 0, right: 0, streak: 0 }; return h('tr', {}, h('td', {}, String(k + 1)), h('td', { html: `\\(${f.lhs} = ${f.rhs}\\)` }), h('td', {}, fMastered(k) ? h('span', { class: 'mastered' }, '✓ 3/3') : h('span', { class: 'dots', html: '<span class="on">' + '●'.repeat(s.streak) + '</span>' + '○'.repeat(3 - s.streak) })), h('td', {}, `${s.right} / ${s.att}`)); })));
  }
  function renderTbl() {
    const v = $('#view-tbl'); v.innerHTML = '';
    const modes = { mc: 'Multiple choice', type: 'Type it', flip: 'Flip cards', list: 'Formula cards' };
    v.append(h('div', { class: 'panel' }, h('h2', {}, 'Basic integration formulas (Table 8.1)'),
      h('p', { class: 'help' }, `Memorize all ${FN}. A formula is mastered after 3 right in a row; misses come back first. Mastered: ${fCount()} / ${FN}.`),
      h('div', { class: 'row modes' }, Object.entries(modes).map(([m, n]) => h('button', { class: 'btn' + (tbl.mode === m ? ' primary' : ''), onclick: () => { tbl.mode = m; tbl.k = null; renderTbl(); } }, n)))));
    if (tbl.mode === 'list') {
      v.append(math(h('div', { class: 'cards-grid' }, Formulas.F.map((f, k) => h('div', { class: 'panel card' }, h('h2', {}, h('span', { class: 'tag' }, String(k + 1)), fMastered(k) ? h('span', { class: 'mastered' }, '✓') : ''), h('div', { class: 'formula', html: fTex(k) }))))));
    } else {
      if (tbl.k == null) tbl.k = pickFormula();
      const k = tbl.k;
      v.append(h('div', { class: 'panel' }, formulaQ(k, null, () => { tbl.k = pickFormula(k); renderTbl(); })));
    }
    v.append(h('div', { class: 'panel' }, h('h3', {}, 'Your formulas'), formulaTable()));
  }

  // ---------- step widget ----------
  function stepEl(step, i, opts) {
    const input = h('input', { type: 'text', autocomplete: 'off', spellcheck: 'false', 'aria-label': 'answer' });
    const pv = h('div', { class: 'preview' });
    const fb = h('div', { class: 'fb' });
    input.addEventListener('input', () => { preview(input, pv); opts.onInput && opts.onInput(input.value); });
    const el = h('div', { class: 'step' }, h('div', { class: 'label', html: `${i + 1}. ${step.label}` }), h('div', { class: 'row' }, input, ...(opts.buttons ? opts.buttons(input, fb) : [])), pv, fb);
    el._input = input; el._fb = fb; el._pv = pv;
    if (opts.value) { input.value = opts.value; preview(input, pv); }
    input.addEventListener('keydown', e => { if (e.key === 'Enter') { e.preventDefault(); opts.onEnter && opts.onEnter(); } });
    return math(el);
  }

  // ---------- practice ----------
  const practice = { sel: null, p: null };
  function renderTypeList() {
    const a = $('#type-list'); a.innerHTML = '';
    const panel = h('div', { class: 'panel' });
    panel.append(h('button', { class: 'type-btn' + (!practice.sel ? ' sel' : ''), onclick: () => { practice.sel = null; practice.p = null; renderPractice(); } }, h('b', {}, 'Smart: weak spots first'), ''));
    const btn = (id, name) => h('button', { class: 'type-btn' + (practice.sel && practice.sel.length === 1 && practice.sel[0] === id ? ' sel' : ''), onclick: () => { practice.sel = [id]; practice.p = null; renderPractice(); } }, h('span', {}, name), dots(id));
    panel.append(h('h3', {}, 'Table 8.1 (memorize)'), btn('tbl', 'Basic integration formulas'));
    let sec = '';
    for (const t of ON_TEST) {
      if (t.sec !== sec) { sec = t.sec; panel.append(h('h3', {}, t.head || sec)); }
      panel.append(btn(t.id, t.name));
    }
    const offT = Gen.TYPES.filter(t => t.off);
    panel.append(h('details', { class: 'not-on-test', open: offT.some(t => practice.sel && practice.sel.includes(t.id)) ? '' : false }, h('summary', {}, 'Not on the test'), offT.map(t => btn(t.id, t.name))));
    a.append(panel);
  }
  function nextProblem() {
    const id = practice.sel && practice.sel.length === 1 ? practice.sel[0] : smartType(practice.sel, practice.p && practice.p.type);
    practice.p = id === 'tbl' ? { type: 'tbl', k: pickFormula(practice.p && practice.p.k) } : Gen.make(id, newSeed());
    practice.idx = 0; practice.missed = new Set(); practice.recorded = false;
  }
  function renderPractice() {
    renderTypeList();
    if (!practice.p) nextProblem();
    const p = practice.p, m = $('#practice-main'); m.innerHTML = '';
    if (p.type === 'tbl') {
      const sub = practice.sel ? '' : 'smart pick';
      m.append(h('div', { class: 'panel' }, h('div', {}, h('span', { class: 'tag' }, 'Table 8.1'), h('b', {}, 'Basic integration formulas'), ' ', dots('tbl'), sub ? h('span', { class: 'help' }, '  · ' + sub) : null),
        formulaQ(p.k, renderTypeList, () => { nextProblem(); renderPractice(); })));
      return;
    }
    const card = CARDS.find(c => c.id === p.card);
    const cardBox = h('div', { class: 'inline-card', hidden: true });
    const sub = practice.sel ? (practice.sel.length === 1 ? '' : 'card set') : 'smart pick';
    const top = h('div', { class: 'panel' },
      h('div', {}, h('span', { class: 'tag' }, p.sec), h('b', {}, p.name), ' ', dots(p.type), sub ? h('span', { class: 'help' }, '  · ' + sub) : null),
      h('p', { class: 'statement', html: p.statement }),
      h('div', { class: 'row' }, h('button', { class: 'btn', onclick: () => { cardBox.hidden = !cardBox.hidden; } }, 'Formula card'), ' ', h('button', { class: 'btn', onclick: () => { nextProblem(); renderPractice(); } }, 'New problem (skip)')),
      cardBox);
    if (card) cardBox.append(cardEl(card, false));
    m.append(math(top));
    const stepsBox = h('div', { class: 'panel' }, h('p', { class: 'help' }, INPUT_HELP));
    m.append(stepsBox);
    const els = p.steps.map((s, i) => {
      const el = stepEl(s, i, {
        onEnter: () => check(i),
        buttons: () => [h('button', { class: 'btn primary', onclick: () => check(i) }, 'Check'), h('button', { class: 'btn', onclick: () => reveal(i) }, 'Show')],
      });
      stepsBox.append(el); return el;
    });
    const endBox = h('div'), solBox = h('div');
    m.append(endBox, solBox);
    function showSol() { if (!solBox.firstChild) solBox.append(math(h('div', { class: 'panel' }, h('div', { class: 'solution' }, h('h4', {}, 'Worked solution'), ...p.solution.map(x => h('div', { html: x })))))); }
    function sync() {
      els.forEach((el, i) => {
        const locked = i > practice.idx;
        el.classList.toggle('locked', locked);
        el._input.disabled = i !== practice.idx;
        el.querySelectorAll('button').forEach(b => b.disabled = i !== practice.idx);
      });
      if (practice.idx < els.length && (practice.idx > 0 || !matchMedia('(pointer: coarse)').matches)) els[practice.idx]._input.focus({ preventScroll: practice.idx === 0 });
    }
    function done(i, how) {
      const el = els[i], s = p.steps[i];
      el.classList.add(how === 'ok' ? 'done' : 'revealed');
      el._fb.className = 'fb ' + (how === 'ok' ? 'good' : 'warn');
      el._fb.innerHTML = how === 'ok' ? '✓ Correct' : 'Answer: ' + texHTML(s.ans) + (s.kind === 'anti' ? ' + C' : '');
      practice.idx++;
      if (practice.idx >= p.steps.length) finish();
      sync();
    }
    function check(i) {
      if (i !== practice.idx) return;
      const s = p.steps[i], el = els[i];
      const res = Check.grade(s, el._input.value);
      if (res.ok || el._input.value.trim()) showSol();
      if (res.ok) return done(i, 'ok');
      if (el._input.value.trim()) practice.missed.add(s.id);
      el._fb.className = 'fb bad'; el._fb.textContent = '✗ ' + res.msg;
    }
    function reveal(i) { if (i !== practice.idx) return; practice.missed.add(p.steps[i].id); showSol(); done(i, 'shown'); }
    function finish() {
      const clean = practice.missed.size === 0;
      if (!practice.recorded) { record(p.type, clean, [...practice.missed]); practice.recorded = true; }
      const s = store.types[p.type];
      endBox.append(math(h('div', { class: 'panel' },
        h('p', { class: 'fb ' + (clean ? 'good' : 'bad') }, clean ? `Clean solve. Streak ${Math.min(s.streak, 3)}/3${s.streak >= 3 ? ' (mastered)' : ''}.` : `Missed: ${[...practice.missed].map(stepName).join(', ')}. Streak reset to 0; this type will come back.`),
        h('p', {}, h('button', { class: 'btn primary', onclick: () => { nextProblem(); renderPractice(); } }, 'Next problem')))));
      showSol();
      renderTypeList();
      endBox.querySelector('.btn.primary').focus();
    }
    // restore progress when re-rendering the same problem
    for (let i = 0; i < practice.idx; i++) { els[i].classList.add('done'); els[i]._fb.className = 'fb good'; els[i]._fb.textContent = '✓'; }
    if (practice.idx > 0) showSol();
    sync();
    if (practice.idx >= p.steps.length) finish();
  }

  // ---------- drill ----------
  const drill = { cat: null, q: null };
  const ds = c => (store.drill[c] = store.drill[c] || { att: 0, right: 0, streak: 0 });
  function renderDrill() {
    const v = $('#view-drill'); v.innerHTML = '';
    const cats = Object.keys(Drill.CATS);
    if (!drill.q) {
      const cat = drill.cat || weightedPick(cats, cats.map(c => { const s = store.drill[c]; return !s ? 2 : s.streak >= 3 ? 0.5 : 3 + (s.att - s.right); }));
      drill.q = Drill.make(newSeed(), cat); drill.answered = false;
    }
    const q = drill.q;
    const sel = h('select', { onchange: e => { drill.cat = e.target.value || null; drill.q = null; renderDrill(); } }, h('option', { value: '' }, 'All categories (weakest first)'), cats.map(c => h('option', { value: c, selected: drill.cat === c ? 'selected' : false }, Drill.CATS[c])));
    const why = h('div', { class: 'fb', hidden: true });
    const next = h('button', { class: 'btn primary', hidden: true, onclick: () => { drill.q = null; renderDrill(); } }, 'Next question');
    const opts = h('div', { class: 'opts' }, q.options.map(o => h('button', { class: 'opt', html: o, onclick: e => {
      if (drill.answered) return; drill.answered = true;
      const right = o === q.correct, s = ds(q.cat);
      s.att++; if (right) { s.right++; s.streak++; } else s.streak = 0; save();
      opts.querySelectorAll('.opt').forEach(b => { b.disabled = true; if (b._o === q.correct) b.classList.add('right'); });
      if (!right) e.currentTarget.classList.add('wrong');
      why.hidden = false; why.className = 'fb ' + (right ? 'good' : 'bad'); why.innerHTML = (right ? '✓ ' : '✗ ') + q.why; math(why);
      next.hidden = false; next.focus(); renderDrillStats();
    } })));
    opts.querySelectorAll('.opt').forEach((b, i) => b._o = q.options[i]);
    v.append(h('div', { class: 'panel' }, h('div', {}, 'Category: ', sel), h('p', {}, h('span', { class: 'tag' }, Drill.CATS[q.cat])), math(h('p', { class: 'statement', html: q.q })), math(opts), why, next));
    const stats = h('div', { class: 'panel', id: 'drill-stats' }); v.append(stats); renderDrillStats();
  }
  function renderDrillStats() {
    const el = $('#drill-stats'); if (!el) return;
    el.innerHTML = '';
    el.append(h('table', {}, h('tr', {}, h('th', {}, 'Category'), h('th', {}, 'Right / tried'), h('th', {}, 'Streak')),
      Object.entries(Drill.CATS).map(([c, n]) => { const s = store.drill[c] || { att: 0, right: 0, streak: 0 }; return h('tr', {}, h('td', {}, n), h('td', {}, `${s.right} / ${s.att}`), h('td', {}, s.streak >= 3 ? h('span', { class: 'mastered' }, '✓ ' + s.streak) : String(s.streak))); })));
  }

  // ---------- practice test ----------
  const pick = a => a[Math.floor(Math.random() * a.length)];
  function buildTest() {
    const ids = ['disp-dist', pick(['pos-v', 'pos-a']), pick(['area-x', 'area-y', 'area-split']), pick(['washer-x', 'washer-y', 'washer-h', 'washer-v', 'slice']), pick(['shell-y', 'shell-x', 'shell-v', 'shell-h']), 'both', pick(['arc-x', 'arc-x', 'arc-y']), 'pump', 'pump'];
    return ids.map(type => ({ type, seed: newSeed() }));
  }
  let tick = null;
  function stopTimer() { clearInterval(tick); tick = null; $('#timer').hidden = true; }
  function renderTest() {
    const v = $('#view-test'); v.innerHTML = '';
    const t = store.test;
    if (!t || t.abandoned) {
      stopTimer();
      const mins = h('input', { type: 'number', min: 10, max: 180, value: 50, style: 'width:80px' });
      v.append(math(h('div', { class: 'panel' }, h('h2', {}, 'Mixed practice test'),
        h('p', {}, 'Nine problems covering 6.1, 6.2, 6.3-6.4 (disk/washer, shell, set up both ways), 6.5 and 6.7 pumping, generated fresh each time. Enter every step like on paper; nothing is checked until you submit. Then you get your score, the exact mistake on each wrong step, and full worked solutions.'),
        h('p', {}, 'Time limit (minutes): ', mins, ' ', h('button', { class: 'btn primary', onclick: () => { store.test = { items: buildTest(), answers: {}, end: Date.now() + Math.max(1, +mins.value || 50) * 60000, submitted: false }; save(); renderTest(); } }, 'Start test')))));
      return;
    }
    const probs = t.items.map(it => Gen.make(it.type, it.seed));
    if (!t.submitted) {
      $('#timer').hidden = false;
      const upd = () => { const left = Math.max(0, t.end - Date.now()); const mm = Math.floor(left / 60000), ss = Math.floor(left / 1000) % 60; $('#timer').textContent = `${mm}:${String(ss).padStart(2, '0')}`; $('#timer').classList.toggle('low', left < 5 * 60000); if (left <= 0) submit(); };
      clearInterval(tick); tick = setInterval(upd, 1000); upd();
      v.append(h('div', { class: 'panel' }, h('p', { class: 'help' }, INPUT_HELP + ' Answers are saved as you type, so a reload keeps your progress.')));
      const all = [];
      probs.forEach((p, qi) => {
        const box = h('div', { class: 'panel' }, h('div', {}, h('span', { class: 'tag' }, p.sec), h('b', {}, `Problem ${qi + 1}`)), h('p', { class: 'statement', html: p.statement }));
        p.steps.forEach((s, si) => {
          const key = qi + ':' + s.id;
          const el = stepEl(s, si, { value: t.answers[key] || '', onInput: val => { t.answers[key] = val; save(); }, onEnter: () => { const k = all.indexOf(el); if (all[k + 1]) all[k + 1]._input.focus(); } });
          all.push(el); box.append(el);
        });
        v.append(math(box));
      });
      v.append(h('div', { class: 'panel' }, h('button', { class: 'btn primary', onclick: () => { if (confirm('Submit the test for grading?')) submit(); } }, 'Submit test'), ' ', h('button', { class: 'btn', onclick: () => { if (confirm('Abandon this test? Nothing will be recorded.')) { store.test = null; save(); renderTest(); } } }, 'Abandon')));
      return;
    }
    stopTimer();
    // results
    let stepsRight = 0, stepsTot = 0, probsRight = 0, finalsRight = 0, finalsTot = 0;
    const blocks = probs.map((p, qi) => {
      const rows = []; let allOk = true; const missed = [];
      p.steps.forEach((s, si) => {
        const val = (t.answers[qi + ':' + s.id] || '').trim();
        const g = val ? Check.grade(s, val) : { ok: false, msg: 'Blank.' };
        stepsTot++; if (g.ok) stepsRight++; else { allOk = false; missed.push(s.id); }
        if (s.id === 'final') { finalsTot++; if (g.ok) finalsRight++; }
        rows.push(h('tr', {}, h('td', { html: s.label }), h('td', { class: 'your' }, val || '—'), h('td', { html: g.ok ? '<span class="fb good">✓</span>' : `<span class="fb bad">✗ ${g.msg}</span><br>Correct: ${texHTML(s.ans)}` })));
      });
      if (allOk) probsRight++;
      if (!t.recorded) record(p.type, allOk, missed);
      return math(h('div', { class: 'panel' }, h('div', {}, h('span', { class: 'tag' }, p.sec), h('b', {}, `Problem ${qi + 1}: ${p.name}`), ' ', allOk ? h('span', { class: 'fb good' }, '✓ all steps') : h('span', { class: 'fb bad' }, '✗')),
        h('p', { class: 'statement', html: p.statement }),
        h('table', {}, h('tr', {}, h('th', {}, 'Step'), h('th', {}, 'Your answer'), h('th', {}, 'Result')), rows),
        h('div', { class: 'solution' }, h('h4', {}, 'Worked solution'), ...p.solution.map(x => h('div', { html: x })))));
    });
    if (!t.recorded) { t.recorded = true; (store.testHistory = store.testHistory || []).push({ when: Date.now(), steps: stepsRight, of: stepsTot, finals: finalsRight, finalsOf: finalsTot }); save(); }
    v.append(h('div', { class: 'panel' }, h('div', { class: 'score' }, `${stepsRight} / ${stepsTot} steps correct (${Math.round(100 * stepsRight / stepsTot)}%)`),
      h('p', {}, `Final answers right: ${finalsRight} / ${finalsTot}. Problems with every step right: ${probsRight} / ${probs.length}. Missed types now count against their mastery streak.`),
      h('button', { class: 'btn primary', onclick: () => { store.test = null; save(); renderTest(); } }, 'New test')));
    blocks.forEach(b => v.append(b));
  }
  function submit() { if (!store.test || store.test.submitted) return; store.test.submitted = true; save(); stopTimer(); renderTest(); window.scrollTo(0, 0); }

  // ---------- dashboard ----------
  function renderDash() {
    const v = $('#view-dash'); v.innerHTML = '';
    const total = SMART_IDS.length, nm = SMART_IDS.filter(mastered).length;
    v.append(h('div', { class: 'panel' }, h('div', { class: 'score' }, `${nm} / ${total} problem types mastered`), h('p', { class: 'help' }, 'Mastered = solved cleanly (no wrong step, no "Show") 3 times in a row. Any miss resets the streak and Smart practice serves that type again.'),
      h('div', { class: 'bar' }, h('i', { style: `width:${100 * nm / total}%` }))));
    const fRow = (() => {
      const ss = Formulas.F.map((f, k) => store.formulas[k] || { att: 0, right: 0 }), att = ss.reduce((a, s) => a + s.att, 0), right = ss.reduce((a, s) => a + s.right, 0);
      const worst = ss.map((s, k) => [k, s.att - s.right]).filter(x => x[1] > 0).sort((a, b) => b[1] - a[1]).slice(0, 3).map(([k, n]) => `#${k + 1} (${n})`).join(', ');
      return h('tr', {}, h('td', {}, '8.1'), h('td', {}, h('a', { href: '#', onclick: e => { e.preventDefault(); show('tbl'); } }, 'Basic integration formulas (Table 8.1)')), h('td', {}, dots('tbl')), h('td', {}, String(att)), h('td', {}, att ? Math.round(100 * right / att) + '%' : '—'), h('td', {}, worst || '—'));
    })();
    const rows = [fRow, ...ON_TEST.map(t => {
      const s = store.types[t.id] || { att: 0, clean: 0, streak: 0, miss: {} };
      const worst = Object.entries(s.miss).sort((a, b) => b[1] - a[1]).slice(0, 3).map(([k, n]) => `${stepName(k)} (${n})`).join(', ');
      return h('tr', {}, h('td', {}, t.sec), h('td', {}, h('a', { href: '#', onclick: e => { e.preventDefault(); practice.sel = [t.id]; practice.p = null; show('practice'); } }, t.name)), h('td', {}, dots(t.id)), h('td', {}, String(s.att)), h('td', {}, s.att ? Math.round(100 * s.clean / s.att) + '%' : '—'), h('td', {}, worst || '—'));
    })];
    v.append(h('div', { class: 'panel' }, h('h3', {}, 'Problem types'), h('table', {}, h('tr', {}, h('th', {}, 'Sec'), h('th', {}, 'Type'), h('th', {}, 'Streak'), h('th', {}, 'Tries'), h('th', {}, 'Clean'), h('th', {}, 'Most-missed steps')), rows)));
    v.append(h('div', { class: 'panel' }, h('h3', {}, `Table 8.1 formulas: ${fCount()} / ${FN} mastered`), formulaTable()));
    const hist = (store.testHistory || []).slice(-10).reverse();
    v.append(h('div', { class: 'panel' }, h('h3', {}, 'Practice tests'), hist.length ? h('table', {}, h('tr', {}, h('th', {}, 'When'), h('th', {}, 'Steps'), h('th', {}, 'Final answers')), hist.map(x => h('tr', {}, h('td', {}, new Date(x.when).toLocaleString()), h('td', {}, `${x.steps}/${x.of} (${Math.round(100 * x.steps / x.of)}%)`), h('td', {}, `${x.finals}/${x.finalsOf}`)))) : h('p', { class: 'help' }, 'No tests taken yet.')));
    const dpanel = h('div', { class: 'panel', id: 'drill-stats' }); v.append(h('h3', {}, 'Which-method drill'), dpanel); renderDrillStats();
    v.append(h('p', {}, h('button', { class: 'btn', onclick: () => { if (confirm('Erase all progress?')) { localStorage.removeItem(KEY); location.reload(); } } }, 'Reset all progress')));
  }

  window.__state = { practice, drill, store, tbl };
  show(store.test && !store.test.submitted ? 'test' : views.includes(location.hash.slice(1)) ? location.hash.slice(1) : 'practice');
})();
