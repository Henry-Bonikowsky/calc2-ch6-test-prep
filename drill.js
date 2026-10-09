// "Which method?" decision drill: generated multiple-choice questions.
(function (root, factory) {
  if (typeof module === 'object' && module.exports) module.exports = factory(require('./problems.js'), require('./check.js'));
  else root.Drill = factory(root.Gen, root.Check);
})(this, function (Gen, Check) {
  const T = s => Check.tex(s);
  const CATS = {
    variable: 'dx or dy for this method/axis',
    diskwasher: 'Disk or washer?',
    which: 'Which method is practical?',
    radius: 'Radius about a shifted line',
    split: 'dx or dy: avoid splitting',
    distance: 'Distance vs displacement vs position',
    shift: 'What changes when the axis moves',
    work: 'Pumping: lift distance',
  };
  const axisName = (kind, k) => kind === 'h' ? (k === 0 ? 'the \\(x\\)-axis' : `the line \\(y = ${k}\\)`) : (k === 0 ? 'the \\(y\\)-axis' : `the line \\(x = ${k}\\)`);

  function shuffle(r, a) { a = a.slice(); for (let i = a.length - 1; i > 0; i--) { const j = r.int(0, i); [a[i], a[j]] = [a[j], a[i]]; } return a; }

  const gens = {
    variable(r) {
      const kind = r.pick(['h', 'v']), k = r.pick([0, 0, -2, -1, 3, 5]), method = r.pick(['disk/washer', 'shell']);
      const along = kind === 'h' ? 'dx' : 'dy';
      const correct = method === 'shell' ? (along === 'dx' ? 'dy' : 'dx') : along;
      return { q: `You revolve a region about ${axisName(kind, k)} using the <b>${method}</b> method. You integrate with respect to:`, options: ['\\(dx\\)', '\\(dy\\)'], correct: `\\(${correct}\\)`,
        why: method === 'shell' ? `Shells run <b>parallel</b> to the axis, so their thickness is in the other variable: about a ${kind === 'h' ? 'horizontal' : 'vertical'} axis, shells use \\(${correct}\\).` : `Disks/washers are slices <b>perpendicular</b> to the axis, so their thickness is along the axis: \\(${correct}\\).` };
    },
    diskwasher(r) {
      const id = r.pick(['washer-x', 'washer-h', 'washer-y', 'washer-v']);
      const p = Gen.make(id, r.int(1, 1e9));
      const disk = p.steps.find(s => s.id === 'r').ans === '0';
      const stmt = p.statement.replace(/\. Use the disk\/washer method.*$/, '');
      return { q: `${stmt}. It is revolved about ${axisName(p.axis.kind, p.axis.k)}. Slicing perpendicular to the axis gives:`, options: ['Disks (no hole)', 'Washers (hole)'], correct: disk ? 'Disks (no hole)' : 'Washers (hole)',
        why: disk ? 'Every slice runs from the axis itself out to the far curve, so there is no hole: r = 0.' : 'The region does not touch the axis along each slice, so each slice has a gap of air next to the axis: a washer with inner radius r.' };
    },
    which(r) {
      const idx = r.pick([6, 7, 8, 9, 10]);
      const R = Gen.REGIONS[idx](r);
      const kind = r.pick(['h', 'v']), k = kind === 'h' ? r.pick([0, -1, -2]) : r.pick([0, -1, -2]);
      const opts = ['Disk/washer with \\(dx\\)', 'Shells with \\(dx\\)', 'Disk/washer with \\(dy\\)', 'Shells with \\(dy\\)'];
      const correct = kind === 'h' ? opts[0] : opts[1];
      return { q: `${Gen._internal.regionText(R)}. It is revolved about ${axisName(kind, k)}. Which setup is practical?`, options: opts, correct,
        why: `A curve here can't be solved cleanly for \\(x\\) as one function of \\(y\\), so stay with \\(dx\\). ${kind === 'h' ? 'About a horizontal axis, dx slices are perpendicular to it: disks/washers.' : 'About a vertical axis, dx slices are parallel to it: shells.'}` };
    },
    radius(r) {
      const curves = ['x^2', 'sqrt(x)', '2 x + 1', '4 - x^2', 'x^3', 'e^x'];
      const f = r.pick(curves), kind = r.pick(['washer', 'shell']);
      if (kind === 'washer') {
        const below = r.bool(), k = below ? -r.int(1, 4) : r.int(5, 9);
        const ft = T(f), K = Math.abs(k);
        const correct = below ? `\\(${ft} + ${K}\\)` : `\\(${k} - (${ft})\\)`;
        const opts = below ? [correct, `\\(${ft} - ${K}\\)`, `\\(${ft}\\)`, `\\(-${K} - (${ft})\\)`] : [correct, `\\(${ft} - ${k}\\)`, `\\(${ft}\\)`, `\\(${ft} + ${k}\\)`];
        return { q: `A washer slice has its edge on \\(y = ${ft}\\). The axis is \\(y = ${k}\\), which lies ${below ? 'below' : 'above'} the region. The distance from the axis to that edge is:`, options: opts, correct,
          why: `Radius = distance = (bigger y) − (smaller y) = ${below ? `\\(${ft} - (${k}) = ${ft} + ${K}\\)` : `\\(${k} - (${ft})\\)`}.` };
      }
      const left = r.bool(), k = left ? -r.int(1, 4) : r.int(4, 8), K = Math.abs(k);
      const correct = left ? `\\(x + ${K}\\)` : `\\(${k} - x\\)`;
      const opts = left ? [correct, `\\(x - ${K}\\)`, `\\(x\\)`, `\\(${K} - x\\)`] : [correct, `\\(x - ${k}\\)`, `\\(x\\)`, `\\(x + ${k}\\)`];
      return { q: `Shells with \\(dx\\) about the line \\(x = ${k}\\) (${left ? 'left of' : 'right of'} the region). The shell radius is:`, options: opts, correct,
        why: `Radius = distance from the axis to the shell at \\(x\\): ${left ? `\\(x - (${k}) = x + ${K}\\)` : `\\(${k} - x\\)`}. The height doesn't change when the axis moves.` };
    },
    split(r) {
      const n = r.pick([1, 2, 3]), c = n * (n + 1);
      const bank = [
        { d: `\\(y = \\sqrt{x}\\), \\(y = x - ${c}\\), and \\(y = 0\\)`, a: 'dy', w: `In \\(dx\\) the bottom boundary switches from \\(y = 0\\) to \\(y = x - ${c}\\) at \\(x = ${c}\\), so you'd need two integrals. In \\(dy\\): right \\(x = y + ${c}\\), left \\(x = y^2\\), one integral.` },
        { d: `\\(y = x\\), \\(y = ${2 * n} - x\\), and \\(y = 0\\)`, a: 'dy', w: `In \\(dx\\) the top switches at \\(x = ${n}\\). In \\(dy\\): left \\(x = y\\), right \\(x = ${2 * n} - y\\), one integral.` },
        { d: `\\(x = y^2\\) and \\(x = y + 2\\)`, a: 'dy', w: 'In \\(dx\\) the bottom switches from \\(-\\sqrt{x}\\) to \\(x - 2\\) at \\(x = 1\\). In \\(dy\\): right \\(x = y + 2\\), left \\(x = y^2\\), one integral.' },
        { d: `\\(y = x^2\\), \\(y = 2 - x\\), and \\(y = 0\\) (first quadrant)`, a: 'dy', w: 'In \\(dx\\) the top switches at \\(x = 1\\). In \\(dy\\): left \\(x = \\sqrt{y}\\), right \\(x = 2 - y\\), one integral.' },
        { d: `\\(y = x\\), \\(y = x/2\\), and \\(x = ${2 * n}\\)`, a: 'dx', w: `In \\(dx\\): top \\(y = x\\), bottom \\(y = x/2\\), one integral. In \\(dy\\) the right boundary switches from \\(x = 2y\\) to \\(x = ${2 * n}\\) at \\(y = ${n}\\).` },
        { d: `\\(y = x^2\\) and \\(y = ${n === 1 ? '' : n + ''}x\\)`, a: 'either', w: 'Both ways the same two curves bound every slice, so no split either way.' },
      ];
      const b = r.pick(bank);
      const opts = ['\\(dx\\) (one integral)', '\\(dy\\) (one integral)', 'Either, no split needed'];
      return { q: `Area of the region bounded by ${b.d}. Which variable lets you use a single integral?`, options: opts, correct: b.a === 'dx' ? opts[0] : b.a === 'dy' ? opts[1] : opts[2], why: b.w };
    },
    distance(r) {
      const bank = [
        ['the total distance the object travels on [0, 4]', 1], ['the displacement on [0, 4]', 0], ['the net change in position on [0, 4]', 0],
        ['how far the object is from where it started at t = 4', 0], ['the odometer reading after 4 seconds', 1], ['the position at t = 4, given s(0) = 3', 2],
        ['where the object is at t = 4 if it starts at s = 3', 2], ['the total length of the path traveled from t = 0 to t = 4', 1],
      ];
      const [phrase, i] = r.pick(bank);
      const opts = ['\\(\\int_0^4 v(t)\\,dt\\)', '\\(\\int_0^4 |v(t)|\\,dt\\)', '\\(3 + \\int_0^4 v(t)\\,dt\\)'];
      return { q: `Given velocity \\(v(t)\\), which integral gives ${phrase}?`, options: opts, correct: opts[i],
        why: ['Displacement / net change keeps signs: backward motion cancels forward motion. Just integrate v. ("How far from start" is the size of this, still no splitting into |v|.)', 'Distance counts every meter, forward or back: integrate |v| by splitting where v = 0.', 'Position = starting position + displacement.'][i] };
    },
    shift(r) {
      const method = r.pick(['shell', 'washer']), k = r.pick([-3, -2, -1, 2, 4]), kind = r.pick(['h', 'v']);
      if (method === 'shell') {
        const opts = ['Only the radius', 'Only the height', 'Both radius and height', 'Nothing'];
        return { q: `Shell method: you switch the axis from ${axisName(kind, 0)} to ${axisName(kind, k)}. What changes in the setup?`, options: opts, correct: opts[0], why: 'Moving the axis changes the shell radius (distance to the new line). The height (top − bottom or right − left) and the bounds stay the same.' };
      }
      const opts = ['Both R and r (each measured from the new line)', 'Only R', 'Only r', 'Only the bounds'];
      return { q: `Washer method: you switch the axis from ${axisName(kind, 0)} to ${axisName(kind, k)}. What changes in the setup?`, options: opts, correct: opts[0], why: 'Each radius is a distance to the axis, so both are re-measured from the new line. The bounds stay the same.' };
    },
    work(r) {
      const t = 'pump'; // only pumping is on the test; spring, plate, chain kept below
      if (t === 'spring') {
        const L0 = r.pick([10, 20, 25]), L1 = L0 + r.pick([5, 10, 15]);
        const right = `\\(${(L1 - L0) / 100}\\) m`;
        return { q: `A spring's natural length is ${L0} cm. It is stretched to a length of ${L1} cm. In Hooke's law \\(F = kx\\), what is \\(x\\)?`, options: [right, `\\(${L1 / 100}\\) m`, `\\(${L1 - L0}\\) m`, `\\(${L1}\\) m`], correct: right, why: 'x is the stretch beyond the natural length, in meters.' };
      }
      if (t === 'pump') {
        const H = r.pick([4, 5, 6]), h = r.pick([0, 1, 2]), top = H + h;
        const right = `\\(${top} - y\\)`;
        return { q: `Water is pumped from a tank of height ${H} m ${h ? `to an outlet ${h} m above the top` : 'out over the top'}. With \\(y\\) measured up from the bottom, a slice at height \\(y\\) is lifted:`, options: [right, '\\(y\\)', h ? `\\(${H} - y\\)` : `\\(${H}\\)`, `\\(y - ${top}\\)`], correct: right, why: `It has to reach height ${top}; it is already at y, so it rises ${top} − y.` };
      }
      if (t === 'plate') {
        const H = r.pick([2, 3, 4]), s = r.pick([0, 1, 2]), a = H + s;
        const right = `\\(${a} - y\\)`;
        return { q: `A vertical plate ${H} m tall has its top edge ${s ? s + ' m below' : 'at'} the water surface. With \\(y\\) measured up from the bottom of the plate, the depth of a strip at height \\(y\\) is:`, options: [right, '\\(y\\)', `\\(${a + 1} - y\\)`, `\\(y - ${a}\\)`], correct: right, why: `The surface is at y = ${a}; depth is measured down from it: ${a} − y. Pressure = ρg·depth.` };
      }
      const L = r.pick([10, 20, 30]);
      const right = '\\(y\\)';
      return { q: `A ${L} m chain hangs from the top of a building; \\(y\\) = distance of a small piece below the top. Pulling the whole chain up lifts that piece:`, options: [right, `\\(${L} - y\\)`, `\\(${L}\\)`, `\\(${L / 2}\\)`], correct: right, why: 'A piece y below the top has to rise y to reach the top. Work = ∫ (weight per length)·y dy.' };
    },
  };

  function make(seed, cat) {
    const r = Gen.rng(seed);
    cat = cat || r.pick(Object.keys(gens));
    const d = gens[cat](r);
    return { cat, q: d.q, options: shuffle(r, d.options), correct: d.correct, why: d.why };
  }
  return { make, CATS };
});
