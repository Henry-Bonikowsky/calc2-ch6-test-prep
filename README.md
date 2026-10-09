# MA-172 Chapter 6 test prep

Static offline study site (open `index.html` in a browser; no server needed).
Covers Briggs/Cochran 6.1, 6.2, 6.3-6.4 (incl. general slicing with known cross-sections), 6.5, 6.7 pumping (6.6 skipped), and the Table 8.1 basic integration formulas.

- `problems.js` generators (exact answers, per-step checks, mistake hints, worked solutions)
- `check.js` answer checking (math.js; numeric equivalence at random points)
- Type `hw` serves the exact assigned book problems (6.4 #5,6,9,12,13,15,20,22,24,35,39-44,53; 6.5 #3-8,10), each step-checked.
- Types `sh-*` ("Shapes" section) drill the slice set-up for pumping/force: width or radius at height y, then A(y), for tanks, cones, spheres and troughs.
- `coverage.md` lists what the test covers, each topic with its source and the site type that drills it.
- `formulas.js` Table 8.1 formulas ("Integration formulas" view): typed-answer checking in book notation and multiple-choice wrong answers; per-formula mastery.
- Types with `off: true` (springs, chains, plate force, thin-bar mass) are kept but not on the test: only in the collapsed "Not on the test" groups.
- `drill.js` "which method?" questions, `cards.js` formula cards, `app.js` UI
- Progress lives in localStorage key `ma172ch6.v1`.

Verify every answer key against independent numerical integration:

    node test/verify.js 300
