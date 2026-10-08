# MA-172 Chapter 6 test prep

Static offline study site (open `index.html` in a browser; no server needed).
Covers Briggs/Cochran 6.1, 6.2, 6.3-6.4 (incl. general slicing with known cross-sections), 6.5, 6.7 (6.6 skipped).

- `problems.js` generators (exact answers, per-step checks, mistake hints, worked solutions)
- `check.js` answer checking (math.js; numeric equivalence at random points)
- Type `hw` serves the exact assigned book problems (6.4 #5,6,9,12,13,15,20,22,24,35,39-44,53; 6.5 #3-8,10), each step-checked.
- `coverage.md` lists what the test covers, each topic with its source and the site type that drills it.
- `drill.js` "which method?" questions, `cards.js` formula cards, `app.js` UI
- Progress lives in localStorage key `ma172ch6.v1`.

Verify every answer key against independent numerical integration:

    node test/verify.js 300
