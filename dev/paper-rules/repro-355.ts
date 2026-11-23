// Issue #355.
// A local object the function allocates and never passes anywhere keeps
// its facts across a call to a callback: the callback cannot reach it.

type Cursor = { i: number };

/** @requires safeInteger(c.i) && 0 <= c.i && c.i < xs.length
 *  @ensures safeInteger(c.i) && 0 <= c.i */
function step(xs: number[], c: Cursor): Modifies<{ "c.*": "scalar" }, number> {
  const x = xs[c.i]!;
  c.i = c.i + 1;
  return x;
}

// Accepted: no callback between the steps.
export function walk(xs: number[]): number {
  const c: Cursor = { i: 0 };
  const n = xs.length;
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= n) return total;
    total += step(xs, c);
  }
}

// Refused (safe): the callback's call drops the facts over c.i, which the
// callback cannot reach.
export function walkVisiting(xs: number[], onStep: (x: number) => void): number {
  const c: Cursor = { i: 0 };
  const n = xs.length;
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= n) return total;
    const x = step(xs, c);
    total += x;
    onStep(x);
  }
}

// `paperAssume(fact, "#N");` is the prototype's unsafe assume: the prototype
// checks it as `if (!(fact)) throw "#N";`, so past it the pass knows `fact`
// as on the branch where it holds, and names the issue in its verdict; the
// ordinary verifier reads it as a call that changes nothing.
function paperAssume(fact: boolean, issue: string): Modifies<{}, void> {}

// Accepted by the prototype, naming #355; refused by the ordinary verifier.
// The facts over c.i the call of onStep drops are assumed after it. The loop
// reads xs.length at each test, which onStep may change.
export function walkVisitingAssumed(xs: number[], onStep: (x: number) => void): number {
  const c: Cursor = { i: 0 };
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= xs.length) return total;
    const x = step(xs, c);
    total += x;
    onStep(x);
    const i = c.i;
    paperAssume(Number.isSafeInteger(i) && 0 <= i, "#355"); // unsafe assume until #355
  }
}

// Refused (safe): the assumed fact gives c.i a safe integer but not
// 0 <= c.i, which step requires.
export function walkVisitingWeak(xs: number[], onStep: (x: number) => void): number {
  const c: Cursor = { i: 0 };
  let total = 0;
  while (true) {
    const s = c.i;
    if (s >= xs.length) return total;
    const x = step(xs, c);
    total += x;
    onStep(x);
    const i = c.i;
    paperAssume(Number.isSafeInteger(i), "#355"); // unsafe assume until #355
  }
}
