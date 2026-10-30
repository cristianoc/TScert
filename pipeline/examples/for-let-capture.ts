// JavaScript copies a `for` loop's `let` bindings into each iteration
// (CreatePerIterationEnvironment): a closure created in an iteration holds
// that iteration's binding, which the next iteration's update does not write.
// Under Node, `values(3)` is `[0, 1, 2]`, `fixpoint([1, 3])` is 3,
// `skips(4)` is `[0, 0, 3]` and `steps(3)` is `[0, 1, 2]`.
export function values(n: number): number[] {
  const fs: (() => number)[] = [];
  for (let i: number = 0; i < n; i = i + 1) {
    fs.push(() => i);
  }
  const out: number[] = [];
  for (const f of fs) out.push(f());
  return out;
}

// A callback writes the iteration's binding, and the test reads what it
// wrote: the shape of `functionPlacement`'s loop (fragment-statements.mts).
export function fixpoint(xs: readonly number[]): number {
  let rounds: number = 0;
  for (let changed = true; changed; ) {
    changed = false;
    rounds = rounds + 1;
    xs.forEach((x) => {
      if (x > rounds) changed = true;
    });
  }
  return rounds;
}

// A `continue` runs the update on the next iteration's binding; a closure in
// the head's initializer holds the head's own binding, which the iterations
// copy and never write.
export function skips(n: number): number[] {
  const out: number[] = [];
  for (let i: number = 0, first: () => number = () => i; i < n; i = i + 1) {
    if (i === 1) continue;
    out.push(i % 2 === 0 ? first() : (() => i)());
  }
  return out;
}

// Closures in the test and the update read the binding of the iteration
// they run in; a body that is one statement.
export function steps(n: number): number[] {
  const out: number[] = [];
  for (let i: number = 0; (() => i)() < n; i = (() => i + 1)()) out.push(i);
  return out;
}

// The update's escaping closure shares the following test/body cell.
export function updateClosures(): number[] {
  const fs: (() => number)[] = [];
  for (let i: number = 0; i < 3; fs.push(() => i), i = i + 1) {
    if (i === 1) i = 2;
  }
  const out: number[] = [];
  for (const f of fs) out.push(f());
  return out;
}

// Even the failing test retains its own cell; the body writes earlier cells.
export function testClosures(): number[] {
  const fs: (() => number)[] = [];
  for (let i: number = 0; fs.push(() => i), i < 3; i = i + 1) {
    i = i + 1;
  }
  const out: number[] = [];
  for (const f of fs) out.push(f());
  return out;
}

// Inner transfers target the inner loop; both heads have captured cells.
export function nested(): number[] {
  const fs: (() => number)[] = [];
  for (let i: number = 0; i < 2; i = i + 1) {
    for (let j: number = 0; j < 3; j = j + 1) {
      if (j === 0) continue;
      fs.push(() => i * 10 + j);
      break;
    }
  }
  const out: number[] = [];
  for (const f of fs) out.push(f());
  return out;
}

// The finalizer overrides a break with continue, then a continue with break.
export function finalizerTransfers(): number[] {
  const fs: (() => number)[] = [];
  for (let i: number = 0; i < 3; i = i + 1) {
    fs.push(() => i);
    try {
      if (i === 0) break;
      continue;
    } finally {
      i = i + 1;
      if (i === 1) continue;
      break;
    }
  }
  const out: number[] = [];
  for (const f of fs) out.push(f());
  return out;
}
