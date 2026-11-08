// A local named as a module function, `after`: the fragment names it
// `after@L:C`, and a fact about it names that binding, so `after = i` with
// `i < xs.length` bounds the read `xs[after]!` (pretext's line walkers
// declare a local `after` beside `function after`).

function after(i: number): number {
  return i + 1;
}

export function walk(xs: number[]): number {
  let s = 0;
  for (let i = 0; i < xs.length; i++) {
    const after = i;
    s += xs[after]!;
  }
  return s;
}

export function next(i: number): number {
  return after(i);
}
