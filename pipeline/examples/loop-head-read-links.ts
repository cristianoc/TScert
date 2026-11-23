// A local copy of a field keeps its read link across a loop head when every
// edge into the head preserves the field: direct copy, object destructuring,
// an alias of the copy, and a loop body calling a function whose effect keeps
// fields (`Modifies<{ spines: "grow" }, void>`).

export function sumVia(h: { xs: number[] }): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) s += xs[i]!;
  return s;
}

export function sumDestructured(h: { xs: number[] }): number {
  const { xs } = h;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) s += xs[i]!;
  return s;
}

function pushZero(out: number[]): Modifies<{ spines: "grow" }, void> {
  out.push(0);
}

export function sumViaGrow(h: { xs: number[] }, out: number[]): number {
  const xs = h.xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) {
    pushZero(out);
    s += xs[i]!;
  }
  return s;
}

export function sumViaAlias(h: { xs: number[] }): number {
  const xs = h.xs;
  const ys = xs;
  let s = 0;
  for (let i = 0; i < h.xs.length; i++) s += ys[i]!;
  return s;
}

export function sumViaLengthField(h: { length: number[] }): number {
  const xs = h.length;
  let s = 0;
  for (let i = 0; i < h.length.length; i++) s += xs[i]!;
  return s;
}

export function sumDestructuredLengthField(h: { length: number[] }): number {
  const { length } = h;
  let s = 0;
  for (let i = 0; i < h.length.length; i++) s += length[i]!;
  return s;
}
