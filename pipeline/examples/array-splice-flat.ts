// `splice` without items and `flat()` at its default depth, read through the
// array prototype's reviewed contract.
// Census functions:
// files.mts#withLedger, declaration-graph.mts#collect,
// computed-types.mts#indexedAccess, written-applications.mts#writtenApplications.
declare const values: { value: number }[];

// A module's array spliced in the `finally` block of a generic function.
export function use<T>(run: () => T): T {
  try {
    return run();
  } finally {
    values.splice(0, 1);
  }
}

// The removed elements, a fresh array read at the receiver's elements; the
// receiver keeps its contract.
export function removed(xs: string[], at: number): string[] {
  const out = xs.splice(at);
  out.push("end");
  xs.push("tail");
  return out;
}

export function firstRemoved(xs: number[]): number {
  for (const x of xs.splice(0, 1)) return x;
  return -1;
}

// One level of flattening: a mutable and a readonly receiver, and arrays of
// arrays, whose own elements are kept as they are.
export function joined(lines: string[][]): string[] {
  return lines.flat();
}

export function levels(groups: readonly (readonly number[][])[]): number[][] {
  return groups.flat();
}

// The result holds no hole: spread and iterated at its elements.
export function total(rows: readonly (readonly number[])[]): number {
  let sum = 0;
  for (const n of [...rows.flat()]) sum += n;
  return sum;
}
