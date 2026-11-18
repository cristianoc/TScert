// The walker's module of readonly-frame-walker, with a member that awaits
// (docs/drafts/readonly-handles.md, "No suspension"): `total` reads the
// widths it was given read-only, awaits, and reads on. Its call returns at
// the `await`, so the caller may then truncate its own array, which the
// read-only frame would hold protected for the call: under Node,
// `total({ widths: xs })` with `xs.length = 1` set after the call reads
// `xs[1]` as `undefined` (tests/node-runs.mts). (S) refuses the module's
// certificate at the `async` function and at its `await`.
/** A handle: the widths a walker reads. */
export type H = { readonly widths: readonly number[] };

export function walk(h: H, visit: () => void): number {
  const w = h.widths;
  let sum = 0;
  for (let i = 0; i < w.length; i++) {
    visit();
    sum += w[i] ?? 0;
  }
  return sum;
}

export async function total(h: H): Promise<number> {
  const w = h.widths;
  const n = w.length;
  await null;
  let sum = 0;
  for (let i = 0; i < n; i++) sum += w[i] as number;
  return sum;
}
