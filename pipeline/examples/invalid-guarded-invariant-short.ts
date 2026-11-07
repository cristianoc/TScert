// A builder returning a nullable parallel array one element short: `prepare`
// states the guarded invariant `this.contexts === null ||
// this.contexts.length === this.widths.length` of its result, which its
// return, given contexts it never tests, does not establish, and is refused
// there. The walker reading below `widths.length` under `contexts !== null`
// then reads past the array's end (run under Node:
// `narrowing(prepare(["a", "b"], [1]), 0, 1)` reads `undefined` at `number`
// and returns `NaN`).

/** @invariant this.contexts === null || this.contexts.length === this.widths.length */
export type Data = {
  widths: number[];
  contexts: number[] | null;
};

export function prepare(texts: string[], contexts: number[] | null): Data {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  return { widths, contexts };
}

/** @requires safeInteger(start) && safeInteger(last) && 0 <= start && last < prepared.widths.length */
export function narrowing(prepared: Data, start: number, last: number): number {
  const { contexts } = prepared;
  let n = 0;
  if (contexts !== null) for (let i = start; i <= last; i++) n += contexts[i]!;
  return n;
}
