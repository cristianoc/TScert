// A guarded record invariant (PROGRAM-TYPING.md, "Guarded clauses"), in the
// shape of pretext's `line-break.ts`: `discretionaryHyphenContexts` is null
// where the text has no soft hyphen, and otherwise holds one entry per
// segment, parallel to `widths`. The invariant
// `this.contexts === null || this.contexts.length === this.widths.length` is
// each walker's precondition and each builder's result fact: `prepare`'s
// return proves it where its test of the given contexts either found `null`
// or found their length equal, `prepareHard`'s where the field is `null`.
// `narrowing`, pretext's `returnsFromUnfitHyphen`, destructures the field and
// reads `contexts[i]!` under `contexts !== null`; `sumAt` tests the path
// itself.

/** @invariant this.contexts === null || this.contexts.length === this.widths.length */
export type Data = {
  widths: number[];
  contexts: number[] | null;
};

export function prepare(texts: string[], contexts: number[] | null): Data {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  if (contexts !== null && contexts.length !== widths.length)
    throw new Error("one context per segment");
  return { widths, contexts };
}

export function prepareHard(texts: string[]): Data {
  const widths: number[] = [];
  for (const t of texts) widths.push(t.length);
  return { widths, contexts: null };
}

/** @requires safeInteger(start) && safeInteger(last) && 0 <= start && last < prepared.widths.length */
export function narrowing(prepared: Data, start: number, last: number): number {
  const { contexts } = prepared;
  let n = 0;
  if (contexts !== null) for (let i = start; i <= last; i++) n += contexts[i]!;
  return n;
}

/** @requires safeInteger(i) && 0 <= i && i < prepared.widths.length */
export function sumAt(prepared: Data, i: number): number {
  if (prepared.contexts === null) return 0;
  return prepared.contexts[i]!;
}

export function layout(texts: string[], contexts: number[] | null): number {
  const prepared = prepare(texts, contexts);
  const n = prepared.widths.length;
  if (n > 0) return narrowing(prepared, 0, n - 1) + sumAt(prepared, n - 1);
  return 0;
}

export function layoutHard(texts: string[]): number {
  const prepared = prepareHard(texts);
  const n = prepared.widths.length;
  if (n > 0) return sumAt(prepared, n - 1);
  return 0;
}
