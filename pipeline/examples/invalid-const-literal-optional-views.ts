// A constant's literal also held as a writable dictionary, whose holder may
// add keys, is not claimed with its exact keys (nor would they meet the
// dictionary): a view saying `a` is absent is not derived.
export function views(): void {
  const t = {};
  const f: { a?: number } = t;
  const g: { [k: string]: boolean } = t;
}
