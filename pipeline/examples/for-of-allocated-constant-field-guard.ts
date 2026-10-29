// A field of a constant bound to an object literal, tested before a
// `for...of` loop: the iterator's separation leaves out such a constant, so
// a step keeps no read link about its fields and the loop's cuts claim
// none, whether the field is reread after the loop (`after`) or not
// (`across`), and in a closure capturing the constant (`captured`).
export function after(s: string | null, xs: readonly number[]): number {
  const f: { v: string | null } = { v: s };
  if (!f.v) return 0;
  let n = 0;
  for (const x of xs) n += x;
  return n + f.v.length;
}

export function across(s: string | null, xs: readonly number[]): number {
  const f: { v: string | null } = { v: s };
  if (!f.v) return 0;
  let n = 0;
  for (const x of xs) n += x;
  return n;
}

export function captured(
  s: string | null,
  xs: readonly number[],
): () => number {
  const f: { v: string | null } = { v: s };
  return (): number => {
    if (!f.v) return 0;
    let n = 0;
    for (const x of xs) n += x;
    return n;
  };
}
