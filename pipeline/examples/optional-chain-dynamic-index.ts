// A read at a `number` key in an optional chain, `xs?.[i]` or a later link
// `o?.args[i]`, is the host's `%ElementAt%` on the chain's present value:
// the element at an index below the length, else `undefined`, as outside a
// chain. A chain that skips is `undefined` too.
export function at(
  xs: readonly string[] | undefined,
  i: number,
): string | undefined {
  return xs?.[i];
}

export function argAt(
  o: { args: readonly string[] } | undefined,
  i: number,
): string | undefined {
  return o?.args[i];
}

export function lengthAt(xs: readonly string[] | null, i: number): number {
  return xs?.[i]?.length ?? 0;
}

// The index of one array read in another, which may be shorter.
export function paired(
  xs: readonly string[],
  ys: readonly number[] | undefined,
): number {
  let total = 0;
  xs.forEach((x, i) => {
    total += ys?.[i] ?? x.length;
  });
  return total;
}

// A second `?.` before the read, a read after a call in the chain.
export function nestedAt(
  o: { a?: readonly string[] } | undefined,
  i: number,
): string | undefined {
  return o?.a?.[i];
}

export function calledAt(
  o: { list(): readonly string[] } | undefined,
  i: number,
): string | undefined {
  return o?.list()[i];
}

// The key is evaluated only where the chain does not skip.
export function skippedKey(xs: readonly string[] | undefined): number {
  let k = 0;
  const v = xs?.[k++];
  return k + (v?.length ?? 0);
}
