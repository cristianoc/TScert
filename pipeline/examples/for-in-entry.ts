// A read at the key a `for...in` step visited, where nothing that could change
// the entry ran since the step, is the value the step found there: a
// dictionary's index type, not `undefined`.
export function sum(v: { [k: string]: number }): number {
  let total = 0;
  for (const k in v) {
    total = total + v[k]!;
  }
  return total;
}

// A call after the read changes nothing already read.
export function lastLogged(
  v: { [k: string]: number },
  log: (n: number) => void,
): number {
  let last: number = 0;
  for (const k in v) {
    const skipped: boolean = k === "";
    const value: number = v[k]!;
    log(value);
    if (!skipped) last = value;
  }
  return last;
}

// A chain of reads the loop's body cannot change finds the same object.
export function joined(o: {
  readonly inner: { readonly [k: string]: string };
}): string {
  let out: string = "";
  for (const k in o.inner) {
    const piece: string = o.inner[k]!;
    out = out + k + piece;
  }
  return out;
}

export function products(
  a: { [k: string]: number },
  b: { [k: string]: number },
): number {
  let n: number = 0;
  for (const x in a) {
    const ax: number = a[x]!;
    for (const y in b) {
      n = n + ax * b[y]!;
    }
  }
  return n;
}
