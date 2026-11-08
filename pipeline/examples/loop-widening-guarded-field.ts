// Each assignment propagates the literal by one binding per iteration.
type Trims = { trims: number[] | null };

export function sumTrims(record: Trims, n: number): number {
  let a = 0;
  let b = 0;
  let c = 0;
  let d = 0;
  let e = 0;
  let f = 0;
  let sum = 0;
  for (let k = 0; k < n; k++) {
    if (record.trims !== null) sum += record.trims[k] ?? 0;
    f = e;
    e = d;
    d = c;
    c = b;
    b = a;
    a = 1;
  }
  return sum + a + b + c + d + e + f;
}
