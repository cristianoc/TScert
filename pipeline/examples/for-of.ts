// `for...of` over an array binds each element in turn: a readonly or mutable
// array, a literal, loops nested with `break` and `continue`, and a return
// from inside the loop.
export function count(xs: readonly boolean[]): number {
  let n: number = 0;
  for (const x of xs) {
    if (x) {
      n = n + 1;
    }
  }
  return n;
}
export function first(xs: readonly number[], fallback: number): number {
  for (const x of xs) {
    return x;
  }
  return fallback;
}
export function nested(xs: readonly number[], ys: readonly string[]): number {
  let n: number = 0;
  for (const x of xs) {
    for (const y of ys) {
      if (y === "stop") {
        break;
      }
      n = n + x;
    }
    if (x === 0) {
      continue;
    }
    n = n + 1;
  }
  return n;
}
export function literal(): number {
  let n: number = 0;
  for (const s of ["a", "b"]) n = n + 1;
  return n;
}
export function fields(xs: { a: boolean }[]): boolean {
  for (const o of xs) {
    if (o.a) {
      return true;
    }
  }
  return false;
}
