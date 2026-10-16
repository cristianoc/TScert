// `Array.isArray`, and `instanceof Array`, on `unknown` find a built-in
// array: `unknown` carries the array invariant, so a value owning an array's
// store holds a possibly sparse store of `unknown` values and
// `Array.prototype`. A thrown value is of `unknown` as well.
export function elements(x: unknown): readonly unknown[] {
  if (Array.isArray(x)) return x;
  return [];
}

export function first(x: unknown): unknown {
  if (x instanceof Array) return x[0];
  return undefined;
}

export function size(x: unknown): number {
  if (Array.isArray(x)) return x.length;
  return 0;
}

export function nested(x: unknown): number {
  if (Array.isArray(x)) {
    const y: unknown = x[0];
    if (Array.isArray(y)) return y.length;
  }
  return 0;
}

export function caught(f: () => void): number {
  try {
    f();
  } catch (e) {
    if (Array.isArray(e)) return e.length;
  }
  return 0;
}

// Each operand of `&&` sees what the earlier ones found.
declare function sharedRO<T>(a: ReadonlyArray<T>, b: ReadonlyArray<T>): number;

export function both(u: unknown, w: unknown): number {
  if (u instanceof Array && w instanceof Array) return sharedRO(u, w);
  return 0;
}

type R = { a: number };

export function lengths(u: R | string[], w: R | string[]): number {
  if (Array.isArray(u) && Array.isArray(w)) return u.length + w.length;
  return 0;
}
