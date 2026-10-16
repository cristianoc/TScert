// A test keeps a type parameter's value within its bound's values the test
// admits: the meet of the parameter with them, still a `T`.

// `x ?? d` takes `x` where it is neither null nor undefined: `T ⊓ number`.
export function present<T extends number | null | undefined>(x: T): number {
  return x ?? 0;
}

export function presentString<T extends string | null>(x: T): string | number {
  return x ?? 0;
}

export function presentEither<T extends number | string | null>(
  x: T,
): string | number {
  return x ?? 0;
}

// No value of the bound is other than null or undefined.
export function absent<T extends null | undefined>(x: T): number {
  return x ?? 0;
}

// The meet is still a `T`.
export function stillT<T extends number | null>(x: T): T | number {
  return x ?? 0;
}

// Where `typeof x === "function"` holds, `x` is a function: `T ⊓ Function`.
export function fn<T>(x: T): Function {
  if (typeof x === "function") {
    return x;
  }
  return () => {};
}

export function fnStillT<T>(x: T): T | undefined {
  if (typeof x === "function") {
    return x;
  }
  return undefined;
}

export function unknownFn(x: unknown): Function {
  if (typeof x === "function") {
    return x;
  }
  return () => {};
}
