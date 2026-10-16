// `<T>e` is `e as T` spelled the older way: an upcast the operand meets.
export function upcast(x: number): unknown {
  const y: unknown = <unknown>x;
  return y;
}

export function literal(): readonly ["a", 1] {
  return <const>["a", 1];
}

// A top-level `;` runs nothing, as in a body.
