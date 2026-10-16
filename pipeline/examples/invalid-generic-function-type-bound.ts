// A scheme keeps its binder's bound: `keep` meets its signature only at
// strings, so it is no function of every type. At `T := number` it returns
// a number where a string is promised.
function keep<T extends string>(x: T): string {
  return x;
}

export function unbounded(): string {
  // @ts-expect-error
  const k: <T>(x: T) => string = keep;
  return k(1);
}
