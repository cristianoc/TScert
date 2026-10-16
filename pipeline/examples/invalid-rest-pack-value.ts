// The array a call collects is fresh: it holds the actuals and none of the
// type parameter's other members, so it is no value of that parameter.
// TypeScript infers `T := string[] & { tag: string }` from the spread of a
// tagged array, and `b.tag` is then `undefined` typed `string`.
function rest<T extends readonly string[]>(...args: T): T {
  return args;
}

function respread<T extends readonly string[]>(v: T, f: (...a: T) => T): T {
  return f(...v);
}

export function wrong(): string {
  const tagged = Object.assign(["a"], { tag: "t" });
  const b = respread(tagged, rest);
  return b.tag;
}
