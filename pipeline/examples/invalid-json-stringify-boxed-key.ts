// A boxed string in a key list is converted by its `toString`, client code
// `JSON.stringify` runs (run under Node): the stated key list holds
// primitive numbers and strings.
interface Named {
  toString(): string;
}

export function keyed(x: { [k: string]: number }, key: Named): string {
  // @ts-expect-error: an object is no string
  return JSON.stringify(x, [key]);
}
