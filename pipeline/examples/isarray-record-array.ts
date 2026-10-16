// A record or dictionary type is of objects meeting the built-in array
// invariant: one owning an array's store holds `Array.prototype` and owns
// no key it provides. Array.isArray does not establish density, but every
// in-bounds read, including a hole's undefined, meets readonly unknown[].
type Foo = { a: string; b: number };

export function elements(x: number[] | Foo): readonly unknown[] {
  if (Array.isArray(x)) return x;
  return [];
}

export function length(x: number[] | Foo): number {
  if (Array.isArray(x)) {
    return x.length;
  }
  return 0;
}

export function dictionary(
  x: { [k: string]: number } | string,
): readonly unknown[] {
  if (typeof x === "string") return [];
  if (!Array.isArray(x)) return [];
  return x;
}
