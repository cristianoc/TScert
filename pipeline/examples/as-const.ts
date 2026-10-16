// `as const` gives its operand's literal types: a literal its own, an array
// literal the readonly tuple of its elements', an object literal readonly
// fields of theirs, a name its type; and a tuple literal passed where a
// binder bounded by a tuple is expected is built at that tuple.
declare function exact<K extends [0, 1]>(x: K): K;
declare function takeFooOrT<T>(x: "foo" | T): void;

export function tuple(): readonly [0, 1] {
  const t = [0, 1] as const;
  return t;
}
export function nested(x: number): readonly [readonly [0, 1], number] {
  return [[0, 1] as const, x] as const;
}
export function empty(): readonly [] {
  return [] as const;
}
export function record(): { readonly kind: "a"; readonly size: 2 } {
  return { kind: "a", size: 2 } as const;
}
export function literal(): "bar" {
  takeFooOrT("bar" as const);
  return "bar" as const;
}
export function inferred(): [0, 1] {
  return exact([0, 1]);
}
