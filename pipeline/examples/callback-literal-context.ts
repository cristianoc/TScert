// A callback's object literal is built at the arm of the call's expected
// element type it fits: `map`'s binder `U` is the element the expected
// result names, so the literal keeps its discriminant `"leaf"`, whether the
// expected type is a field's, the enclosing function's result, or a generic
// function's own result.
type Node =
  | { kind: "leaf"; name: string }
  | { kind: "pair"; left: Node; right: Node };

function build<U>(f: (n: number) => U): U[] {
  return [f(0), f(1)];
}

export function asField(): { parts: Node[] } {
  return { parts: ["a", "b"].map((name) => ({ kind: "leaf", name })) };
}

export function asResult(names: readonly string[]): Node[] {
  return names.map((name) => ({ kind: "leaf", name }));
}

export function asGeneric(): Node[] {
  return build((n) => ({ kind: "leaf", name: String(n) }));
}
