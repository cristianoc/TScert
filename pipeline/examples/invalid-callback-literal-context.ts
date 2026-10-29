// A callback's object literal fitting no arm of the expected element type is
// refused: its discriminant `"tree"` is no arm's.
type Node =
  | { kind: "leaf"; name: string }
  | { kind: "pair"; left: Node; right: Node };

export function asResult(names: readonly string[]): Node[] {
  // @ts-expect-error: "tree" is no arm's discriminant.
  return names.map((name) => ({ kind: "tree", name }));
}
