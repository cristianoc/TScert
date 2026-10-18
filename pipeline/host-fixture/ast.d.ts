// The host package's `Node`, reduced to members that reach no node list:
// `jsDoc`, which allocates on each read, declared as the package declares it.
export interface Node {
  readonly kind: number;
  readonly parent: Node;
  readonly jsDoc?: readonly Node[] | undefined;
}
// The host package's node list, declared as the package declares it: read as
// a dense readonly array of its elements, its heritage and members unread.
export interface NodeArray<T extends Node> extends ReadonlyArray<T> {
  hasTrailingComma?: boolean;
  transformFlags: number;
}
export interface Block extends Node {
  readonly statements: NodeArray<Node>;
}
