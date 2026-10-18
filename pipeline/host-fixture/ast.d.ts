// The host package's `Node`, reduced to members that reach no node list:
// `jsDoc`, which allocates on each read, declared as the package declares it.
export interface Node {
  readonly kind: number;
  readonly parent: Node;
  readonly jsDoc?: readonly Node[] | undefined;
}
