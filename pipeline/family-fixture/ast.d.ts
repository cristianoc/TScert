// A stand-in host package with a tagged family whose root declares an
// optional method, which no audited package does: pipeline/test.mts activates
// it under a description of its own, which names its installation and
// digest. Each shape inherits `text` required and `describe` optional.
export declare enum SyntaxKind {
  First = 0,
  Second = 1,
}
export interface ReadonlyTextRange {
  readonly pos: number;
  readonly end: number;
}
export interface Node extends ReadonlyTextRange {
  readonly kind: SyntaxKind;
  describe?(): string;
  text(): string;
}
export interface First extends Node {
  readonly kind: SyntaxKind.First;
}
export interface Second extends Node {
  readonly kind: SyntaxKind.Second;
}
