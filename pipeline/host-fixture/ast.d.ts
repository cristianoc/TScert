// The host package's `Node`, reduced to members that reach no node list:
// `jsDoc`, which allocates on each read, declared as the package declares it.
export interface Node {
  readonly kind: number;
  readonly parent: Node;
  readonly jsDoc?: readonly Node[] | undefined;
}
// The host package's node list, declared as the package declares it: read as
// a dense readonly array of its elements owning the contract's members.
export interface NodeArray<T extends Node> extends ReadonlyArray<T> {
  hasTrailingComma?: boolean;
  transformFlags: number;
}
export interface Block extends Node {
  readonly statements: NodeArray<Node>;
}
// The branded string, declared as the package declares it: a string where the
// client receives one, refused as a host parameter.
export type Path = string & {
    __pathBrand: any;
};
export interface SourceFile extends Node {
  readonly path: Path;
}
export declare function fileAt(path: Path): SourceFile | undefined;
// An abstract base with its brand, declared `any` as the package declares it:
// an optional member of type `unknown`.
export interface Expression extends Node {
  _expressionBrand: any;
}
// Branded strings at each direction of use.
export declare function withPath(produce: () => Path): void;
export declare function taker(): (path: Path) => void;
export declare function eachPath(visit: (path: Path) => void): void;
export interface Holder<T> {
  readonly value: T;
}
export declare function holder(): Holder<Path>;
export declare function nested(visit: (each: (path: Path) => void) => void): void;
export declare function nestedOut(visit: (each: (take: (path: Path) => void) => void) => void): void;
export declare function curried(): () => (path: Path) => void;
export declare function maybe(): Path | undefined;
export declare function optionally(path?: Path): void;
export interface Located extends Node {
  readonly alternative?: Path;
}
