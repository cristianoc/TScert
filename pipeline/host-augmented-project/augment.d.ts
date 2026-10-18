// A project's augmentations of host types: a member merged into the sync
// API's Checker and one into a node type. The installation's declarations
// are those types' whole shapes, so each is refused where it is reached.
import type * as ts from "typescript/unstable/ast";

declare module "typescript/unstable/sync" {
  interface Checker {
    extra(node: ts.Node): number;
  }
}

declare module "typescript/unstable/ast" {
  interface SourceFile {
    extra: number;
  }
}
