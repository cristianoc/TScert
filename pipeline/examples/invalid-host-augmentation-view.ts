// A member a project's augmentation merges into a host class: the
// installation's declarations, through the named view, are its whole shape
// (reading rule 4).
import type * as ts from "typescript/unstable/ast";
import type { Checker } from "typescript/unstable/sync";

export function use(checker: Checker, n: ts.Node): number {
  return checker.extra(n);
}
