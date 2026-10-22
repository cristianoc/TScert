// A program record's optional member tested and read past a call: no
// program object meets a type stating a stable key, whatever its members'
// spelling, so the call may remove the member, and the read past it is of
// the declared type (HOST-FAMILIES.md, "Stable keys"). Under Node, a call
// deleting the member makes the read return `undefined`.
import type * as ts from "typescript/unstable/ast";

type Holder = { readonly initializer?: ts.Expression };

export function initializerOf(d: Holder, log: () => void): ts.Expression {
  if (!d.initializer) throw new Error("no initializer");
  log();
  return d.initializer;
}
