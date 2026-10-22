// A program's look-alike of a node declaration, its optional member tested
// and read past a call: a look-alike has no family marker, so it states no
// stable key (HOST-FAMILIES.md, "Activation"), the call may remove the
// member, and the read past it is of the declared type. Under Node, a call
// deleting the member makes the read return `undefined`.
interface VariableDeclaration {
  readonly kind: number;
  readonly initializer?: { readonly kind: number };
}

export function initializerOf(
  d: VariableDeclaration,
  log: () => void,
): { readonly kind: number } {
  if (!d.initializer) throw new Error("no initializer");
  log();
  return d.initializer;
}
