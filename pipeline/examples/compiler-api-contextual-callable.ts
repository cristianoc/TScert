import type { TypeNode, TypeReferenceNode } from "typescript/unstable/ast";

// A method of an object literal its interface gives the context, whose
// parameter TypeScript types as a function type of host nodes, as
// `readTypeTerm`'s scopes read a type's parts: read as the interface
// writes it.
interface Scope {
  named(node: TypeReferenceNode, read: (node: TypeNode) => number): number;
}

function use(scope: Scope, node: TypeReferenceNode): number {
  return scope.named(node, (n) => n.pos);
}

export function run(node: TypeReferenceNode): number {
  return use(
    {
      named(reference, read) {
        return read(reference) + reference.end;
      },
    },
    node,
  );
}
