// Reads that are no read of `jsDoc`: a constant named `jsDoc` holding
// "parent" keys the read of `parent`.
import type { Node } from "@fixture/host";

export function parentKind(n: Node): number {
  const jsDoc = "parent";
  return n[jsDoc].kind;
}

// A node at a structural type stating members the shape keeps.
export function viewKind(n: Node): number {
  const view: { readonly kind: number } = n;
  return view.kind;
}

// `"jsDoc" in n` reads no member's value and runs no getter.
export function hasDocs(n: Node): boolean {
  return "jsDoc" in n;
}
