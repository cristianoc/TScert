// A symbol table is keyed by escaped names: a member named `__x` is at
// `___x`, so `get` at its display name finds nothing, and its
// `Symbol | undefined` is not ruled out by `!` (run under Node).
import type { Symbol } from "typescript/unstable/sync";

export function wrong(owner: Symbol, member: Symbol): Symbol {
  return owner.getMembers().get(member.name)!;
}
