// A record literal with a conditional spread, expected at a discriminated
// union, is built at the arms its literal-valued fields admit: its `k` holds
// `"alloc"`, the literal type those arms fix.
// Census functions:
// fragment-classes.mts#classBody, fragment-classes.mts#classStmt.
type E =
  | { readonly k: "id"; readonly name: string }
  | { readonly k: "alloc"; readonly fields: readonly { name: string; e: E }[]; readonly proto?: E };
export function link(name: string, proto: E | null): E {
  const l: E = { k: "alloc", fields: [{ name: "message", e: { k: "id", name } }], ...(proto ? { proto } : {}) };
  return l;
}
export function maybe(ok: boolean, name: string, proto: E | null): E | null {
  const l: E | null = ok ? { k: "alloc", fields: [{ name: "message", e: { k: "id", name } }], ...(proto ? { proto } : {}) } : null;
  return l;
}
