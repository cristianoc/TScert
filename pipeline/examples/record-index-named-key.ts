// A key whose type is a declared union of literals reads, per literal, the
// member it names: the key read from an array and narrowed, an alias of the
// union, and a union mixing a declared part with a literal.
type Role = "text" | "code" | "plain";
type Shown = Role;
type Wider = Role | "extra";

const CLASS: { [R in Role]: string } = {
  text: "m-text",
  code: "m-code",
  plain: "",
};

export function classOf(roles: Role[], i: number): string {
  const r = roles[i] ?? "plain";
  return CLASS[r];
}

export function narrowed(roles: readonly Shown[], i: number): string {
  const r = roles[i];
  return r === undefined ? "" : CLASS[r];
}

export function wider(key: Wider, table: { [K in Wider]: number }): number {
  return table[key];
}
