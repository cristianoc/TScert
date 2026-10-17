// Conditions of `&&` whose left operand is a string, not a Boolean: the
// condition is read for its truthiness alone, so the right operand's test
// narrows `r` in the branch it guards, in a statement and in a conditional.
// A computed read at a long union of keys is a chain of decided tests.
type Side = "a" | "b";

export function guarded(r: Side, s: string): "b" | null {
  if (s && r !== "a") return r;
  return null;
}

export function chosen(r: Side, s: string): "b" | null {
  return s && r !== "a" ? r : null;
}

type Role =
  | "code"
  | "str"
  | "intr"
  | "script"
  | "text"
  | "lit"
  | "refused"
  | "kw"
  | "op"
  | "var"
  | "con"
  | "bind"
  | "rel"
  | "plain";

export function classOf(r: Role, e: string): string {
  const names: { [K in Role]: string } = {
    code: "",
    str: "",
    intr: "m-intr",
    script: "",
    text: "m-text",
    lit: "m-lit",
    refused: "refused",
    kw: "m-kw",
    op: "m-op",
    var: "",
    con: "m-con",
    bind: "m-bind",
    rel: "m-rel",
    plain: "",
  };
  return r === "code"
    ? e
    : names[r] && r !== "text"
      ? `<span class="${names[r]}">${e}</span>`
      : e;
}
