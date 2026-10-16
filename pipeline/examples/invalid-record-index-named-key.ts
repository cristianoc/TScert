// An element read past the end is `undefined`, which names no member of the
// record: TypeScript types `CLASS[roles[i]]` a string, and it is `undefined`
// for `classOf([], 0)`.
type Role = "text" | "code";

const CLASS: { [R in Role]: string } = { text: "m-text", code: "m-code" };

export function classOf(roles: Role[], i: number): string {
  return CLASS[roles[i]];
}
