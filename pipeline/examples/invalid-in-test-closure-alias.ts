// A write through an alias between the test and the read: `a` may be `p`'s
// object, typed with `name` optional, and write `undefined` there. Under Node,
// `name([o], [o])` with `o = { name: "x" }` returns `[undefined]`.
type Part = { name: string } | { spread: number };
export function name(parts: Part[], aliases: { name?: string }[]): string[] {
  return parts.map((p) => {
    if ("spread" in p) return "s";
    for (const a of aliases) a.name = undefined;
    return p.name;
  });
}
