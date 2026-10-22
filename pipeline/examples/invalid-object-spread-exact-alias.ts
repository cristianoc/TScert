// A closure's returned literal owns exactly its keys when it is allocated,
// but an alias at a writable dictionary may add one, which a later copy
// takes (run under Node: `label()` is 1).
export function label(): string {
  const mk = () => ({ a: 1 });
  const o = mk();
  const d: Record<string, number> = o;
  d["name"] = 1;
  const c = { name: "x", ...o };
  return c.name;
}
