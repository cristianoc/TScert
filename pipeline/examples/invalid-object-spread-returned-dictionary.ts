// A closure returning a dictionary it filled, not a literal: the dictionary
// may own `name`, which the copy takes (run under Node: `label()` is 1).
export function label(): string {
  const extra = () => {
    const d: Record<string, number> = {};
    d["name"] = 1;
    return d;
  };
  const o = { name: "x", ...extra() };
  return o.name;
}
