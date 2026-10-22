// A closure's literal with a getter: the spread copies the getter's value
// under its key, over the written one (run under Node: `label()` is 1).
export function label(): string {
  const extra = () => ({
    get name(): number {
      return 1;
    },
  });
  const o = { name: "x", ...extra() };
  return o.name;
}
