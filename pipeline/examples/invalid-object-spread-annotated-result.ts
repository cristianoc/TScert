// A closure's written result `{}` states no own-key bound: the object it
// returns may own `name`, which the spread then copies over the written
// one. TypeScript keeps the written field's type (run under Node:
// `label()` is 1).
export function label(): string {
  const extra = (): {} => ({ name: 1 });
  const o = { name: "x", ...extra() };
  return o.name;
}
