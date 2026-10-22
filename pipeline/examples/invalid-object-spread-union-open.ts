// A spread of a union with an open arm: a value of `{}` may own `name`,
// which the copy takes, though the other arm is a literal. TypeScript keeps
// the written field's type (run under Node: `label({ name: 1 }, false)` is 1).
export function label(other: {}, dots: boolean): string {
  const o = { name: "x", ...(dots ? { rest: true } : other) };
  return o.name;
}
