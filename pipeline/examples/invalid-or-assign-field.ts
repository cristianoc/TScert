// `||=` on a field keeps a truthy value: its value is the field's truthy
// part or the right side's (run under Node: a field holding 2 gives 2).
export function pick(o: { n: number }): 1 {
  // @ts-expect-error a number is not 1
  return (o.n ||= 1);
}
