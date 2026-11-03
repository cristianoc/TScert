// A function declaration writing a number field of its parameter: the
// field holds a value, so its signature states `{value: any, store: keep}`,
// which keeps the mapped array's dense prefixes, and the `map` callback
// calling it gives a dense result. The write shows: the counter holds the
// number of calls afterwards.
function bump(counter: { n: number }, t: string): string {
  counter.n = counter.n + 1;
  return t;
}

export function counted(ts: string[], counter: { n: number }): string[] {
  return ts.map((t) => bump(counter, t));
}
