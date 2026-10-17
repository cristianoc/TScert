// A function declaration writing a field of its parameter: its signature
// states no heap preservation, so the `map` callback calling it does not,
// `map` takes its unrestricted overload, and the result is sparse. The write
// shows: the counter holds the number of calls afterwards.
function bump(counter: { n: number }, t: string): string {
  counter.n = counter.n + 1;
  return t;
}

export function counted(ts: string[], counter: { n: number }): string[] {
  return ts.map((t) => bump(counter, t));
}
