// Census functions: fragment-statements.mts#switchStmt,#statements.
// A `reduce` callback pushing onto an array it captures, inside a `map`
// callback: `reduce` with an initial value reads the receiver and calls its
// callback, so it is within the callback's footprint,
// `{value: any, store: grow}`, as the `map` callback is, which keeps the
// mapped array's dense prefixes, and the result is dense. The write shows:
// `kept` holds every word afterwards.
export function lengths(lines: string[], kept: string[]): number[] {
  return lines.map((l) =>
    l.split(" ").reduce((total, w) => {
      kept.push(w);
      return total + w.length;
    }, 0),
  );
}
