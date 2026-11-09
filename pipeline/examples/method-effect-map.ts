// A class method stating its effect, `{value: any, store: grow}`: it pushes
// onto a field. A `map` callback calling it is within that footprint, which
// keeps every dense prefix, so the result is dense; the instance type's
// member states it, and the method's code is certified at it.
export class Log {
  entries: number[] = [];
  note(n: number): Modifies<{ values: "any"; stores: "grow" }, number> {
    this.entries.push(n);
    return n + 1;
  }
}

export function notes(log: Log, xs: number[]): number[] {
  const r: number[] = xs.map((x) => log.note(x));
  return r;
}
