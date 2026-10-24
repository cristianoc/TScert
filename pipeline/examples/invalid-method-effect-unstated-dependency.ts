// A method stating the empty footprint whose body calls a method field
// stating no effect: a value of the class may hold any function in that
// field, so the call is unrestricted and the statement is not met over the
// method's whole domain (run under Node: a `Runner` whose `helper` pops the
// mapped array leaves a hole).
export function helper(xs: number[], x: number): number {
  return x;
}

export class Runner {
  helper: typeof helper = helper;
  run(
    xs: number[],
    x: number,
  ): Within<{ value: "keep"; store: "keep" }, number> {
    return this.helper(xs, x);
  }
}

export function wrong(r: Runner, xs: number[]): number[] {
  const out: number[] = xs.map((x) => r.run(xs, x));
  return out;
}
