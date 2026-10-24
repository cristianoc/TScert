// A method stating the empty footprint on a throw too, whose body pops the
// array it is handed and then throws: on the throw, the heap it leaves has
// lost an element, so its code does not meet the statement (run under
// Node: the callback catching the throw leaves a hole).
export class Bump {
  bump(
    xs: number[],
  ): Within<{ value: "keep"; store: "keep"; onThrow: true }, number> {
    xs.pop();
    throw new Error("bumped");
  }
}

export function wrong(b: Bump, xs: number[]): number[] {
  const r: number[] = xs.map((x) => {
    try {
      return b.bump(xs);
    } catch {
      return x;
    }
  });
  return r;
}
