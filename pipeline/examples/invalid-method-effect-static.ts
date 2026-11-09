// A static method stating the empty footprint whose body pops the array it
// is handed: its binding's annotation states the statement, which its code
// is checked at (run under Node: a hole).
export class Units {
  static take(xs: number[], x: number): Modifies<{}, number> {
    xs.pop();
    return x;
  }
}

export function wrong(xs: number[]): number[] {
  const r: number[] = xs.map((x) => Units.take(xs, x));
  return r;
}
