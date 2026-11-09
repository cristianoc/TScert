// An override whose body pops the array it is handed, beyond its base's
// statement of the empty footprint: the derived class's instance type meets
// the base's members, so the override is checked at the base's statement
// (run under Node: a `Drain` passed as a `Base` leaves a hole).
export class Base {
  take(xs: number[], x: number): Modifies<{}, number> {
    return x;
  }
}

export class Drain extends Base {
  take(xs: number[], x: number): number {
    xs.pop();
    return x;
  }
}

export function wrong(b: Base, xs: number[]): number[] {
  const r: number[] = xs.map((x) => b.take(xs, x));
  return r;
}
