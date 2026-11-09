// An override within its base's statement: the derived class's instance
// type meets its base's members, so its method is checked at the base's
// statement, and a `map` callback calling the base's method on either is
// within the empty footprint.
export class Base {
  size(n: number): Modifies<{}, number> {
    return n;
  }
}

export class Twice extends Base {
  size(n: number): Modifies<{}, number> {
    return n * 2;
  }
}

export function sizes(b: Base, xs: number[]): number[] {
  const r: number[] = xs.map((x) => b.size(x));
  return r;
}

export function twice(xs: number[]): number[] {
  return sizes(new Twice(), xs);
}
