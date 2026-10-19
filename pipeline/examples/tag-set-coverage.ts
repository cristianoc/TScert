// A set covered between several target clauses: an alias's union of a
// parameter and a literal, read at a set argument, is the parameter's labels
// beside the literal's, no one of which holds every element.
type Or<A> = A | 3;

export function widen(x: 1 | 2 | 3): Or<1 | 2> {
  return x;
}

export function elements(xs: readonly (1 | 2 | 3)[]): readonly Or<1 | 2>[] {
  return xs;
}

export function generic<T extends string>(x: T | "a" | "b", y: "a" | "b"): T | "a" | "b" {
  return y === "a" ? x : y;
}
