// A store region stated at a function type: a callback's statement has no
// unit whose check establishes it, so it is refused at the reader.
export function apply(xs: number[], f: (ys: number[]) => Modifies<{ values: "any"; "ys[*]": "any" }, void>): void {
  f(xs);
}
