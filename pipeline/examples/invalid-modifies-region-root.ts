// A store region rooted at a parameter with a default: its value in the body
// is not the call's where the call passes none, so the root is refused.
export function fill(xs: number[] = []): Modifies<{ values: "any"; "xs[*]": "any" }, void> {
  xs.pop();
}
