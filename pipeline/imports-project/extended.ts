// A module whose function states the change `extend` on spines, which
// `stated-extend-value-import` imports: `append` pushes onto the array it is
// handed, keeping every cell at its index, and its own run certifies it.
export function append(xs: number[], x: number): Modifies<{ values: "any"; spines: "extend" }, void> {
  xs.push(x);
}
