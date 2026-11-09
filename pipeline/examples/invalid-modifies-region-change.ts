// A store region stated at a change other than `"any"`: a region's store and
// cells may change arbitrarily, so a narrower change is refused at the reader.
export function grow(xs: number[]): Modifies<{ values: "any"; "xs[*]": "grow" }, void> {
  xs.push(1);
}
