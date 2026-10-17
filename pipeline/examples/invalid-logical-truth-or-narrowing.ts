// `s || r !== "a"` holds where `s` is truthy whatever `r` is: the branch it
// guards may see `r` at "a", so `r` is no "b" there.
type Side = "a" | "b";

export function chosen(r: Side, s: string): "b" | null {
  // @ts-expect-error: `r` may be "a" where `s` is truthy
  return s || r !== "a" ? r : null;
}
