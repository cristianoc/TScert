// An array cannot acquire `toJSON` through a structural view of it.
// `pipeline/test.mts` checks the claims and evidence of a weakened program,
// whose `Hooked` and `View` are records with a writable `toJSON`, against
// this one: the write through the view is refused there.
type Hooked = number[] & { toJSON?: () => undefined };
type View = { toJSON?: () => undefined };
export function viewed(xs: Hooked, f: () => undefined): void {
  const alias: View = xs;
  alias.toJSON = f;
}
