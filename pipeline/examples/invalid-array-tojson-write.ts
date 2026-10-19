// An array cannot acquire `toJSON` by a write, which would make a later
// `JSON.stringify` of it call the hook. `pipeline/test.mts` checks the claims
// and evidence of a weakened program, whose `Hooked` is a record with a
// writable `toJSON`, against this one: the write is refused there.
type Hooked = number[] & { toJSON?: () => undefined };
export function hook(xs: Hooked, f: () => undefined): void {
  xs.toJSON = f;
}
