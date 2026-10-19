// An array cannot acquire `toJSON` by a write, which would make a later
// `JSON.stringify` of it call the hook.
export function hook(
  xs: number[] & { toJSON?: () => undefined },
  f: () => undefined,
): void {
  xs.toJSON = f;
}
