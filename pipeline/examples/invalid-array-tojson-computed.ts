// Nor by a write at a computed key spelling `toJSON`.
export function hook(
  xs: number[] & { toJSON?: () => undefined },
  f: () => undefined,
): void {
  xs["toJSON"] = f;
}
