// A structural alias must not grant a write to an array's `toJSON`.
export function hook(xs: number[], f: () => undefined): void {
  const alias: { length: number; toJSON?: () => undefined } = xs;
  alias.toJSON = f;
}
