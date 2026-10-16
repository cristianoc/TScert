// A structural alias must not grant a write to an array's constructor.
export function replace(xs: number[], replacement: Function): void {
  const alias: { constructor: Function } = xs;
  alias.constructor = replacement;
}
