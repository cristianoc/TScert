export function replace(p: Promise<number>): void {
  const alias: { constructor: unknown } = p;
  alias.constructor = undefined;
}
