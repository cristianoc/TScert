export function replace(p: Promise<number>, replacement: Function): void {
  p.constructor = replacement;
}
