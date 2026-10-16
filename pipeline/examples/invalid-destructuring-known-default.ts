export function reachableDefault(x: { f?: number }): number {
  const { f = false } = x;
  return f;
}
