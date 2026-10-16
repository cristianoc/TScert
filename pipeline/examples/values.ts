function identity(value: boolean): boolean {
  const snapshot = value;
  return snapshot;
}
function mutable(seed: boolean): boolean | null {
  let value: boolean | null = seed;
  const snapshot = value;
  value = null;
  return snapshot;
}
