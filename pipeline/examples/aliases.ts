type Id<T> = T;
type Box<T> = { value: T };
function identityAlias<T>(value: Id<T>): Id<T> {
  return value;
}
function groundIdentity(value: Id<boolean>): boolean {
  return value;
}
function allocatedAlias(seed: boolean): boolean {
  const box: Box<boolean> = { value: seed };
  return box.value;
}
