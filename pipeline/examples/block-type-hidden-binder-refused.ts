// `Many` closes over `hidden`'s `T`, which the closure's own `T` hides where
// the closure names `Many`: no binder there denotes the outer `T`.
function hidden<T>(value: T): number {
  type Many = T[];
  const count = <T>(items: Many, other: T): number =>
    items.length + (other === other ? 0 : 1);
  return count([value], 0);
}
