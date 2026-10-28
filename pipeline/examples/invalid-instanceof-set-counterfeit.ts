// An object made by `Object.create(Set.prototype)` passes `instanceof Set`
// without a set's internal slots: the native `has` called on it throws a
// TypeError (run under Node). The fragment makes no such object:
// `Object.create` is refused.
export function counterfeit(): boolean {
  const fake: unknown = Object.create(Set.prototype);
  return fake instanceof Set ? fake.has(1) : false;
}
