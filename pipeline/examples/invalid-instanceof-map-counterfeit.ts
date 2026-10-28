// An object made by `Object.create(Map.prototype)` passes `instanceof Map`
// without a map's internal slots: the native `get` called on it throws a
// TypeError (run under Node). The fragment makes no such object:
// `Object.create` is refused.
export function counterfeit(): unknown {
  const fake: unknown = Object.create(Map.prototype);
  return fake instanceof Map ? fake.get("k") : undefined;
}
