// `Object.assign` of a source typed `unknown`, which admits a host object:
// refused.
export function copy(o: unknown): object {
  return Object.assign({}, o);
}
