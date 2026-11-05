// A spread of a value typed `{}`, which admits a host object: refused.
export function copy(o: {}): object {
  return { ...o };
}
