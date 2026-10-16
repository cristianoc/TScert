// The same readable array constructor is used before and after substitution.
// At unknown, holes read as allowed values; at T, copying reads only T values.
function collect<T>(...values: T[]): T[] {
  return values;
}

export function copy<T>(source: readonly T[]): T[] {
  return collect<T>(...source);
}

export function fromRecord(value: {}): readonly unknown[] {
  if (Array.isArray(value)) {
    return copy<unknown>(value);
  }
  return [];
}

// An iterator and a spread consume the same read guarantee, even at a binder.
export function iterable<T>(source: readonly T[]): Iterable<T> {
  return source;
}

// Readable numbers exclude holes, so a pure map may select its dense-input contract.
export function doubled(source: readonly number[]): number[] {
  return source.map((value: number) => value * 2);
}
