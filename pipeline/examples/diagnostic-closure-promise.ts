// A failed promise inside a closure makes that closure opaque.
const predicate = (value: unknown): value is string => true;

export function usePredicate(value: unknown): boolean {
  return predicate(value);
}
