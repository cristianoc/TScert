// Iterable construction can execute client code; the empty constructor contract refuses it.
export function wrong(
  entries: Iterable<readonly [object, number]>,
): WeakMap<object, number> {
  return new WeakMap<object, number>(entries);
}
