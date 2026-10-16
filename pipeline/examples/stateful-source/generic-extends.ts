/**
 * T extends boolean is T ≤ boolean. Returning x at boolean is transport
 * along that inclusion; returning true as T is not.
 */
function asBoolean<T extends boolean>(x: T): boolean {
  return x;
}

function idBounded<T extends boolean>(x: T): T {
  return x;
}
