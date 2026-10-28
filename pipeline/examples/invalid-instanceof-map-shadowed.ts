// A class extending `Map` passes `instanceof Map` with its own
// `[Symbol.iterator]`, which shadows the native one: the loop calls the
// program's method, which the host's iteration does not (run under Node:
// the method ran). The fragment declares no such class: a class extending
// one of the library is refused.
let ran: number = 0;
class Shadowed extends Map<string, number> {
  [Symbol.iterator](): MapIterator<[string, number]> {
    ran++;
    return super.entries();
  }
}
export function entries(value: unknown): unknown[] {
  const found: unknown[] = [];
  if (value instanceof Map) for (const entry of value) found.push(entry);
  return found;
}
export function shadowed(): number {
  entries(new Shadowed());
  return ran;
}
