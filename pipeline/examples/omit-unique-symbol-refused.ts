// Omit of an interface with a unique-symbol key keeps that key, and Pick
// over it is refused.
declare const tag: unique symbol;
interface Tagged {
  [tag]: number;
  name: string;
}
export function name(t: Omit<Tagged, "name">): number {
  return 0;
}
