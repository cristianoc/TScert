// `instanceof` of a class expression another module's constant holds: the
// constant is a value at its declared type, which no class declaration
// binds, so nothing says which prototype it gives its instances.
import { Made } from "@fixture/failures";

export function made(x: unknown): boolean {
  return x instanceof Made;
}
