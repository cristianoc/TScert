// An imported function with overloads is callable at each of them, never at
// its implementation's signature.
import { either } from "@fixture/lib";
export function text(): string {
  return either("a");
}
export function count(): number {
  return either(1);
}
