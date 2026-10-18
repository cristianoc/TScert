// A `let` holding an arrow may be reassigned to a function of another type:
// its initializer states no type for it, and it is refused.
import { swapped } from "@fixture/lib";

export function call(): number {
  return swapped(1);
}
