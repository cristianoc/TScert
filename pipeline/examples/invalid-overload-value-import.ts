// An imported overloaded call's result is the result of the overload it
// matches, not the implementation's.
import { either } from "@fixture/lib";
export function wrong(): number {
  return either("a");
}
