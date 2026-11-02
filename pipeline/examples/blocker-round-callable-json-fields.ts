// Census functions: claim-text.mts#atomText,#bareAtomText,#typeText and callers.
// A malformed callable atom may lack the function field, which the printer handles.
import type { JsonObject, JsonRead } from "../../tools/calculus.mts";
function isObject(value: JsonRead): value is JsonObject {
  return typeof value === "object" && value !== null && !Array.isArray(value);
}
export function render(value: JsonRead): string {
  if (!isObject(value)) return "unavailable";
  if (value.a === "callable") return render(value.function);
  return "value";
}
