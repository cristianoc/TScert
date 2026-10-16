import type { Json, JsonObject } from "@fixture/collections";

// A string index signature does not establish that a runtime key is present.
export function missingKey(object: JsonObject, key: number): Json | null {
  return object[key];
}
