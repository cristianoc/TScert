// Imported recursive Json: a nested value, and a dictionary read at a string
// key known only at run time, which may find a member every object inherits
// from `Object.prototype` and is refused.
import type { Json, JsonObject } from "@fixture/collections";

export function nest(value: Json): Json {
  return { child: [value, null] };
}

export function lookup(
  object: JsonObject,
  key: string,
): Json | null | undefined {
  return object[key];
}
