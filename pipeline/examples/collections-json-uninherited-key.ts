// Imported recursive Json: a nested value, and a dictionary read at a number
// key, under which no member of `Object.prototype` is.
import type { Json, JsonObject } from "@fixture/collections";

export function nest(value: Json): Json {
  return { child: [value, null] };
}

export function lookup(
  object: JsonObject,
  key: number,
): Json | null | undefined {
  return object[key];
}
