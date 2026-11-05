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
