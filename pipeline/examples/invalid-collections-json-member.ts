import type { Json } from "@fixture/collections";

// A function is not a JSON value, even inside a newly constructed dictionary.
export function invalidMember(value: Json): Json {
  return { child: (): Json => value };
}
