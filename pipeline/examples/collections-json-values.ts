// Boolean, number, string, array and object values passed to a consumer of
// the imported Json.
import type { Json } from "@fixture/collections";

export function values(): Json {
  const accept = (value: Json): Json => value;
  const flag = accept(true);
  const count = accept(42);
  const label = accept("ready");
  const list = accept([flag, count, label, null]);
  return accept({ flag: flag, count: count, label: label, list: list });
}
