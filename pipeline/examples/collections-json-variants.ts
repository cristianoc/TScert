// A function at `T extends Json`, Json imported, called with primitive,
// array and object values.
import type { Json } from "@fixture/collections";

export function variants(): Json {
  const accept = <T extends Json>(value: T): Json => value;
  const flag = accept(true);
  const count = accept(42);
  const label = accept("ready");
  const list = accept([flag, count, label, null]);
  const object: Json = { flag: flag, count: count, label: label, list: list };
  return accept(object);
}
