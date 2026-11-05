// A function is no imported Json: it does not instantiate `T extends Json`.
import type { Json } from "@fixture/collections";

export function invalidBound(): Json {
  const accept = <T extends Json>(value: T): Json => value;
  return accept((): boolean => true);
}
