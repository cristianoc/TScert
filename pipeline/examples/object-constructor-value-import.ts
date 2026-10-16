// An imported constructor consumes an object and returns a nested object field.
import { ObjectBox } from "@fixture/lib";
export function constructObject(): number {
  return new ObjectBox({ value: 1 }).v.value;
}
