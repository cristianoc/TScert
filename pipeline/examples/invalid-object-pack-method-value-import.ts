// An object actual must meet its position's object contract: a string field
// is no number.
import { objectMaker, ObjectBox } from "@fixture/lib";
export function build(): number {
  // @ts-expect-error: a string value is no number
  return objectMaker.make(ObjectBox, { value: "a" }).v.value;
}
