// A pack parameter instantiated at a tuple of objects: `Params` is
// `[{ readonly value: number }]`, which the constructor takes at the same level.
import { objectMaker, ObjectBox } from "@fixture/lib";
export function build(): number {
  return objectMaker.make(ObjectBox, { value: 1 }).v.value;
}
