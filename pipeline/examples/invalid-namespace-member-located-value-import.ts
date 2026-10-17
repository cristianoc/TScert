// A refusal of a namespace member is located at its use: `lib.madeProperty`
// is a constant whose type TypeScript infers from its code, which no
// annotation states, refused where the second function reads it.
import * as lib from "@fixture/lib";

export function fine(): number {
  return lib.limit;
}

export function made(): unknown {
  return lib.madeProperty;
}
