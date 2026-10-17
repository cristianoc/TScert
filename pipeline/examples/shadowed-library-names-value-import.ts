// Names the gate lowers specially are recognised by what TypeScript binds
// them to, not by spelling: `Object.assign` through a namespace named
// `Object` is the export `assign`, and `lib.call` the export `call`, each a
// call of the binding at its declared type.
import * as Object from "@fixture/lib";
import * as lib from "@fixture/lib";

export function assigned(): string {
  return Object.assign(1);
}

export function called(): number {
  return lib.call(1);
}
