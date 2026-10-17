// An imported constant initialized by a literal naming nothing states its
// type by that literal: a string literal its literal type, an object literal
// of such the record TypeScript infers.
import { greeting, origin } from "@fixture/lib";

export function greeted(): "hello" {
  return greeting;
}

export function shifted(): number {
  return origin.x + origin.y + origin.label.length;
}
