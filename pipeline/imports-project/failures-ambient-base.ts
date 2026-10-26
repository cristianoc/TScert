// A class whose base an ambient module declares, with no body TypeScript
// checks (`invalid-instanceof-ambient-base-value-import`).
import { Declared } from "@fixture/failures-ambient";

export class OnDeclared extends Declared {
  readonly on: number = 1;
}
