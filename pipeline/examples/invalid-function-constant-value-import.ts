// A constant holding a function literal without a result annotation states
// no type: its use is refused at the parser's gate.
import { unstated } from "@fixture/lib";

export function use(): number {
  return unstated(1);
}
