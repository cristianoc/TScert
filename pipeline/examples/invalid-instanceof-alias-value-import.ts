// `instanceof` of a local constant holding an imported class: the constant
// is a value, not the import binding the rule reads.
import { IoFailure } from "@fixture/failures";

const Failure = IoFailure;
export function aliased(x: unknown): boolean {
  return x instanceof Failure;
}
