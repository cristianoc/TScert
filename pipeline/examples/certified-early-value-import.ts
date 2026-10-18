// An imported function of a certified module whose body has an early
// binding: its unit lowers the binding's cell and checked accesses in the
// module's run, with the intrinsic its module lists.
import { count } from "@fixture/early";

export function big(xs: readonly number[]): number {
  return count(xs);
}
