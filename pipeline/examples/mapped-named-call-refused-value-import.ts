// An imported function whose declaration takes `Partial` of an interface
// with a call signature: TypeScript maps only its members and drops the
// signature, a reading the declaration reader refuses once the graph is
// complete.
import { tick } from "@fixture/hooks-ambient-callable";

export function ticks(): number {
  return tick({ count: 1 });
}
