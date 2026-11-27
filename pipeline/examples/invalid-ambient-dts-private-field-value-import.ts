// An untyped field of an imported `.d.ts` class is readonly `unknown`, not
// the `any` TypeScript reads it at: assigning it to `string` is refused.
import type { ServiceInstance } from "@fixture/ambient-private";

export function badRead(s: ServiceInstance): string {
  const x: string = s.pub;
  return x;
}
