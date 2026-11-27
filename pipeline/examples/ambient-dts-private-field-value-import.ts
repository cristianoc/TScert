// An external `.d.ts` class with an unannotated `private` field (as `tsc`
// emits for private parameter properties) and an untyped field is admitted:
// its untyped instance fields are readonly `unknown`, never inferred from code.
import type { ServiceInstance } from "@fixture/ambient-private";

export function serviceName(s: ServiceInstance): string {
  return s.getName();
}

export function readUntyped(s: ServiceInstance): unknown {
  return s.pub;
}
