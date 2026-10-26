// `instanceof` of a class whose module writes its binding, which TypeScript
// rejects there (TS2629): after `swap()`, the import holds another class, and
// an instance made before is no longer an instance (run under Node).
import { Rebound, swap } from "@fixture/failures-rebound";

export function rebound(x: Rebound): boolean {
  swap();
  return x instanceof Rebound;
}
