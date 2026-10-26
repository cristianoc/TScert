// `instanceof` of a class whose module writes its binding under a comment
// suppressing TypeScript's error: after `swap()`, the import holds another
// class, and an instance made before is no longer an instance (run under
// Node).
import { Suppressed, swap } from "@fixture/failures-suppressed";

export function suppressed(x: Suppressed): boolean {
  swap();
  return x instanceof Suppressed;
}
