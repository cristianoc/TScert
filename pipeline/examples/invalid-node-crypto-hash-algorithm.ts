// An algorithm the caller chooses: at "shake128" the host emits a
// deprecation warning, which reads `process.noDeprecation` during the call,
// a property other code may replace by a getter (run under Node: the getter
// runs inside `createHash`). The reviewed entry takes "sha256" alone,
// refused.
import { createHash } from "node:crypto";

export function use(algorithm: string, s: string): string {
  return createHash(algorithm).update(s).digest("hex");
}
