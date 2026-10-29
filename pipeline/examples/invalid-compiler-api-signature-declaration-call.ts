// A resolved signature's `declaration` is an ordinary data field the
// package's client shares per signature: a test that it is present holds
// only until a call, which may reassign it through another alias (run
// under Node).
import type { NodeHandle, Signature } from "typescript/unstable/sync";

export function wrong(
  signature: Signature,
  otherwise: NodeHandle,
  log: () => void,
): NodeHandle {
  if (signature.declaration === undefined) return otherwise;
  log();
  return signature.declaration;
}
