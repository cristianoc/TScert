// Census functions: client-prototype.mts#clientHasMethod, #guardClientRequests.
// The compiler client's prototype is inspected through its audited boundary.
// The safe, unsupported Error-prototype form is in SOURCE-REWRITES.md,
// "The compiler client's prototype".
import type { API } from "typescript/unstable/sync";
import { clientHasMethod } from "../../tools/client-prototype.mts";
export function hasRequest(api: API): boolean {
  return clientHasMethod(api, "apiRequest");
}
