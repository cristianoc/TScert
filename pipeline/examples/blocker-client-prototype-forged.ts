// A forged API handed to the boundary: an object whose `client` is an
// array, so the boundary's prototype would be `Array.prototype` and its
// wrappers would land on it. Refused: `unknown` is no API, whose private
// members no ordinary object has.
import type { API } from "typescript/unstable/sync";
import { guardClientRequests } from "../../tools/client-prototype.mts";

export function forge(): void {
  const fake = { client: [] } as unknown as API;
  guardClientRequests(fake, (_member, _receiver, _args, send) => send());
}
