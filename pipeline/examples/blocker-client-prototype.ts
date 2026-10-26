// A client of the compiler channel's boundary module, tools/client-prototype.mts,
// shaped like compiler-channel.mts#privateClient and #guard: it checks an
// API's private client for its request methods and wraps every request,
// through the boundary alone. It holds neither the client, its prototype, a
// method nor a request's answer, and its `around` returns nothing: the
// boundary returns each answer itself.
import type { API } from "typescript/unstable/sync";
import { clientHasMethod, guardClientRequests, requestMembers } from "../../tools/client-prototype.mts";

/** A request's failure, naming the request. */
class RequestFailure extends Error {
  readonly request: string;
  constructor(request: string) {
    super(`request ${request} failed`);
    this.request = request;
  }
}

export function hasRequests(api: API): boolean {
  return requestMembers.every((member) => clientHasMethod(api, member));
}

export function guard(api: API): void {
  guardClientRequests(api, (member, _receiver, _args, send) => {
    try {
      send();
    } catch (error) {
      throw error instanceof RequestFailure ? error : new RequestFailure(member);
    }
  });
}
