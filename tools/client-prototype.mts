/* Part of the trusted front end: the compiler channel's (`compiler-channel.mts`)
 * access to the class prototype of an `API`'s private client, `Client` in the
 * pinned package's `dist/api/sync/client.js`, whose request methods are own
 * data properties of that prototype, and the memo of a snapshot's answers.
 * This module holds the front end's only use of `Object.getPrototypeOf`,
 * which TScert refuses (SOURCE-CONTRACTS.md, "`Object` and `Reflect`"): it is
 * a host boundary, whose callers rely on its signatures and the contract
 * below, audited against the package (SOURCE-REWRITES.md, "The compiler
 * client's prototype").
 *
 * Each function takes the `API` itself, a compiler API value only the package
 * makes, so the only prototype it reaches is that client's class prototype.
 * Neither hands its caller the client, the prototype, a method or a way to
 * answer a request: every answer a wrapped request returns is the
 * compiler's, or, for a query of a snapshot asked again, its earlier answer
 * read back from JSON text, which assumes the compiler answers a held
 * snapshot's query the same each time (query omission, a conjecture). */
import type { API } from "typescript/unstable/sync";
import { sharing } from "./files.mts";
import { fieldOf } from "./thrown.mts";

/** The client's members that send a request on its channel: every one of
 * them, the API's requests through the first two, and an echo and the
 * timing queries through the others. */
export type RequestMember = "apiRequest" | "apiRequestBinary" | "echo" | "echoBinary" | "getTimingInfo" | "resetTimingInfo";
export const requestMembers: readonly RequestMember[] =
  ["apiRequest", "apiRequestBinary", "echo", "echoBinary", "getTimingInfo", "resetTimingInfo"];

/** A method of the client, called with a client as its receiver. */
type Method = (this: unknown, ...args: unknown[]) => unknown;
const isMethod = (f: unknown): f is Method => typeof f === "function";

/** `api`'s private client, or `undefined`. */
const clientOf = (api: API): unknown => fieldOf(api, "client");
/** The class prototype of `api`'s private client, or `null`. */
const clientPrototype = (api: API): object | null => {
  const client = clientOf(api);
  const prototype: unknown = client && typeof client === "object" ? Object.getPrototypeOf(client) : null;
  return prototype && typeof prototype === "object" ? prototype : null;
};

/** Whether `member` of the class prototype of `api`'s private client is a
 * function, read as an own data property: no accessor runs, and nothing is
 * written. */
export function clientHasMethod(api: API, member: RequestMember): boolean {
  const prototype = clientPrototype(api);
  return prototype !== null && isMethod(fieldOf(prototype, member));
}

/** The queries of a snapshot the front end asks (docs/STAGE-STORE.md, "Shared
 * work"): each a read of the snapshot its parameters name, which the compiler
 * holds unchanged until its release. A request off the list (a snapshot's
 * update or release, the client's initialization, a configuration's parse,
 * a profile) goes to the compiler every time. */
const snapshotQueries: ReadonlySet<string> = new Set([
  "getAliasedSymbol", "getAliasSymbolOfType", "getConstantValue", "getContextualType", "getDefaultProjectForFile",
  "getExportsOfModule", "getExportsOfSymbol", "getImmediateAliasedSymbol", "getIndexInfosOfType", "getMembersOfSymbol",
  "getNonNullableType", "getParameterType", "getParametersOfSignature", "getProgramDiagnostics", "getPropertiesOfType",
  "getPropertyOfType", "getResolvedSignature", "getReturnTypeOfSignature", "getSemanticDiagnostics",
  "getShorthandAssignmentValueSymbol", "getSignaturesOfType", "getSourceFileMetadata", "getSourceFileNames",
  "getSymbolAtLocation", "getSymbolOfType", "getSymbolsAtLocations", "getSyntacticDiagnostics", "getTargetOfType",
  "getThisParameterOfSignature", "getTypeArguments", "getTypeAtLocation", "getTypeFromTypeNode", "getTypeOfSymbol",
  "getTypeParametersOfSignature", "getTypePredicateOfSignature", "getTypesOfType", "getWellKnownSymbols", "isArrayType",
  "isTupleType", "resolveName", "typeToString",
]);
/** Each client's answers to the queries of each snapshot it holds, as text
 * by method and parameters: a query asked again of the same snapshot is
 * answered as it was first (query omission, a conjecture), and a snapshot's
 * answers go with its release. */
const answers = new WeakMap<object, Map<unknown, Map<string, string>>>();
/** How many queries of a snapshot were made in this process, and how many of
 * them its earlier answer served, for the controls. */
const queries: { asked: number; served: number } = { asked: 0, served: 0 };
export const queryTelemetry = (): { asked: number; served: number } => ({ ...queries });
/** How many snapshots of a compiler hold kept answers, for the controls. */
export function heldSnapshots(api: API): number {
  const client = clientOf(api);
  return client && typeof client === "object" ? answers.get(client)?.size ?? 0 : 0;
}
function query(client: object, method: unknown, params: unknown, request: () => unknown): unknown {
  const snapshot = fieldOf(params, "snapshot");
  if (typeof method !== "string" || snapshot === undefined) return request();
  let held = answers.get(client);
  if (!held) answers.set(client, held = new Map());
  if (method === "release") {
    held.delete(snapshot);
    return request();
  }
  if (!snapshotQueries.has(method) || !sharing()) return request();
  queries.asked++;
  const key = `${method}\0${JSON.stringify(params)}`;
  const known = held.get(snapshot)?.get(key);
  if (known !== undefined) {
    queries.served++;
    return known === "" ? undefined : JSON.parse(known);
  }
  const value = request();
  let byKey = held.get(snapshot);
  if (!byKey) held.set(snapshot, byKey = new Map());
  byKey.set(key, JSON.stringify(value) ?? "");
  return value;
}

/** The prototypes whose request methods are wrapped. */
const wrapped = new WeakSet<object>();
/** Replaces each request member of the class prototype of `api`'s private
 * client, once per prototype, by a method that calls
 * `around(member, receiver, args, send)` and returns the request's answer.
 * `send` sends the request, the original method on that receiver with
 * those arguments, through the memo for `apiRequest`; it may be called
 * once, while `around` runs, and its answer is the method's result. A
 * method whose `around` returns without sending throws, and one whose
 * request failed throws that failure though `around` returned. The first call of a
 * process wraps every client of the class; a later one changes nothing. A
 * member that is no function throws before any is written. It writes those
 * members of that prototype alone. */
export function guardClientRequests(api: API,
    around: (member: RequestMember, receiver: unknown, args: readonly unknown[], send: () => void) => void): void {
  const prototype = clientPrototype(api);
  if (prototype === null || wrapped.has(prototype)) return;
  const methods = requestMembers.map((member): [string, Method] => {
    const original = fieldOf(prototype, member);
    if (!isMethod(original))
      throw Error(`the compiler package's private shape changed: API.client.${member} (client-prototype.mts)`);
    return [member, function (this: unknown, ...args: unknown[]): unknown {
      const call: { open: boolean; sent: boolean; answer: unknown; failure: { error: unknown } | null } =
        { open: true, sent: false, answer: undefined, failure: null };
      const request = (): unknown => original.call(this, ...args);
      const send = (): void => {
        if (!call.open || call.sent) throw Error(`API.client.${member} sent outside its call, or twice (client-prototype.mts)`);
        call.sent = true;
        try {
          call.answer = member === "apiRequest" && this && typeof this === "object" ? query(this, args[0], args[1], request) : request();
        } catch (error) {
          call.failure = { error };
          throw error;
        }
      };
      try {
        around(member, this, args, send);
      } finally {
        call.open = false;
      }
      if (!call.sent) throw Error(`API.client.${member} returned without its request (client-prototype.mts)`);
      // A request that failed fails its method, though `around` returned.
      if (call.failure) throw call.failure.error;
      return call.answer;
    }];
  });
  Object.assign(prototype, Object.fromEntries(methods));
  wrapped.add(prototype);
}
