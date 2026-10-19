/* Part of the trusted front end: the compiler's synchronous API, opened and
 * released in one place, and the one place that reads the pinned package's
 * private shape (typescript 7.0.2, `dist/api/sync/client.js`): an `API`'s
 * `client`, whose members `requestMembers` lists carry every request to the
 * compiler process, whose `close` ends that process without a request,
 * and whose `channel.child` is the process. A package that renames one of
 * them fails here, by name (`tests/tool-failures.mts` opens one).
 *
 * Every request's failure, whatever it raised (a reply the compiler sent as
 * an error, a panic, a transport or native I/O failure, a stack exhaustion
 * before or after the request was written), is thrown as a `CompilerFailure`,
 * so a catch elsewhere cannot read it as a refusal (`toolFailureOf`). */
import { API } from "typescript/unstable/sync";
import { CompilerFailure, fieldOf, messageOf, toolFailureOf } from "./thrown.mts";

/** The compiler process, as the client's channel holds it. */
interface CompilerProcess {
  readonly pid?: number;
  readonly exitCode: number | null;
  readonly signalCode: string | null;
  kill(signal: "SIGKILL"): boolean;
  once(event: "exit", listener: () => void): unknown;
}
/** The members of an `API`'s private client this module uses. */
interface PrivateClient {
  close(): void;
  readonly channel: { readonly child: CompilerProcess };
}
type Request = (this: unknown, ...args: unknown[]) => unknown;
const isRequest = (f: unknown): f is Request => typeof f === "function";
const isProcedure = (f: unknown): f is () => unknown => typeof f === "function";
/** A value's prototype, where its methods are own members. */
const prototypeOf = (value: object): unknown => Object.getPrototypeOf(value);

/** The client's members that send a request on its channel: every one of
 * them, the API's requests through the first two, and an echo and the
 * timing queries through the others. */
const requestMembers = ["apiRequest", "apiRequestBinary", "echo", "echoBinary", "getTimingInfo", "resetTimingInfo"] as const;

/** An `API`'s private client, its members checked by name. */
export function privateClient(api: API): PrivateClient {
  const client = fieldOf(api, "client");
  const missing = (member: string): Error =>
    Error(`the compiler package's private shape changed: API.client${member} is missing (compiler-channel.mts)`);
  if (!client || typeof client !== "object") throw missing("");
  if (!("close" in client) || !isProcedure(client.close)) throw missing(".close");
  for (const member of requestMembers)
    if (!isRequest(fieldOf(prototypeOf(client), member))) throw missing(`.${member}`);
  const child = fieldOf(fieldOf(client, "channel"), "child");
  if (!child || typeof child !== "object" || !("kill" in child) || !isProcedure(child.kill) ||
      !("once" in child) || !isProcedure(child.once) || !("exitCode" in child) || !("signalCode" in child))
    throw missing(".channel.child");
  return client as PrivateClient; // asserted: the decoder of the private client, each member it names checked above
}

/** Each request of a client prototype guarded once: what it throws becomes a
 * `CompilerFailure` naming the request. */
const guarded = new WeakSet<object>();
function guard(client: PrivateClient): void {
  const prototype = prototypeOf(client);
  if (!prototype || typeof prototype !== "object" || guarded.has(prototype)) return;
  // A request is named by its method, the first argument of the API's two;
  // the others by their member.
  const wrap = (member: string, original: unknown): Request => {
    if (!isRequest(original)) throw Error(`the compiler package's private shape changed: API.client.${member} (compiler-channel.mts)`);
    const named = member === "apiRequest" || member === "apiRequestBinary";
    return function (this: unknown, ...args: unknown[]): unknown {
      try {
        return original.call(this, ...args);
      } catch (error) {
        throw error instanceof CompilerFailure ? error : new CompilerFailure(named ? String(args[0]) : member, error);
      }
    };
  };
  Object.assign(prototype, Object.fromEntries(requestMembers.map((member) =>
    [member, wrap(member, fieldOf(prototype, member))])));
  guarded.add(prototype);
}

/** A compiler process opened through the API, its requests guarded. */
export function openCompiler(options: ConstructorParameters<typeof API>[0]): API {
  let api: API;
  try {
    api = new API(options);
  } catch (error) {
    throw new CompilerFailure("spawn", error);
  }
  guard(privateClient(api));
  return api;
}

/** The compiler process of an API, for a test that waits for its end. */
export const compilerProcess = (api: API): CompilerProcess => privateClient(api).channel.child;

/** Ends the compiler process without a request: the client closes its
 * channel's pipes and signals the process, then the process is killed,
 * which it cannot ignore. */
export function abandonCompiler(api: API): void {
  const client = privateClient(api);
  try {
    client.close();
  } finally {
    const child = client.channel.child;
    if (child.exitCode === null && child.signalCode === null) child.kill("SIGKILL");
  }
}

/** Releases a compiler after its work, or after `thrown`. Where the channel
 * is readable (no failure, a refusal, a panic the compiler replied), it is
 * closed in order: its snapshots released by request, then its process
 * ended. Where it may not be (any other tool failure), it is abandoned,
 * without a further request. A failure closing it abandons it and is
 * reported, as a tool failure, with what was in flight as context. */
export function releaseCompiler(api: API, thrown: { error: unknown } | null): void {
  const failure = thrown && toolFailureOf(thrown.error);
  if (failure && !failure.readable) {
    abandonCompiler(api);
    return;
  }
  try {
    api.close();
  } catch (error) {
    abandonCompiler(api);
    const context = thrown ? `, closing the compiler after: ${messageOf(thrown.error).split("\n")[0] ?? ""}` :
      ", closing the compiler";
    throw new CompilerFailure("close", error, context);
  }
}
