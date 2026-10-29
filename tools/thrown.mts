/* What a thrown value says. Defining no language: a `catch` binds `unknown`,
 * and every tool here reports what it caught the same way, so the one reading
 * of a thrown value lives on its own rather than being asserted at each of
 * them.
 */

/** The message of what was thrown, or the value itself where it is not an
 * error. `instanceof Error` is the check that says which; a tool that reported
 * `(e as Error).message` was asserting that and would have printed `undefined`
 * for anything else thrown. */
export const messageOf = (thrown: unknown): string =>
  thrown instanceof Error ? thrown.message : String(thrown);

/** One field of what was thrown, where a caller looks for one a child process
 * attaches — `stderr`, `code`, `killed`. A thrown value is `unknown` until
 * something reads it, and this is that reading. */
export const fieldOf = (thrown: unknown, key: string): unknown =>
  !!thrown && typeof thrown === "object" && key in thrown
    ? Object.getOwnPropertyDescriptor(thrown, key)?.value
    : undefined;


/** Whether what was thrown is the engine exhausting the call stack. */
const stackExhaustion = (thrown: unknown): boolean =>
  thrown instanceof RangeError && thrown.message === "Maximum call stack size exceeded";

/** A failure of a request to the compiler: whatever its call into the
 * compiler's package threw (`compiler-channel.mts` makes every request's
 * failure one), the request's name, and whether the channel's later replies
 * stay readable, which only a panic the compiler replied leaves them. */
export class CompilerFailure extends Error {
  readonly request: string;
  readonly readable: boolean;
  constructor(request: string, cause: unknown, context: string = "") {
    super(`${messageOf(cause).split("\n")[0] ?? ""}${context}`, { cause });
    this.request = request;
    this.readable = !context && !stackExhaustion(cause) && messageOf(cause).startsWith("panic:");
  }
}

/** A failure of a file-system operation of the front end: whatever it threw,
 * the operation and the path. Only `ioFailure` constructs one. */
class IoFailure extends Error {
  readonly operation: string;
  readonly path: string;
  constructor(operation: string, path: string, cause: unknown) {
    super(`${operation} ${path}: ${messageOf(cause).split("\n")[0] ?? ""}`, { cause });
    this.operation = operation;
    this.path = path;
  }
}

/** Causes registered by the maker, weakly keyed by the error identity. */
const ioFailures = new WeakMap<object, { readonly cause: unknown }>();

/** The failure of `operation` at `path` that threw `cause`, entered in the
 * table. */
export function ioFailure(operation: string, path: string, cause: unknown): Error {
  const failure = new IoFailure(operation, path, cause);
  ioFailures.set(failure, { cause });
  return failure;
}

/** The failure `thrown` is, with what its operation threw; undefined for any
 * other value. */
export const ioFailureOf = (thrown: unknown): { readonly cause: unknown } | undefined =>
  thrown !== null && typeof thrown === "object" ? ioFailures.get(thrown) : undefined;

/** A failure of the tool itself, not a refusal of the source, by kind:
 * - `panic`: the compiler process panicked on a query and replied so;
 * - `api`: any other failure of a request to the compiler (`CompilerFailure`),
 *   or an error raised in the compiler's package before the front end's code;
 * - `stack`: the front end exhausted the call stack, also inside a request;
 * - `io`: a file-system operation of the front end failed (`IoFailure`, which
 *   `files.mts` makes of whatever such an operation throws), where no absence
 *   was asked for (`orAbsent`).
 * `readable` is whether the channel's later replies may be read: only after
 * a replied panic. The query is the outermost API frame (the request's name
 * where there is none), the caller the first frame of the front end's own
 * code; the reason is the first line of the message. An error carrying a tool
 * failure as its `cause` is that failure. */
export type ToolFailure = { kind: "panic" | "api" | "stack" | "io"; readable: boolean; query: string; caller: string; reason: string };
export const toolFailureOf = (thrown: unknown): ToolFailure | null => {
  if (!(thrown instanceof Error)) return null;
  const request = thrown instanceof CompilerFailure ? thrown : null;
  const io = thrown instanceof IoFailure;
  if (!request && !io) {
    const inner = toolFailureOf(thrown.cause);
    if (inner) return inner;
  }
  const compiler = /[/\\](typescript|@typescript)[/\\]/;
  const frames = (thrown.stack ?? "").split("\n").map(l => l.trim()).filter(l => l.startsWith("at "));
  const inCompiler = frames.map(f => compiler.test(f));
  const own = (f: string): boolean => !compiler.test(f) && !(io && /^at ioFailure \(/.test(f)) && !/compiler-channel\.mts/.test(f) && /\.mts:\d+/.test(f);
  const firstOwn = frames.findIndex(own);
  const stack = stackExhaustion(thrown) || (request !== null && stackExhaustion(request.cause));
  const panic = thrown.message.startsWith("panic:");
  if (!request && !stack && !panic && !io && !inCompiler.slice(0, firstOwn < 0 ? frames.length : firstOwn).some(b => b))
    return null;
  const outer = inCompiler.lastIndexOf(true);
  const query = outer >= 0 ? (/^at (\S+)/.exec(frames[outer] ?? "")?.[1] ?? "?") : request?.request ?? "?";
  const caller = /\/([^/]+:\d+):\d+\)?$/.exec(frames.find((f, i) => i > outer && own(f)) ?? "")?.[1] ?? "?";
  return { kind: stack ? "stack" : panic ? "panic" : io ? "io" : "api", readable: request ? request.readable : panic || io,
    query, caller, reason: thrown.message.split("\n")[0] ?? "" };
};
/** A catch that makes a refusal, an absence or an unknown of what it caught
 * calls this first: a tool failure is none of them, and is thrown on. */
export const passToolFailure = (thrown: unknown): void => {
  if (toolFailureOf(thrown)) throw thrown;
};
/** The compiler's API (typescript 7.0.2) panics writing the type of an empty
 * array literal TypeScript types as a tuple (`[] as const`, or `[]` where a
 * destructuring or a tuple type is its context) into a reply, observed of
 * `Checker.getTypeAtLocation` and `TypeObject.getTypes`; it writes a declared
 * `[]` and a literal with an element. Its report says so. */
const emptyTuplePanic = "panic: interface conversion: checker.TypeData is *checker.TypeReference, not *checker.TupleType";
/** The report of a tool failure: no verdict on the source, located. */
export const toolFailureText = (failure: ToolFailure, at: string): string => failure.kind === "stack"
  ? `tool failure: the front end exhausted the call stack (at ${failure.caller}${failure.query === "?" ? "" : `, in ${failure.query}`}) ${at}`
  : failure.kind === "io" ? `tool failure: the file system failed (called from ${failure.caller}): ${failure.reason} ${at}`
  : failure.reason.startsWith(emptyTuplePanic)
    ? `tool failure: the compiler's API failed in ${failure.query} (called from ${failure.caller}): a type ` +
      "TypeScript gives here holds an empty array literal's tuple type (`[] as const`, or `[]` where a " +
      `destructuring or a tuple type is its context), which the compiler's API cannot write (${failure.reason}) ${at}`
    : `tool failure: the compiler's API failed in ${failure.query} (called from ${failure.caller}): ${failure.reason} ${at}`;
