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


/** A failure of the tool itself, not a refusal of the source: an error
 * raised inside the compiler's package (its RPC channel, or a panic of the
 * compiler process it reports), or the front end exhausting the call stack,
 * which can interrupt a query mid-reply and leave the channel's next reply
 * unreadable. The query is the outermost API frame, the caller the first
 * frame of the front end's own code; the reason is the first line of the
 * message. An error carrying a tool failure as its `cause` is that failure. */
export type ToolFailure = { kind: "api" | "stack"; query: string; caller: string; reason: string };
export const toolFailureOf = (thrown: unknown): ToolFailure | null => {
  if (!(thrown instanceof Error)) return null;
  const inner = toolFailureOf(thrown.cause);
  if (inner) return inner;
  const compiler = /[/\\](typescript|@typescript)[/\\]/;
  const frames = (thrown.stack ?? "").split("\n").map(l => l.trim()).filter(l => l.startsWith("at "));
  const inCompiler = frames.map(f => compiler.test(f));
  const panic = thrown.message.startsWith("panic:");
  const stack = thrown instanceof RangeError && thrown.message === "Maximum call stack size exceeded";
  if (!stack && !panic && !inCompiler[0]) return null;
  const outer = inCompiler.lastIndexOf(true);
  const query = outer >= 0 ? (/^at (\S+)/.exec(frames[outer] ?? "")?.[1] ?? "?") : "?";
  const own = frames.find((f, i) => i > outer && !compiler.test(f)) ?? "";
  const caller = /\/([^/]+:\d+):\d+\)?$/.exec(own)?.[1] ?? "?";
  return { kind: stack ? "stack" : "api", query, caller, reason: thrown.message.split("\n")[0] ?? "" };
};
/** The compiler's API (typescript 7.0.2) panics writing the type of an empty
 * array literal TypeScript types as a tuple (`[] as const`, or `[]` where a
 * destructuring or a tuple type is its context) into a reply, observed of
 * `Checker.getTypeAtLocation` and `TypeObject.getTypes`; it writes a declared
 * `[]` and a literal with an element. The source holds no defect there, but
 * the query's answer is not known: the gate refuses where the query was
 * made, naming the panic. */
export const emptyTupleRefusal = (failure: ToolFailure): string | null =>
  failure.reason.startsWith("panic: interface conversion: checker.TypeData is *checker.TypeReference, not *checker.TupleType")
    ? `a type TypeScript gives here holds an empty array literal's tuple type (\`[] as const\`, or \`[]\` where a ` +
      `destructuring or a tuple type is its context), which the compiler's API cannot write: ${failure.query} ` +
      `panics (${failure.reason})`
    : null;
/** The report of a tool failure: no verdict on the source, located. */
export const toolFailureText = (failure: ToolFailure, at: string): string => failure.kind === "stack"
  ? `tool failure: the front end exhausted the call stack (at ${failure.caller}${failure.query === "?" ? "" : `, in ${failure.query}`}) ${at}`
  : `tool failure: the compiler's API failed in ${failure.query} (called from ${failure.caller}): ${failure.reason} ${at}`;
