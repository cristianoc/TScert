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

