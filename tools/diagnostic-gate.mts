import type { Span } from "./span.mts";

/** A refusal carries its source identity independently of its wording. */
export type GateRefusal = { readonly pos: Span; readonly message: string };

/** Payloads registered by the maker, weakly keyed by the error identity. */
const refusals = new WeakMap<object, GateRefusal>();

/** The error a refusal at `pos` throws, entered in the table. */
export function refusal(message: string, pos: Span): Error {
  const error = new Error(message);
  refusals.set(error, { pos, message });
  return error;
}

/** The registered payload, or undefined for any other value. Lookup preserves the entry. */
export function refusalOf(thrown: unknown): GateRefusal | undefined {
  return thrown !== null && typeof thrown === "object" ? refusals.get(thrown) : undefined;
}
