/* A span belongs to no language here: the fragment, the claims document and the
 * report all carry them, so the one declaration lives on its own. This is the
 * TypeScript half of Decode.lean, and only half of it: there are no shared
 * field accessors to mirror, because each language file validates its own
 * shapes rather than sharing a decoder.
 */

/** A half-open span of the source, in UTF-16 code units. */
export type Span = [start: number, end: number];
