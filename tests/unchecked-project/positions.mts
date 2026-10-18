/* External `any` at positions a syntactic classification misses: TypeScript
 * decides each through the one opaque type the shadow program reads it as. */
import { Derived, bounded, box, conditional, dict, made, sink, takesAlias } from "./library/index.mjs";

bounded(1);
bounded("oops"); // expected: any flow
// @ts-ignore -- the next line's error would vanish // expected: suppressed
export const ignored: number = JSON.parse("1");
takesAlias(1); // expected: any flow
box.x = 1; // expected: any flow
dict.x = 1; // expected: any flow
sink.put(1); // expected: any flow
new Derived().put(1); // expected: any flow
const defaulted = made();
export const nested: { x: number } = defaulted; // expected: any flow
export const checked: { x: number } = conditional; // expected: any flow
export const text: string = JSON.stringify(undefined); // expected: any flow
export const listed: string = JSON.stringify({ a: 1 }, ["a"]);
// @ts-expect-error -- a directive of its own // expected: suppressed
export const silenced: number = JSON.parse("1");

export const inline = 1; // @ts-ignore // expected: suppressed
export const hidden: number = JSON.parse("1");
