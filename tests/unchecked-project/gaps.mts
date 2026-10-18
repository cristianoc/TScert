/* Accepted by the check, and not by the written program or by the type the
 * declarations write: the relations that `any` satisfied in an outside
 * declaration are not re-established, a limit the check states (WORK.md,
 * "The any check over external declarations"). No line here is expected:
 * each is a documented gap; and `JSON.stringify` of a function is typed
 * `string`. */
import { box, chosen, f, sink, D } from "./gaps/index.mjs";

export const overloaded: string = f(new D());
export const member: { x: number } = box;
export const computed: number = chosen;
sink.put(1);
export const stringified: string = JSON.stringify(function named(): void {});
