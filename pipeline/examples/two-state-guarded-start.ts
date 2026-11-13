// The start's identity under the guard its occurrence is read beneath:
// `maybePush`'s postcondition reads `xs.length` only where `xs` is not
// `undefined`, where its precondition defines it. The start knows
// `xs === undefined || xs.length === old(xs.length)`, which the entry facts
// entail, and no definedness of `xs.length` where `xs` is `undefined`.

/**
 * @requires xs === undefined || (0 <= xs.length && xs.length <= 1000)
 * @ensures xs === undefined || xs.length === old(xs.length) + 1
 */
export function maybePush(xs: number[] | undefined): Modifies<{ values: "any"; stores: "grow" }, void> {
  if (xs === undefined) return;
  xs.push(0);
}
