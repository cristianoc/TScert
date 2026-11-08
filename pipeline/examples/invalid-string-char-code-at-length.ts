// A code unit read at the string's length is `NaN`, no safe integer: the
// call requiring one is refused (run under Node: `last("ab")` is `NaN`).

/** @requires safeInteger(c) */
function unit(c: number): number {
  return c;
}

export function last(text: string): number {
  return unit(text.charCodeAt(text.length));
}
