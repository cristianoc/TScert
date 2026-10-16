// The call's value is its target: onto a local's object it would be one more
// reference to it, so only the statement form is lowered.
export function copy(): { a: number; b: string } {
  const o = { a: 1 };
  return Object.assign(o, { b: "s" });
}
