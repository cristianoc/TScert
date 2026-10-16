// Another binding holds the target: the keys the copy adds would be seen
// through it, so the statement is refused.
export function copy(): { a: number } {
  const o = { a: 1 };
  const alias = o;
  Object.assign(o, { b: "s" });
  return alias;
}
