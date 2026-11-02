// The object default runs before the nested array rest. Its pop violates
// the stated growth footprint even though the subsequent collection is pure.
export function changed(
  source: { items?: readonly number[] },
  victim: number[],
): Within<{ value: "any"; store: "grow" }, number> {
  const { items: [, ...tail] = (victim.pop(), [0]) } = source;
  return tail.length;
}
