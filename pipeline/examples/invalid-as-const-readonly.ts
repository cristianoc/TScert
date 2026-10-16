// `as const` makes an array literal a readonly tuple, which is not the
// mutable tuple of the same elements: a write through the mutable view would
// reach a value the readonly one promised constant.
export function mutable(): [0, 1] {
  const t = [0, 1] as const;
  return t;
}
