// The host answers `in` with a Boolean: a result claimed at `true` is not
// established by it, whatever the operands.
export function always(t: [number]): true {
  const r: true = (0 in t) as true;
  return r;
}
