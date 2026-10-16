// `x++`, `x--` and `x op= r` of a local cell inside a closed expression (an
// operand of `&&`, an arrow's expression body) read the cell at its contract,
// write the result back at it, and give the old or the new value.
export function counts(): number {
  let x: number = 5;
  const ok = x++ > 0 && x-- > 0;
  const g = (): boolean => (x += 2) > 3 || x++ < 0;
  return ok && g() ? x : 0;
}
