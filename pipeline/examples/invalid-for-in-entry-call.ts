// A call between the step and the read may remove the key the step visited
// (`delete v[k]`): the read then finds `undefined`, which `!` does not rule
// out.
export function wrong(
  v: { [k: string]: number },
  before: (v: { [k: string]: number }) => void,
): number {
  for (const k in v) {
    before(v);
    return v[k]!;
  }
  return 0;
}
