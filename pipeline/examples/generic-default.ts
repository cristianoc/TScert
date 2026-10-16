// The scheme checker must not discard this default and certify only the body.
// Its write breaks the fixed boolean contract and returns null at run time.
// Field writes in a rigid body remain outside its certificate language.
function genericDefault(seed: boolean): boolean {
  const cell: { value: boolean } = { value: seed };
  const pick = <T>(
    value: T,
    ignored: boolean | undefined = (cell.value = null),
  ): T => value;
  const result: boolean = pick(seed, undefined);
  return cell.value;
}
