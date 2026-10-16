function invalidWrite(seed: boolean): boolean {
  const cell = { value: seed };
  const alias = cell;
  alias.value = null;
  return cell.value;
}
