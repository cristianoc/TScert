function aliasWrite(seed: boolean): boolean {
  const cell = { value: seed, ready: true };
  const alias = cell;
  alias.value = false;
  return cell.value;
}
function objectParameter(cell: { value: boolean; ready: boolean }): boolean {
  cell.ready = true;
  return cell.value;
}
