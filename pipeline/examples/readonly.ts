function viewOfAlias(cell: { value: number }): number {
  const view: { readonly value: number } = cell;
  cell.value = 2;
  return view.value;
}
function readonlyArray(items: number[]): readonly (number | string)[] {
  return items;
}
