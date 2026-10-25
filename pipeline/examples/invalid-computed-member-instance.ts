interface Cell<Flag extends boolean = false> {
  value: Flag extends true ? number : string;
}
export function use(cell: Cell): number {
  return cell.value;
}
