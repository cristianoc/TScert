class Box {
  value: number = 1;
}
interface Cell<F extends boolean> {
  value: F extends true ? typeof Box : number;
}
export function read(cell: Cell<true>): number {
  return cell.value.value;
}
