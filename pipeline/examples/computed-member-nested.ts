interface Value<T> {
  value: T;
}
interface Cell<F extends boolean> {
  nested: F extends true ? Value<number> : Value<string>;
}
export function read(cell: Cell<true>): number {
  return cell.nested.value;
}
class Box {
  value: number = 1;
}
interface ObjectCell<F extends boolean> {
  object: F extends true ? Box : number;
}
export function objectRead(cell: ObjectCell<true>): number {
  return cell.object.value;
}
