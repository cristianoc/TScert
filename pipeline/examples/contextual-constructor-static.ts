class Box {
  value: number = 1;
}
class Holder {
  static readonly ctor = Box;
}
export function use(): number {
  return Holder.ctor.value;
}
