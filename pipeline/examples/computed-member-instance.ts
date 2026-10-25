interface Enabled {
  enabled: number;
}
interface Text {
  text: string;
}
interface Cell<Flag extends boolean = false> {
  value: Flag extends true ? Enabled : Text;
  next: Cell<Flag> | null;
  read(value: Flag extends true ? number : string): number;
}
export function use(left: Cell, right: Cell<true>): number {
  left.value = { text: "ready" };
  right.value = { enabled: 1 };
  return left.read("ready") + right.read(1);
}
export function recursive(cell: Cell<true>): number {
  const next = cell.next;
  if (next === null) return 0;
  return next.value.enabled;
}
