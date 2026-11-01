// Adding an optional key can break another writable view of the same object.
type WithOptional = { opt?: number };
export function set(x: WithOptional): void {
  x.opt = 3;
}
export function unsafe(): string {
  const object = {};
  const numbers: WithOptional = object;
  const strings: { opt?: string } = object;
  set(numbers);
  return strings.opt === undefined ? "absent" : strings.opt.toUpperCase();
}
