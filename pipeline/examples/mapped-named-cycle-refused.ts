// A mapped type at an interface whose own field is that mapped type: its
// expansion needs the interface's settled shape while that shape is settled,
// and the reader refuses it.
interface Patch {
  value: number;
  child: Partial<Patch>;
}
export function value(p: Patch): number {
  return p.value;
}
