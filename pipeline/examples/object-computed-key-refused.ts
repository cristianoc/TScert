// A computed key in an object literal that names no `unique symbol` constant:
// an allocation's keys are the names it spells, and this one is known only at
// run time.
export function make(key: string): object {
  return { [key]: 1 };
}
