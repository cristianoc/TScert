// A regex owns `lastIndex`, which the model's regex does not state: `in` with
// that key is refused whatever the operand's type, a view `object` included.
export function hasState(o: object): boolean {
  return "lastIndex" in o;
}
