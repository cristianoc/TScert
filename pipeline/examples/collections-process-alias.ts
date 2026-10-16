// A global is read at the members its references name, and as a value at its
// call signatures: an alias of one that declares none is refused.
const p = process;
export function f(): void {
  p;
}
