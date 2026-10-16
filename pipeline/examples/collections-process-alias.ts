// A global is read only at the members its references name, so a reference
// that names none, such as an alias of it, is refused.
const p = process;
export function f(): void {
  p;
}
