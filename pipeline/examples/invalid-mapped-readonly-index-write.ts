// `Readonly` makes a number index readonly: its value is not a record with a
// writable number index.
export function writable(p: Readonly<{ [k: number]: string }>): { [k: number]: string } {
  return p;
}
