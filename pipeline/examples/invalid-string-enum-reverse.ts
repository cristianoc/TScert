// A string enum's object has no reverse mapping: at a member's value there
// is no key, though TypeScript admits the object as a dictionary of strings.
enum Unit {
  Name = "name",
  Call = "call",
}
const units: { readonly [k: string]: string } = Unit;
function unitName(u: Unit): number {
  return units[u].length;
}
