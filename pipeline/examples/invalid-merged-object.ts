// Another module of the project merges `toJSON(): undefined` into `Object`,
// stating a hook every object inherits: the unit is refused at its first
// construct reaching the declarations, here the global `JSON`.
export function text(): string {
  return JSON.stringify({ a: 1 });
}
