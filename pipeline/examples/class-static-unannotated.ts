// A static field without an annotation is at the type TypeScript gives it,
// which the class value's type states: its initializer's value is checked
// at it.
function seed(): number {
  return 4;
}
class Config {
  static readonly port = seed();
  static readonly label = "a" + "b";
  static readonly unit = 1;
}

export function use(): number {
  return Config.port + Config.label.length + Config.unit;
}
