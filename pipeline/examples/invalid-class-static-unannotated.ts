// A static field without an annotation is at the type TypeScript gives it,
// a string here, which a number result does not admit.
class Config {
  static readonly label = "a" + "b";
}

export function use(): number {
  // @ts-expect-error a string is not a number
  return Config.label;
}
