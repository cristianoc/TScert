// A declared generic value whose type literal has a method over its binder:
// at each call's instance the binder is its ground argument, and the type
// literal is the record with that method.
declare function unwrap<A>(value: { f(input: A | null): A }): A;
function f(input: string | null): string {
  return input ?? "";
}
export function use(): string {
  return unwrap({ f });
}
