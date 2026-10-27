// `new TypeError(m)` at a string message constructs an error whose message
// is that string and whose name, inherited from `TypeError.prototype`, is
// `"TypeError"`; with options stating `cause`, it holds the cause. A throw of
// it is an outcome.
export function fail(message: string): never {
  throw new TypeError(message);
}
export function made(message: string): string {
  const error = new TypeError(message);
  return `${error.name}: ${error.message}`;
}
export function caused(message: string, cause: number): never {
  throw new TypeError(message, { cause });
}
