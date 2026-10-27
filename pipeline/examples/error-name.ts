// An error's `name` is the string `Error.prototype` holds, `"Error"`, which
// the model states on the error's first link beside its message: a read, a
// destructuring and `in` find it, `Object.keys` does not list it, and the
// error meets TypeScript's `Error`, as an instance of a class extending
// `Error` does (run under Node).
class Failure extends Error {}

export function wrapped(): Error {
  return new Error("boom");
}

export function named(): string {
  return new Error("m").name;
}

export function described(e: Error): string {
  const { name, message } = e;
  return `${name}: ${message}`;
}

export function inherited(): string {
  return new Failure("x").name;
}

export function found(): boolean {
  return "name" in new Error("m");
}

export function listed(): string[] {
  return Object.keys(new Error("m"));
}

export function both(): Error[] {
  return [new Error("a"), new Failure("b")];
}
