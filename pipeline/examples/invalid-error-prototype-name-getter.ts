// A getter installed at `Error.prototype.name` runs code at every read of an
// error's `name` and may return what is no string (run under Node: 5). The
// source reaches neither `Object.defineProperty` nor `Error.prototype`.
export function main(): string {
  Object.defineProperty(Error.prototype, "name", { get: () => 5 });
  return new Error("m").name;
}
