// `JSON.stringify` of an error with the replacer `["message"]` reads the
// message through [[Get]]; an error holding a prototype is no JSON value:
// refused at the argument.
export function text(): string {
  return JSON.stringify(new Error("x"), ["message"]);
}
