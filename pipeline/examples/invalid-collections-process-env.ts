// `process.env` is a string index: a variable may be unset, and TypeScript
// (with `noUncheckedIndexedAccess`) and the model both read `string | undefined`.
export function read(): string {
  const value: string = process.env["APP_PLATFORM"];
  return value;
}
