// `new RegExp` of strings: a regex whose capture shape and flags are known
// only at run time, read as a `RegExp` annotation states one.
export function matches(pattern: string, text: string): boolean {
  return new RegExp(pattern, "u").test(text);
}
export function first(pattern: string, text: string): string {
  const found = new RegExp(pattern).exec(text);
  return found ? found[0] : "";
}
