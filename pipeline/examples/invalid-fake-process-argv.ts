// `process` here is the project's own declaration, spelled as Node's: no
// reviewed entry admits its origin, so its `argv` is not read as Node's.
export function args(): string[] {
  return process.argv.slice(2);
}
