// Assigning the body's copy leaves the initializer closure's cell null.
// Node returns null, outside the stated string result.
export function wrong(): string {
  for (let x: string | null = null, get: () => string | null = () => x; ; ) {
    x = "body";
    return get();
  }
  return "";
}
