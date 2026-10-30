// The iteration's binding is a cell a closure writes: after the closure runs,
// the test's narrowing no longer holds. TypeScript keeps it and types the
// result `string`; under Node, `cleared()` is `null`.
export function cleared(): string {
  for (let x: string | null = "a"; x !== null; ) {
    const clear = (): void => {
      x = null;
    };
    clear();
    return x;
  }
  return "";
}
