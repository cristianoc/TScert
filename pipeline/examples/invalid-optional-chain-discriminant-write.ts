// A call between the test and the read rewrites the tested `let`: what the
// chain's test established of it no longer holds.
type Answered = { readonly ok: true; readonly value: number } | { readonly ok: false; readonly refused: string };

export function wrong(start: Answered | undefined, reset: Answered | undefined): number {
  let found = start;
  const clear = (): void => {
    found = reset;
  };
  if (found?.ok) {
    clear();
    return found.value;
  }
  return 0;
}
