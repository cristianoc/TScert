// A closure made where a cell is narrowed reads it when it runs, after a
// call that writes the cell: what it holds is its contract again, which
// admits `null`.
export function wrong(): string {
  let x: string | null = "a";
  const clear = (): void => {
    x = null;
  };
  if (x !== null) {
    const get = (): string => x as string;
    clear();
    return get();
  }
  return "";
}
