// A call between the test and the read may write the cell: what it holds is
// its contract again, which admits `undefined`.
type Section = { name: string };

export function kept(s: Section): Section {
  let current: Section | undefined = s;
  const reset = (): void => {
    current = undefined;
  };
  if (current) {
    reset();
    return current;
  }
  return s;
}
