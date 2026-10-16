// A null singleton obtained through a binding is the same comparison operand
// as literal null; its claim still needs independent checking.
function namedNull(seed: number | null): number {
  const box = { value: seed };
  const value = box.value;
  const absent: null = null;
  if (value !== absent) return value;
  return 0;
}

function leftUndefined(value: boolean | undefined): boolean {
  const missing: undefined = undefined;
  return missing === value ? false : value;
}

// The receiver read must precede clear(), and must not be repeated afterwards.
function comparisonOrder(seed: boolean): boolean {
  const cell: { value: boolean | null } = { value: seed };
  const clear = (): null => {
    cell.value = null;
    return null;
  };
  return cell.value !== clear();
}
