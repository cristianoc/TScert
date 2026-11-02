// A current-content check cannot promise a lasting readonly field type.
// A later callback can mutate a previously selected object through its alias.
type Cell = { value: string | null };
export function unsafe(xs: Cell[], victim: Cell): string[] {
  const selected = xs.filter((x, i): x is { readonly value: string } => {
    if (i > 0) victim.value = null;
    return x.value !== null;
  });
  return selected.map((x) => x.value.toUpperCase());
}
