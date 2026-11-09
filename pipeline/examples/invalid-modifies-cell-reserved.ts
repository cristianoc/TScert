// A cache in a binding named `values`, stated as the cell `"cell(values)"`:
// a location key, which the reader refuses while no source statement reaches
// the regions it names.
let values: number[] | null = null;

export function cached(): Modifies<{ "cell(values)": "init" }, number[]> {
  values ??= [];
  return values;
}
