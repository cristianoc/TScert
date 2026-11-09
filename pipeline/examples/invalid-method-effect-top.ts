// A statement of the footprint letting every location change, on a throw
// too: it states nothing the ordinary effect does not.
export function any(
  xs: number[],
): Modifies<{ values: "any"; stores: "any"; onThrow: true }, number> {
  xs.pop();
  return 0;
}
