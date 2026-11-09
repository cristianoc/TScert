// tools/files.mts#io records a failure and rethrows. A normal-return
// footprint composes through the query; the handler has no normal exit.
let queryFailure: unknown = null;
export function kept<T>(
  query: () => Modifies<{ values: "any"; stores: "grow" }, T>,
): Modifies<{ values: "any"; stores: "grow" }, T> {
  try {
    return query();
  } catch (error) {
    queryFailure ??= error;
    throw error;
  }
}
// A throwing region can change storage arbitrarily; its effects never
// reach a normal return of this invocation.
export function changedOnThrow(
  xs: number[],
  query: () => Modifies<{ values: "any"; stores: "grow" }, number>,
): Modifies<{ values: "any"; stores: "grow" }, number> {
  try {
    return query();
  } catch (error) {
    xs.pop();
    throw error;
  }
}
export function nested(
  xs: number[],
  query: () => Modifies<{ values: "any"; stores: "grow" }, number>,
): Modifies<{ values: "any"; stores: "grow" }, number> {
  try {
    return query();
  } catch (error) {
    try {
      xs.pop();
      throw error;
    } catch (second) {
      xs.pop();
      throw second;
    }
  }
}
export function finalizer(
  query: () => Modifies<{ values: "any"; stores: "grow" }, number>,
): Modifies<{ values: "any"; stores: "grow" }, number> {
  try {
    return query();
  } finally {
    queryFailure = 1;
  }
}
function inferred(
  query: () => Modifies<{ values: "any"; stores: "grow" }, number>,
): number {
  try {
    return query();
  } catch (error) {
    queryFailure = error;
    throw error;
  }
}
export function mapped(
  xs: number[],
  query: () => Modifies<{ values: "any"; stores: "grow" }, number>,
): number[] {
  return xs.map(() => inferred(query));
}
