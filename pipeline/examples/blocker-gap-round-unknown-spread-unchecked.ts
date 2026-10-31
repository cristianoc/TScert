// Spread of unknown after object and null tests.
// Census functions:
// family-activation.mts#activeGuards
// family-activation.mts#loadedGuards
// family-activation.mts#activateGuards
// family-activation.mts#checkedGuards
// family-activation.mts#guardOfExport
export function spread(loaded: unknown): object {
  if (typeof loaded !== "object" || loaded === null)
    throw Error("object required");
  return { ...loaded };
}
