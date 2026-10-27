// A member read on an `unknown` that `typeof x === "function"` found a
// function, as a loaded guard is compared with its source text.
// Census functions:
// family-activation.mts#checkedGuards, family-activation.mts#activateGuards,
// family-activation.mts#activeGuards, family-activation.mts#loadedGuards,
// family-activation.mts#importedGuard, family-activation.mts#importedExport,
// family-activation.mts#guardOfExport, family-activation.mts#selectionGuard,
// family-activation.mts#hostEnumObject, family-activation.mts#tagEnumObject.
export function runs(value: unknown, text: string): boolean {
  return typeof value === "function" && value.toString() === text;
}
