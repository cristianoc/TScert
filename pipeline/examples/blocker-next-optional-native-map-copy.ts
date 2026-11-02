// Census functions:
// family-activation.mts#importedGuard
// family-activation.mts#importedExport
// family-activation.mts#activatedModules
export function copy(
  source: Map<string, number> | undefined,
): ReadonlyMap<string, number> {
  const modules = new Map<string, number>(source);
  return modules;
}
