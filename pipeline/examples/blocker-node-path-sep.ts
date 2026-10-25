// An imported property of an export-assigned Node module needs a reviewed
// constant contract.
// Census functions:
// declaration-graph.mts#declarationOrigin,
// declaration-graph.mts#globalFunction, declaration-graph.mts#moduleIds,
// declaration-graph.mts#originOf, declaration-graph.mts#selectGlobal,
// family-activation.mts#activateGuards,
// family-activation.mts#activatedModules, family-activation.mts#activeGuards,
// family-activation.mts#checkInventory, family-activation.mts#checkedGuards,
// family-activation.mts#checkedInstallation,
// family-activation.mts#checkedInventory,
// family-activation.mts#declarationInventory,
// family-activation.mts#declarationsDigest,
// family-activation.mts#familyOfFile, family-activation.mts#guardOfExport,
// family-activation.mts#hostEnumObject, family-activation.mts#importedExport,
// family-activation.mts#importedGuard, family-activation.mts#installationPath,
// family-activation.mts#installations, family-activation.mts#isHostFile,
// family-activation.mts#loadedGuards, family-activation.mts#selectionGuard,
// family-activation.mts#tagEnumMatches, family-activation.mts#tagEnumObject,
// files.mts#compilerFileSystem.
import { sep } from "node:path";
export function use(path: string): string[] {
  return path.split(sep);
}
