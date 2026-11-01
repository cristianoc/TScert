// Census functions:
// family-activation.mts#checkedInstallation
// family-activation.mts#checkedInventory
// family-activation.mts#checkInventory
// family-activation.mts#importedGuard
// family-activation.mts#importedExport
// family-activation.mts#activatedModules
// family-activation.mts#hostEnumObject
// family-activation.mts#tagEnumObject
// family-activation.mts#tagEnumMatches
import { join } from "node:path";
export function paths(root: string, inventory: string[]): Set<string> {
  return new Set(inventory.map((file) => join(root, ...file.split("/"))));
}
