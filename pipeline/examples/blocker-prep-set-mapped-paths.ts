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
  const joined: string[] = [];
  for (const file of inventory) joined.push(join(root, ...file.split("/")));
  return new Set(joined);
}
