// Hash and stream declarations need reviewed contracts instead of synthesised
// members with no written origin.
// Census functions:
// family-activation.mts#checkInventory,
// family-activation.mts#checkedInstallation,
// family-activation.mts#checkedInventory,
// family-activation.mts#declarationsDigest, family-activation.mts#digestOf,
// family-activation.mts#familyOfFile, family-activation.mts#installationPath,
// family-activation.mts#isHostFile, files.mts#fileDigest,
// files.mts#readAnswer, files.mts#readBytes, guard-closure.mts#guardClosure,
// host-families.mts#familyTable, unchecked.mts#isResult.
import { createHash } from "node:crypto";
export function use(s: string): string {
  return createHash("sha256").update(s).digest("hex");
}
