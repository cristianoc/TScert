// `createHash("sha256").update(s).digest("hex")` from `node:crypto`, read
// through its reviewed entry in the overlay of library modules: Node's
// declarations of `Hash`, `HashOptions` and the streams they name are not
// read. `update` takes bytes too, a `Uint8Array` or a `Buffer`.
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
export function bytes(b: Uint8Array): string {
  return createHash("sha256").update(b).digest("hex");
}
