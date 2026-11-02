// Census functions: family-activation.mts#installations,#familyOfFile,
// #installationPath,#isHostFile,#selectionGuard.
// The real installation lookup has an ordinary arrow contract at this call.
import { installationRoot } from "../../tools/family-activation.mts";
import type { FamilyDescription } from "../../tools/host-families.mts";
export function installations(active: readonly FamilyDescription[]): readonly { description: FamilyDescription; root: string }[] {
  const found = active.flatMap(description => [{ description, root: installationRoot(description) }]);
  for (const [i, a] of found.entries())
    for (const b of found.slice(i + 1))
      if (a.root === b.root) throw Error("same root");
  return found;
}
