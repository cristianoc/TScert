// Census functions:
// family-activation.mts#installations
// family-activation.mts#familyOfFile
// family-activation.mts#installationPath
// family-activation.mts#isHostFile
// family-activation.mts#selectionGuard
export function installations(
  active: string[],
  root: (s: string) => Modifies<{ values: "any"; stores: "grow" }, string>,
): readonly { description: string; root: string }[] {
  const found = active.map((description) => ({
    description,
    root: root(description),
  }));
  for (const [i, a] of found.entries())
    for (const b of found.slice(i + 1))
      if (a.root === b.root) throw Error("same root");
  return found;
}
