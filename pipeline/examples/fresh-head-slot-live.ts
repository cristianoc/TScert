// An edge into a loop head keeps the names at the slots the head states
// fresh: `found`, a fresh array, holds its name on every edge into the
// inner loop, whose head states it fresh, although no later node of the
// loop reads it (SINGLE-PASS.md, "One state").
// Census functions:
// family-activation.mts#installations, declaration-graph.mts#resolutionClean.
type Description = { readonly marker: string; readonly guards: readonly string[] };
declare function active(): readonly Description[];
declare function rootOf(d: Description): string;
export function owners(): readonly { description: Description; root: string }[] {
  const found = active().flatMap(description => [{ description, root: rootOf(description) }]);
  for (const [i, a] of found.entries())
    for (const b of found.slice(i + 1)) {
      if (a.description.marker === b.description.marker) throw Error(`two own ${a.description.marker}`);
      if (a.root === b.root || a.root.startsWith(b.root + "/")) throw Error(`shared ${a.root}`);
      if (a.description.guards.some(g => b.description.guards.includes(g))) throw Error("a shared guard");
    }
  return found;
}
