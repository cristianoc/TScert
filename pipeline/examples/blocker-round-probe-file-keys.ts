// Census functions: declaration-graph.mts#withProject,#withOwnProject,#clientErrors.
// The probe interface widens the callers' constructed native maps to ReadonlyMap.
export function keys(files: ReadonlyMap<string, string>): string[] {
  return [...files.keys()];
}
