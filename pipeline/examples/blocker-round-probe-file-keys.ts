// Census functions: declaration-graph.mts#withProject,#withOwnProject,#clientErrors.
// The probe interface retains the callers' constructed native maps.
export function keys(files: Map<string, string>): string[] {
  return [...files.keys()];
}
