// An ordinary ReadonlyMap reader can run arbitrary code. During map it
// may remove a path before that path's position is visited, leaving a hole.
export function read(
  overlay: ReadonlyMap<string, string>,
  paths: string[],
): string[] {
  return paths.map((path) => overlay.get(path) ?? "");
}
