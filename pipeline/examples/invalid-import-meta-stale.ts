// The module's first evaluation of `import.meta` reads `isMain` of its
// wrapper, where a getter other code defined runs and empties the box.
export function stale(box: { v: string | undefined }): string {
  if (box.v === undefined) return "";
  const url = import.meta.url;
  return typeof url === "string" ? box.v : "";
}
