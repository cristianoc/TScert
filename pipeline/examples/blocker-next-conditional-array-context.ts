// Census: tools/declaration-graph.mts#withProject,#clientErrors.
type Document = string | { uri: string };
export function snapshot(
  file: string,
  opened: boolean,
  api: { update(request: { closeFiles?: Document[] }): { value: number } },
): number {
  const closeFiles: Document[] | undefined = opened ? [file] : undefined;
  const saved = api.update({ ...(closeFiles ? { closeFiles } : {}) });
  return saved.value;
}
