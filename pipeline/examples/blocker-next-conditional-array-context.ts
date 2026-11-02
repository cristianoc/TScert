// Census: tools/declaration-graph.mts#withProject,#clientErrors.
type Document = string | { uri: string };
export function snapshot(
  file: string,
  opened: boolean,
  api: { update(request: { closeFiles?: Document[] }): { value: number } },
): number {
  const saved = api.update({ ...(opened ? { closeFiles: [file] } : {}) });
  return saved.value;
}
