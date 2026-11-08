// A stable view length does not keep the field pointing to that view.
export function replace(prepared: { segmentFlags: Uint8Array }): void {
  prepared.segmentFlags = new Uint8Array(0);
}

export function first(prepared: { segmentFlags: Uint8Array }): number {
  if (prepared.segmentFlags.length > 0) {
    replace(prepared);
    return prepared.segmentFlags[0]!;
  }
  return 0;
}
