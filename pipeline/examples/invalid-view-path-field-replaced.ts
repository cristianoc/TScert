// The bound `i < prepared.segmentFlags.length` is tested, then the field
// `segmentFlags` itself is replaced by an empty view before the read: the
// write alters the object the field held, so the count read through the
// field is not kept, and the read is refused (run under Node:
// `flagAfterReplace({ segmentFlags: new Uint8Array(1) }, 0)` reads
// `undefined` at `number`).

export type Prepared = { segmentFlags: Uint8Array };

export function flagAfterReplace(prepared: Prepared, i: number): number {
  if (0 <= i && i < prepared.segmentFlags.length) {
    prepared.segmentFlags = new Uint8Array(0);
    return prepared.segmentFlags[i]!;
  }
  return 0;
}
