// `JSON.stringify` of a `Buffer` calls `Buffer.prototype.toJSON`, code of
// the host's the overlay does not state (run under Node: an object naming
// its type and data): a `Buffer` is no `JsonValue`, refused.
export function serialized(bytes: Buffer): string {
  return JSON.stringify(bytes);
}
