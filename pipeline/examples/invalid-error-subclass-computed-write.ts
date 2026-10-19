// A write at a key known only as a string may set `stack`, which stays
// non-enumerable on an instance (run under Node). Refused at the receiver.
class Decline extends Error {}

export function set(e: Decline, k: string): void {
  // @ts-expect-error a string key of an instance
  e[k] = "s";
}
