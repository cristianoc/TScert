// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// measurement.ts#buildEngineProfile, which with the rewrites of TScert
// issue #94 reads it through `{ readonly userAgent?: string }` and verifies.
// Refusal: search: closure expression claim: the available claim for
// navigator is the host's Navigator, and the assertion requires a record
// whose `userAgent` is writable.
// The DOM global `navigator`, asserted to a record of an optional writable
// `userAgent` before the read: the assertion would grant a write of a
// member the host defines only a getter for.
export function agent(): string {
  return typeof navigator === "undefined"
    ? ""
    : ((navigator as { userAgent?: string }).userAgent ?? "");
}
