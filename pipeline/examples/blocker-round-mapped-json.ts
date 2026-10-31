// JSON serialization of a mapped array of arrays.
// Census functions:
// files.mts#answerOf
// files.mts#observationsHold
// files.mts#validateLedger
// files.mts#direntsOf
// files.mts#direntsRead
// files.mts#observeScope
// files.mts#observePackageLinks
// files.mts#observeResolution
// files.mts#loadModule
export function answer(entries: string[], kind: (e: string) => string): string {
  return JSON.stringify(entries.map((e) => [e, kind(e)]));
}
