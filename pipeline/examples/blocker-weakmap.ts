// Empty WeakMap construction through the audited native contract.
// Census functions:
// compiler-channel.mts#query, files.mts#answerOf,
// files.mts#compilerFileSystem, files.mts#compilerText, files.mts#direntsOf,
// files.mts#direntsRead, files.mts#entriesOf, files.mts#entriesRead,
// files.mts#listDirectory, files.mts#nodeResolve, files.mts#observationsHold,
// files.mts#observePackageLinks, files.mts#observeResolution,
// files.mts#observeScope, files.mts#observed, files.mts#observedNoting,
// files.mts#remembered, files.mts#resolveObserved, files.mts#treeDigest,
// files.mts#validateLedger, wire-strings.mts#wireText.
export function use(): void {
  const values = new WeakMap<object, number>();
}
