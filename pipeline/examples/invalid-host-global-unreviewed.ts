// A global function a declaration file of the project declares: its
// implementation is the host's, outside what is verified, and no reviewed
// entry lists it, so the call is refused, the file's location
// notwithstanding.
export function now(): number {
  return hostNow();
}
