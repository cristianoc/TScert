// An open read runs no code only by the open-read restriction: a getter at
// the key runs at the read, here giving a different value at each one (run
// under Node). The fragment admits no accessor, so no program makes one.
export function nameOf(manifest: unknown): unknown {
  return typeof manifest === "object" && manifest !== null && "name" in manifest
    ? manifest.name
    : null;
}
export function counted(): unknown {
  const state = { reads: 0 };
  return nameOf({
    get name() {
      state.reads = state.reads + 1;
      return state.reads;
    },
  });
}
