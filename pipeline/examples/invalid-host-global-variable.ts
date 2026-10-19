// A global variable a declaration file of the project declares: its value is
// the host's, and no reviewed entry lists its member, so the read is
// refused, the file's location notwithstanding.
export function level(): number {
  return hostConfig.level;
}
