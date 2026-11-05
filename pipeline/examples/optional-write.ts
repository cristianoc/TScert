// Census sites: files.mts#inputRead and files.mts#noteInput.
// A shared recording owns its flag from construction; marking an input
// replaces the flag while every reference keeps the same object.
type Recording = { readsInput: boolean };
export function mark(recording: Recording): void {
  recording.readsInput = true;
}
export function shared(): boolean {
  const recording: Recording = { readsInput: false };
  const alias = recording;
  mark(recording);
  return alias.readsInput;
}
