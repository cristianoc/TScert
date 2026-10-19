// `stack` is an engine's own property of an error, outside the stated
// instance: its read is refused.
class Decline extends Error {}
export function trace(): string | undefined {
  return new Decline("x").stack;
}
