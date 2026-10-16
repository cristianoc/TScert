// The contextual result is a claim only where the body fits it: "world" is
// not "hello", so the closure is claimed at its own `() => string`.
export function bad(): { fn: () => "hello" } {
  return { fn: () => "world" };
}
