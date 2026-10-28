// `instanceof Map` and `instanceof Set` on a value of unknown type: no
// reviewed entry states what an object passing either test holds.
// Census functions:
// diagnostic-gate.mts#recoverGate, diagnostic-gate.mts#copied,
// diagnostic-gate.mts#copy.
export function isCollection(value: unknown): boolean {
  return value instanceof Map || value instanceof Set;
}
