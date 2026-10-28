// `instanceof Map` and `instanceof Set` on a value of unknown type, the
// collection then iterated, and the value a key of a map read by `has` and
// `get`, as the diagnostic gate's copy does.
// Census functions:
// diagnostic-gate.mts#recoverGate, diagnostic-gate.mts#copied,
// diagnostic-gate.mts#copy.
export function copied(value: unknown, seen: Map<object, unknown>): unknown {
  if (!value || typeof value !== "object") return value;
  if (seen.has(value)) return seen.get(value);
  if (value instanceof Map) {
    const result = new Map<unknown, unknown>();
    seen.set(value, result);
    for (const [key, item] of value) result.set(key, copied(item, seen));
    return result;
  }
  if (value instanceof Set) {
    const result = new Set<unknown>();
    seen.set(value, result);
    for (const item of value) result.add(copied(item, seen));
    return result;
  }
  return value;
}
