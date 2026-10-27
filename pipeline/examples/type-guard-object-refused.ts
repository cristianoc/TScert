// A promise about dictionaries is decided by no test of the argument: the
// tests leave an object without call code, which may be a class instance or
// a host object.
export function isRecord(v: unknown): v is Record<string, unknown> {
  return !!v && typeof v === "object" && !Array.isArray(v);
}
