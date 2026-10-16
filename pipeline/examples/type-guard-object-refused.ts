// A promise about objects is decided by no test of the argument the model
// answers: `typeof v === "object"` gives `unknown` no narrower type.
export function isRecord(v: unknown): v is Record<string, unknown> {
  return !!v && typeof v === "object" && !Array.isArray(v);
}
