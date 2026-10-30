// A `typeof` label narrows to the shape it names alone: the clause of
// `"string"` calls `toFixed`, which a string lacks.
export function describe(v: string | number): string {
  switch (typeof v) {
    case "string":
      return v.toFixed(2);
    default:
      return "";
  }
}
