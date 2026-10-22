// A closure's parameter declared at a union is held at the union's arms, as a
// function's is: a failed `in` test drops the arms that own the key, and a
// read on the rest sees their fields, an optional one included.
type Part = { name: string; computed?: true } | { spread: number };
export function annotated(parts: Part[]): string[] {
  return parts.map((p: Part) =>
    "spread" in p ? "s" : p.computed ? "c" : p.name,
  );
}
export function contextual(parts: Part[]): string[] {
  return parts.map((p) => ("spread" in p ? "s" : p.name));
}
export function block(parts: Part[]): number[] {
  return parts.map((p) => {
    if ("spread" in p) return 0;
    return p.name.length;
  });
}
export function local(): (p: Part) => string {
  const name = (p: Part): string => ("spread" in p ? "s" : p.name);
  return name;
}
