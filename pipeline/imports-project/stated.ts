// A module whose functions state their effects (`Within<F, T>`), which the
// stated-import examples import: `keep` meets its statement; `drain` pops
// the array it is handed, so its own run refuses it, and an importer reads
// it at its declaration, the import assumption (`stated-assumed-value-import`).
export function keep(
  n: number,
): Within<{ value: "keep"; store: "keep" }, number> {
  return n;
}

// `keep`'s type, statement included, under a name a declaration file reads
// (`invalid-stated-external-alias-value-import`).
export type Keeps = typeof keep;

// A guard stating the empty footprint at its promise's type
// (`stated-guard-value-import`).
export interface Circle {
  kind: "circle";
  radius: number;
}
export interface Square {
  kind: "square";
  side: number;
}
export function isCircle(
  s: Circle | Square,
): s is Within<{ value: "keep"; store: "keep" }, Circle> {
  return s.kind === "circle";
}

export function drain(
  xs: number[],
  x: number,
): Within<{ value: "keep"; store: "keep" }, number> {
  xs.pop();
  return x;
}
