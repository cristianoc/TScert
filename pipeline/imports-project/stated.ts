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

export function drain(
  xs: number[],
  x: number,
): Within<{ value: "keep"; store: "keep" }, number> {
  xs.pop();
  return x;
}
