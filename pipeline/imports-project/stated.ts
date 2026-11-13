// A module whose functions state their effects (`Modifies<P, T>`), which the
// stated-import examples import: `keep` meets its statement; `drain` pops
// the array it is handed, so its own run refuses it, and an importer reads
// it at the ordinary effect (`invalid-stated-assumed-value-import`).
export function keep(n: number): Modifies<{}, number> {
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
export function isCircle(s: Circle | Square): s is Modifies<{}, Circle> {
  return s.kind === "circle";
}

export function drain(xs: number[], x: number): Modifies<{}, number> {
  xs.pop();
  return x;
}
