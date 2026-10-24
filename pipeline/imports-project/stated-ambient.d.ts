// Values declared outside the program's sources whose types state effects
// (`invalid-stated-external-value-import`, `invalid-stated-external-alias-value-import`):
// their code is the environment's, which no run checks.
declare module "@fixture/stated-ambient" {
  import type { Keeps } from "@fixture/stated";
  export function ext(
    n: number,
  ): Within<{ value: "keep"; store: "keep" }, number>;
  export const copied: Keeps;
}
