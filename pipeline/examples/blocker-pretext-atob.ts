// Pretext (github.com/chenglou/pretext at 0d102a5c, src/, census by unit):
// line-breaks.ts#unpackTable, line-breaks.ts#unpackVarints.
// Refusal: gate: atob(…) is not in the reviewed overlay of library globals:
// declare function atob(data: string): string;.
// `atob`, not in the reviewed overlay of library globals.
export function bytes(data: string): number {
  return atob(data).length;
}
