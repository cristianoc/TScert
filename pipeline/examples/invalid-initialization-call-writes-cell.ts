// The module's initialization allocates the cell `m`, and the module's
// function `setS` writes it: TypeScript keeps `m` narrowed to `number`
// across the call, and the cell holds "x" after it (run under Node: `out`
// is a string at `number`).
let m: number | string = 1;

function setS(): void {
  m = "x";
}

setS();
export const out: number = m;
