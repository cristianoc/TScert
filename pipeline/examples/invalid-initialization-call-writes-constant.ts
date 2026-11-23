// The module's initialization allocates the object bound to `o`, and the
// module's function `setS` writes its field: TypeScript keeps `o.a`
// narrowed to `number` across the call, and the field holds "x" after it
// (run under Node: `out` is a string at `number`).
const o: { a: number | string } = { a: 1 };

function setS(): void {
  o.a = "x";
}

o.a = 1;
setS();
export const out: number = o.a;
