// The claim printer (`tools/claim-text.mts`) on malformed producer output, which
// no source can make: a report shows what arrived, its malformed parts
// included, and marks the text as not the claim language's. No build needed.
import assert from "node:assert/strict";
import surface from "../tools/claim-text.mts";

const printed = (atom: Parameters<typeof surface.printType>[0]): { text: string; printable: boolean } =>
  surface.printType({ top: false, atoms: [atom] });

// Index markers that are no object are kept as the atom's metadata.
assert.deepEqual(printed({ a: "string", indexes: ["present"] }), {
  text: '«string» @{"indexes":["present"]}',
  printable: false,
});
// An array where an atom belongs is no atom of any kind.
assert.deepEqual(printed([]), { text: "«type»", printable: false });
// A record field that is no object is shown as it arrived.
assert.deepEqual(
  printed({ a: "record", fields: [[1]], indexes: { string: "absent", number: "absent", symbol: "absent" },
    call: "unknown", construct: "unknown", array: "unknown" }),
  { text: "{ (invalid field [1]) }", printable: false },
);
// A malformed field lacking a name keeps the enclosing addition's text.
assert.deepEqual(
  printed({ a: "record", fields: [{ read: { top: true, atoms: [] }, write: { top: true, atoms: [] } }],
    indexes: { string: "absent", number: "absent", symbol: "absent" },
    call: "unknown", construct: "unknown", array: "unknown" }),
  { text: "{ undefined: unknown }", printable: false },
);
// The numeric literal format requires text, even when Number(v) is finite.
for (const v of [[], [1], null, true, 1, { toString: 0 }]) {
  assert.deepEqual(printed({ a: "numberlit", v }), {
    text: "«numberlit»",
    printable: false,
  });
}
for (const v of ["01", " 2 ", "-0"]) {
  assert.equal(printed({ a: "numberlit", v }).text, v);
}
// A callable's complete function and record stay printable; absent parts
// keep the existing placeholders and mark the text as incomplete.
const number = { top: false, atoms: [{ a: "number" }] };
const fn = { a: "function", this: { top: true, atoms: [] }, params: [],
  result: number, construct: "unknown", array: "unknown" };
const bag = { a: "record", fields: [], indexes: { string: "absent", number: "absent", symbol: "absent" },
  call: "unknown", construct: "unknown", array: "unknown" };
assert.deepEqual(printed({ a: "callable", function: fn, bag }),
  { text: "(() => number) & {  }", printable: true });
assert.deepEqual(printed({ a: "callable", function: fn }),
  { text: "(() => number) & «type»", printable: false });
assert.deepEqual(printed({ a: "callable", bag }),
  { text: "(«type») & {  }", printable: false });
assert.deepEqual(printed({ a: "callable" }),
  { text: "(«type») & «type»", printable: false });
process.stdout.write("claim text: malformed index markers, an array atom and malformed fields, including missing callable parts, shown as they arrived\n");
