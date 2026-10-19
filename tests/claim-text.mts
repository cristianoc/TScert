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
process.stdout.write("claim text: malformed index markers, an array atom and an array field shown as they arrived\n");
