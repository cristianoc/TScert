// The facts the claims document proposes at each loop's head, printed as the
// `@invariant` clause a source would write before the loop (ARITHMETIC.md,
// "The clause language"), over source names:
//   node dev/single-pass-invariants.mts <claims.json> <source.ts> [function]
// A loop head is an entry whose position starts a `for`, `while` or `do`
// statement, or a `for` loop's condition. Per loop: its line, the clause, and how many facts it states;
// a fact with no written form (region separation, `apart`) is counted apart.
import { readFileSync } from "node:fs";
import { isJsonList, isJsonObject, type JsonRead, type JsonValue } from "../tools/calculus.mts";

const [claimsPath, sourcePath, only] = process.argv.slice(2);
if (claimsPath === undefined || sourcePath === undefined) {
  process.stderr.write("usage: node dev/single-pass-invariants.mts <claims.json> <source.ts> [function]\n");
  process.exit(2);
}
const source = readFileSync(sourcePath, "utf8");
const doc: JsonValue = JSON.parse(readFileSync(claimsPath, "utf8"));
const field = (v: JsonRead, k: string): JsonRead => (isJsonObject(v) ? v[k] : undefined);
const list = (v: JsonRead): readonly JsonValue[] => (isJsonList(v) ? v : []);
const str = (v: JsonRead): string => (typeof v === "string" ? v : "");
const num = (v: JsonRead): number => (typeof v === "number" ? v : 0);

const path = (x: JsonRead): string => [str(field(x, "name")), ...list(field(x, "path")).map(str)].join(".");
const term = (x: JsonRead): string => (str(field(x, "term")) === "value" ? path(x) : `${path(x)}.length`);
const guards = (gs: JsonRead): string =>
  list(gs).map((g) => `${path(g)} === ${str(field(g, "tag")) === "undefined" ? "undefined" : str(field(g, "tag"))} || `).join("");
function linear(f: JsonRead): string {
  const either = field(f, "either");
  if (either !== undefined) return `(${linear(field(either, "left"))} || ${linear(field(either, "right"))})`;
  // A term with coefficient 0 states only that its value is a safe integer.
  const terms = list(field(f, "terms"));
  if (terms.length === 1 && num(field(terms[0], "coefficient")) === 0) return `${guards(field(f, "guards"))}safeInteger(${term(terms[0])})`;
  const parts = terms.map((t, i) => {
    const c = num(field(t, "coefficient"));
    const sign = c < 0 ? (i === 0 ? "-" : " - ") : i === 0 ? "" : " + ";
    const k = Math.abs(c);
    return `${sign}${k === 1 ? "" : `${k} * `}${term(t)}`;
  });
  return `${guards(field(f, "guards"))}${parts.join("") || "0"} <= ${num(field(f, "bound"))}`;
}
const line = (at: number): number => source.slice(0, at).split("\n").length;
// A `for` loop's head is its condition, the entry just after its first `;`.
const isLoop = (at: number): boolean => /^((for|while|do)\b|;)/.test(source.slice(at, at + 6));

let loops: number = 0, facts: number = 0, unwritten: number = 0;
for (const fn of list(field(doc, "functions"))) {
  if (only !== undefined && str(field(fn, "name")) !== only) continue;
  for (const e of list(field(fn, "entries"))) {
    const at = num(field(e, "start"));
    if (!isLoop(at)) continue;
    const clauses = [
      ...list(field(e, "facts")).map(linear),
      ...list(field(e, "bounds")).map((b) =>
        `${str(field(b, "index"))} ${field(b, "strict") === true ? "<" : "<="} ${str(field(b, "array"))}.length`),
      ...list(field(e, "storesApart")).map((s) =>
        `${guards(field(s, "guards"))}${[str(field(s, "name")), ...list(field(s, "path")).map(str)].join(".")} !== ` +
        `${[str(field(s, "other")), ...list(field(s, "otherPath")).map(str)].join(".")}`),
      ...list(field(e, "quantified")).map((q) => `forall k < ${term(field(q, "stop"))} of ${path(q)}: ${JSON.stringify(field(q, "body"))}`),
    ];
    const apart = list(field(e, "apart")).length;
    loops++; facts += clauses.length; unwritten += apart;
    process.stdout.write(`${str(field(fn, "name"))} line ${line(at)}: ${clauses.length} facts${apart ? `, ${apart} apart (no written form)` : ""}\n`);
    // A guarded clause is its own tag: guards begin a clause (`K ::= G || K`).
    const plain = clauses.filter((c) => !/ === (null|undefined|true|false) \|\| /.test(c));
    const guarded = clauses.filter((c) => !plain.includes(c));
    const tags = [...(plain.length ? [plain.join(" && ")] : []), ...guarded];
    process.stdout.write(`/** ${tags.map((t) => `@invariant ${t}`).join("\n *  ")} */\n`);
  }
}
process.stdout.write(`${loops} loops, ${facts} facts, ${unwritten} with no written form\n`);
