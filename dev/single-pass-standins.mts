// Written-footprint stand-ins of the claims-free single pass
// (`verifier --verify-units 8`, docs/drafts/single-pass.md, "The claims-free
// front"): for a measurement, the footprint each of a file's functions, and
// each import read qualified, would state if its declaration wrote one, read
// from the producer's claims document. A stand-in is the annotation the owner
// would add; the pass reads it from `TSCERT_STANDINS`, apart from the source.
//   node dev/single-pass-standins.mts <claims.json> [name…]
import { readFileSync } from "node:fs";
import { isJsonList, isJsonObject, type JsonRead, type JsonValue } from "../tools/calculus.mts";

const field = (v: JsonRead, k: string): JsonRead => (isJsonObject(v) ? v[k] : undefined);
const list = (v: JsonRead): readonly JsonValue[] => (isJsonList(v) ? v : []);
const top = JSON.stringify({ value: "any", store: "any" });

/** One function's footprint, on-throw flag and result footprint, where any
 * states more than the ordinary effect. */
function standIn(f: JsonValue): JsonValue | null {
  const footprint = field(f, "footprint") ?? null;
  const resultFootprint = field(f, "resultFootprint") ?? null;
  const onThrow = field(f, "onThrow") === true;
  if (JSON.stringify(footprint) === top && !onThrow && JSON.stringify(resultFootprint) === top) return null;
  return { name: field(f, "name") ?? null, footprint, onThrow, resultFootprint };
}

/** The stand-ins of a claims document's functions and qualified imports;
 * with `names`, only those named. */
export function standIns(claimsPath: string, names?: readonly string[]): string {
  const doc: JsonValue = JSON.parse(readFileSync(claimsPath, "utf8"));
  const wanted = (s: JsonValue): boolean => names === undefined || names.includes(String(field(s, "name")));
  const functions = list(field(doc, "functions")).map(standIn).filter((s) => s !== null).filter(wanted);
  const modules = list(field(doc, "modules"));
  const imports = list(field(doc, "qualified")).flatMap((q) => {
    const m = modules.find((m) => field(m, "file") === field(q, "module"));
    const f = list(field(m, "functions")).find((f) => field(f, "name") === field(q, "name"));
    const s = f === undefined ? null : standIn(f);
    return s === null ? [] : [s];
  }).filter(wanted);
  return JSON.stringify({ functions, imports });
}

if (import.meta.filename === process.argv[1]) {
  const [claims, ...names] = process.argv.slice(2);
  if (claims === undefined) {
    process.stderr.write("usage: node dev/single-pass-standins.mts <claims.json> [name…]\n");
    process.exit(2);
  }
  process.stdout.write(standIns(claims, names.length === 0 ? undefined : names) + "\n");
}
