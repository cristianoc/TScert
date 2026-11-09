// Checks the named functions of one file of a pretext checkout, each unit on
// its own, its neighbours read at their declared signatures:
//   node dev/check-functions.mts <pretext checkout> <file under src/> <fn1,fn2,…|*>
// `*` selects every unit of the file. The project is the checkout's own
// `tsconfig.json` with `types: []`, its tests left out. Prints one line per
// selected unit (status, members, first refusal line) and the seconds taken;
// exits 0 when every selected unit verifies.
import { mkdtempSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join, resolve } from "node:path";
import { checkApart, memberName } from "../pipeline/verify-source.mts";

const [checkout, file, names] = process.argv.slice(2);
if (checkout === undefined || file === undefined || names === undefined) {
  process.stderr.write("usage: node dev/check-functions.mts <pretext checkout> <file under src/> <fn1,fn2,…|*>\n");
  process.exit(2);
}
const root = resolve(checkout);
const project = mkdtempSync(join(tmpdir(), "check-functions-"));
writeFileSync(join(project, "tsconfig.json"), JSON.stringify({
  extends: join(root, "tsconfig.json"),
  compilerOptions: { types: [] },
  include: [join(root, "src/**/*.ts")],
  exclude: [join(root, "src/layout.test.ts")],
}, null, 2));
const all = names === "*";
const selected = all ? [] : names.split(",").filter((n) => n !== "");
const started = performance.now();
const result = await checkApart(join(root, "src", file), project, false, undefined, false,
  { omitted: [], select: all ? null : selected });
const units = (result.units ?? []).filter((u) => all || u.members.some((m) => selected.includes(memberName(m))));
const seen = new Set(units.flatMap((u) => u.members.map(memberName)));
let ok: boolean = result.units !== null && result.units !== undefined && units.length > 0;
for (const u of units) {
  if (u.status !== "verified") ok = false;
  const first = u.detail.split("\n").find((l) => l !== "" && !l.startsWith("obligation-diagnostic: ")) ?? "";
  console.log(`${u.status}\t${u.members.map(memberName).join(",")}\t${first.slice(0, 400)}`);
}
for (const n of selected) if (!seen.has(n)) { ok = false; console.log(`missing\t${n}\tno unit with this member`); }
if (result.units === null || result.units === undefined)
  console.log(`file-refused\t${result.status} ${result.phase ?? ""}\t${("detail" in result ? result.detail : "").split("\n")[0]?.slice(0, 400)}`);
console.log(`seconds\t${((performance.now() - started) / 1000).toFixed(1)}`);
process.exit(ok ? 0 : 1);
