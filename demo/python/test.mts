// End-to-end checks of the Python demo and its concrete CPython counterexamples.
// Usage: node demo/python/test.mts (after make build).
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdtempSync, readFileSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { Lowering, readNode } from "./lower.mts";

const here = import.meta.dirname;
const scratch = mkdtempSync(join(tmpdir(), "tscert-python-test-"));
function command(program: string, args: string[]): { status: number | null; out: string } {
  const result = spawnSync(program, args, { encoding: "utf8", timeout: 90_000 });
  if (result.error) throw result.error;
  return { status: result.status, out: result.stdout + result.stderr };
}
function verify(file: string, status: "verified" | "unverified" | "unsupported", detail?: RegExp): string {
  const result = command(process.execPath, [join(here, "verify.mts"), file]);
  assert.equal(result.status, status === "verified" ? 0 : 1, result.out);
  assert.ok(result.out.startsWith(`${status}: `), result.out);
  if (detail) assert.match(result.out, detail);
  return result.out;
}
for (const name of ["stale_title", "aliased_arguments"])
  verify(join(here, "examples", `${name}.py`), "unverified", /This return requires string/);
verify(join(here, "examples", "snapshot_title.py"), "verified");
verify(join(here, "examples", "hello.py"), "verified");
verify(join(here, "examples", "refused.py"), "unverified", /This return requires bigint/);
const runtime = command("python3", ["-I", "-B", join(here, "runtime.py")]);
assert.equal(runtime.status, 0, runtime.out);
process.stdout.write(runtime.out);

const source = readFileSync(join(here, "examples", "stale_title.py"), "utf8");
// Every restriction here guards a source-to-model distinction: actual
// built-in lookup, defaults executed on entry, required dictionary keys,
// lexical binding scope, or a field contract the wire must represent whole.
const boundaries: [string, string, RegExp][] = [
  ["shadow-guard", source.replace("display_title(payload: Payload)", "display_title(payload: Payload, isinstance: str)"), /rebinding the built-in/],
  ["default", source.replace("payload: Payload)", "payload: Payload = {})"), /defaults/],
  ["optional-key", source.replace("TypedDict):", "TypedDict, total=False):"), /total, non-generic TypedDict/],
  ["field-contract", source.replace("title: str | int", "title: list[str]"), /annotation of a field/],
  ["local-rebinding", source.replace("    if isinstance", "    alias = payload\n    if isinstance"), /rebinding alias/],
  ["branch-local", source.replace('        alias["title"] = 0', "        saved = payload"), /outer block/],
  ["computed-key", source.replace('alias["title"] = 0', 'alias[payload["title"]] = 0'), /literal string key/],
];
for (const [name, text, diagnostic] of boundaries) {
  const file = join(scratch, `${name}.py`);
  writeFileSync(file, text);
  verify(file, "unsupported", diagnostic);
}
// Spans must select the Python expression even after astral Unicode and
// CRLF. Check the independently serialized AST, then the final diagnostic.
const unicode = source.replace("    alias = payload", "    # 🦉 café\n    alias = payload").replaceAll("\n", "\r\n");
const file = join(scratch, "unicode.py");
writeFileSync(file, unicode);
const parsed = command("python3", ["-I", join(here, "py_ast.py"), file]);
assert.equal(parsed.status, 0, parsed.out);
const tree: unknown = JSON.parse(parsed.out);
const fragment = new Lowering(unicode).module(readNode(tree), file, "0".repeat(64));
assert.equal(fragment.functions.length, 1);
const out = verify(file, "unverified", /line 13: return payload\["title"\]/);
const span = /obligation at \[(\d+),(\d+)\)/.exec(out);
assert.ok(span, out);
assert.equal(unicode.slice(Number(span[1]), Number(span[2])), 'payload["title"]');
process.stdout.write(`Python demo: 5 verdicts, CPython witnesses, ${boundaries.length} source boundaries, Unicode/CRLF locations\n`);
