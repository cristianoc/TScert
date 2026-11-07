// Execute the freshly generated wasm-bindgen module and a TypeScript caller.
// Usage: node execute-boundary.mts <generated-dir> <caller.ts> <number|bigint|none> [export]
import { readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

/** Dynamic module exports are inspected before reflection invokes them. */
function call(module: unknown, name: string, args: unknown[]): unknown {
  if (typeof module !== "object" || module === null) throw Error("not a module");
  const value: unknown = Reflect.get(module, name);
  if (typeof value !== "function") throw Error(`missing callable export ${name}`);
  return Reflect.apply(value, undefined, args);
}
const [generated, caller, kind, name = "doubled"] = process.argv.slice(2);
if (!generated || !caller || (kind !== "number" && kind !== "bigint" && kind !== "none"))
  throw Error("usage: execute-boundary.mts <generated-dir> <caller.ts> <number|bigint|none> [export]");
const glue: unknown = await import(pathToFileURL(resolve(generated, "lib.js")).href);
await call(glue, "default", [{ module_or_path: readFileSync(join(generated, "lib_bg.wasm")) }]);
const consumer: unknown = await import(pathToFileURL(resolve(caller)).href);
try {
  const value = call(consumer, name, kind === "none" ? [] : [kind === "number" ? 21 : 21n]);
  process.stdout.write(JSON.stringify({ status: "returned", type: typeof value, value: String(value) }) + "\n");
} catch (error) {
  if (!(error instanceof Error)) throw error;
  process.stdout.write(JSON.stringify({ status: "threw", name: error.name, message: error.message }) + "\n");
}
