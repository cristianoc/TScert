// One fresh Wasm instance per observation, including each panic observation.
import { readFileSync } from "node:fs";
import { join, resolve } from "node:path";
import { pathToFileURL } from "node:url";

const [generated, name, ...integers] = process.argv.slice(2);
if (!generated || !name) throw Error("expected generated directory, export and integer arguments");
const glue: unknown = await import(pathToFileURL(resolve(generated, "lib.js")).href);
if (typeof glue !== "object" || glue === null) throw Error("expected module");
const initialize: unknown = Reflect.get(glue, "default");
const fn: unknown = Reflect.get(glue, name);
if (typeof initialize !== "function" || typeof fn !== "function") throw Error("expected module exports");
await Reflect.apply(initialize, undefined, [{ module_or_path: readFileSync(join(generated, "lib_bg.wasm")) }]);
try {
  const value: unknown = Reflect.apply(fn, undefined, integers.map(v => BigInt(v)));
  process.stdout.write(JSON.stringify({ status: "returned", type: typeof value, value: String(value) }) + "\n");
} catch (error) {
  if (!(error instanceof Error)) throw error;
  process.stdout.write(JSON.stringify({ status: "threw", name: error.name, message: error.message }) + "\n");
}
