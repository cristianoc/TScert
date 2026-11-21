import { createHash } from "node:crypto";
import { readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";
import { isJsonList, isJsonObject, type JsonRead } from "../tools/calculus.mts";
import type { Change, Frame } from "../tools/declaration-types.mts";

export const digest = (path: string): string => createHash("sha256").update(readFileSync(path)).digest("hex");
export const read = (path: string): JsonRead => JSON.parse(readFileSync(path, "utf8"));
export function list(value: JsonRead): readonly JsonRead[] {
  if (!isJsonList(value)) throw Error("expected an array");
  return value;
}
export function object(value: JsonRead): { readonly [name: string]: JsonRead } {
  if (!isJsonObject(value)) throw Error("expected an object");
  return value;
}
export function string(value: JsonRead): string {
  if (typeof value !== "string") throw Error("expected a string");
  return value;
}

export function checkedFrame(value: JsonRead): Frame {
  const classes = ["value", "array", "view"];
  const entries = list(value);
  if (entries.length !== classes.length) throw Error("expected one frame entry per class");
  return entries.map((entry, i) => {
    const { region, change } = object(entry);
    const cls = object(object(region).cls);
    function grade(v: JsonRead): Change {
      switch (v) {
        case "keep": case "init": case "scalar": case "extend": case "grow": case "any": return v;
        default: throw Error("expected a change grade");
      }
    }
    if (classes.some((c) => cls[c] !== (c === classes[i]))) throw Error("unexpected frame class");
    return { region: { cls: { value: i === 0, array: i === 1, view: i === 2 } }, change: grade(change) };
  });
}

export const declarationName = (file: string): string => file.replace(/\.ts$/, ".d.ts");
function declarationFiles(dir: string): string[] {
  return readdirSync(dir, { recursive: true, withFileTypes: true })
    .filter((entry) => entry.isFile() && entry.name.endsWith(".d.ts"))
    .map((entry) => join(entry.parentPath, entry.name)).sort();
}

export function declarationDigests(dir: string): Record<string, string> {
  return Object.fromEntries(declarationFiles(dir).map((file) => [file.slice(dir.length + 1), digest(file)]));
}
