/** The compiler API as a host library (COMPILER-API.md): the reviewed
 * contract under which code reading TypeScript's trees and checker through
 * the package `typescript` is verified.
 *
 * The package's declarations are read on use, by the declaration reader's
 * rules for host declarations; this file states what a declaration cannot:
 * which package is the host, and which of its enums the contract reads as
 * values. Each entry is checked against the installed package by
 * `tests/compiler-api.mts`. */
import { readFileSync, realpathSync } from "node:fs";
import { dirname, join } from "node:path";

/** The host package: its name and the version the contract was reviewed
 * against (`tools/package-lock.json`). */
export const hostPackage = { name: "typescript", version: "7.0.2" } as const;

/** The host enums the contract reads as values: each a `declare enum` the
 * package exports through its `#enums/*` imports, its declaration file
 * `dist/enums/<file>.enum.d.ts` and its runtime object, which Node loads
 * under the `default` condition, `dist/enums/<file>.js`. C1 checks that the
 * runtime object holds exactly the members and values the declaration
 * states (T5). An enum of the package outside this list is refused where
 * it is read as a value: `CharacterCodes.ogham` is 5760 in its declaration
 * and 5765 at run time. */
export const hostEnums: readonly { name: string; file: string }[] = [
  { name: "SyntaxKind", file: "syntaxKind" },
  { name: "NodeFlags", file: "nodeFlags" },
  { name: "TypeFlags", file: "typeFlags" },
  { name: "SymbolFlags", file: "symbolFlags" },
  { name: "SignatureKind", file: "signatureKind" },
  { name: "ElementFlags", file: "elementFlags" },
  { name: "DiagnosticCategory", file: "diagnosticCategory" },
];

/** The members of host types whose read allocates (reading rule 1), each
 * with the interface declaring it and the declaration text it was reviewed
 * against: `jsDoc` builds a fresh array on each read
 * (`node.generated.js:221`), so it is refused at its read. */
export const allocatingMembers: readonly { owner: string; name: string; text: string }[] = [
  { owner: "Node", name: "jsDoc", text: "readonly jsDoc?: readonly Node[] | undefined;" },
];

/** The interfaces of the host package that are host types by themselves
 * (reading rule 1): `Node`, every node shape reaching it through `extends`,
 * `NodeArray`, and the sync API's `Type`, its sub-interfaces reaching it.
 * Every class the package declares is a host type too. */
export const hostTypeRoots: readonly string[] = ["Node", "NodeArray", "Type"];

const packageOf = new Map<string, string | null>();

/** The root directory of the package that holds `file`: the directory of the
 * nearest `package.json` above it, or null where none is. */
function packageRoot(file: string): string | null {
  let directory = dirname(file);
  const visited: string[] = [];
  let found: string | null = null;
  for (;;) {
    const known = packageOf.get(directory);
    if (known !== undefined) {
      found = known;
      break;
    }
    visited.push(directory);
    try {
      readFileSync(join(directory, "package.json"));
      found = directory;
      break;
    } catch {
      const parent = dirname(directory);
      if (parent === directory) break;
      directory = parent;
    }
  }
  for (const v of visited) packageOf.set(v, found);
  return found;
}

/** Whether `file` belongs to the host package at the reviewed version: its
 * nearest `package.json` names `hostPackage`. */
export function isHostFile(file: string): boolean {
  let real: string;
  try {
    real = realpathSync(file);
  } catch {
    return false;
  }
  const root = packageRoot(real);
  if (!root) return false;
  const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
  return typeof manifest === "object" && manifest !== null &&
    "name" in manifest && manifest.name === hostPackage.name &&
    "version" in manifest && manifest.version === hostPackage.version;
}
