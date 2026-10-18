/** The compiler API as a host library (COMPILER-API.md): the reviewed
 * contract under which code reading TypeScript's trees and checker through
 * the package `typescript` is verified.
 *
 * The package's declarations are read on use, by the declaration reader's
 * rules for host declarations; this file states what a declaration cannot:
 * which package is the host, and which of its enums the contract reads as
 * values. Each entry is checked against the installed package by
 * `tests/compiler-api.mts`. */
import { createHash } from "node:crypto";
import { readdirSync, readFileSync, realpathSync } from "node:fs";
import { createRequire } from "node:module";
import { dirname, join, relative, sep } from "node:path";

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
 * (`node.generated.js:221`). The declaration reader omits each from its host
 * type's shape, so every read of it is a read of a member the type does not
 * state. */
export const allocatingMembers: readonly { owner: string; name: string; text: string }[] = [
  { owner: "Node", name: "jsDoc", text: "readonly jsDoc?: readonly Node[] | undefined;" },
];

/** The interfaces of the host package that are host types by themselves
 * (reading rule 1): `Node`, every node shape reaching it through `extends`,
 * `NodeArray`, and the sync API's `Type`, its sub-interfaces reaching it.
 * Every class the package declares is a host type too. */
export const hostTypeRoots: readonly string[] = ["Node", "NodeArray", "Type"];

/** The branded strings (COMPILER-API.md, reading rule 5): host-introduced
 * types whose values are strings the package produces. Read as `string` where
 * the client receives one; a host signature's parameter mentioning one is
 * refused (L5), since the calculus has no opaque primitive type to admit only
 * the package's own values. Each entry is its declaration as reviewed. */
export const brandedTypes: readonly { name: string; text: string }[] = [
  { name: "Path", text: "export type Path = string & {\n    __pathBrand: any;\n};" },
  { name: "__String", text: "export type __String = (string & {\n    __escapedIdentifier: void;\n}) | InternalSymbolName;" },
];

/** The host package's node list interface, read as a dense readonly array of
 * its elements (COMPILER-API.md, "Node lists in the model"), never through
 * its declaration. */
export const hostNodeList = "NodeArray";

/** The reviewed host declarations' digest (C0): the SHA-256 of every
 * `.d.ts` file under the audited installation's `dist/`, each its path from
 * the package root, a NUL, its bytes and a NUL, in path order, after the
 * package's version. A different digest is a different package, refused
 * until the contract is reviewed again. */
export const hostDeclarationsDigest = "16f2260fe0003d51dfb6b8503926ce01ff3e8afd3842a3351d3d544c1e81d492";

/** The digest of the declarations of the package installed at `root`. */
export function declarationsDigest(root: string): string {
  const hash = createHash("sha256");
  const manifest: unknown = JSON.parse(readFileSync(join(root, "package.json"), "utf8"));
  const version = typeof manifest === "object" && manifest !== null && "version" in manifest ? String(manifest.version) : "";
  hash.update(`${version}\0`);
  const files: string[] = [];
  const walk = (directory: string): void => {
    for (const entry of readdirSync(directory, { withFileTypes: true })) {
      const path = join(directory, entry.name);
      if (entry.isDirectory()) walk(path);
      else if (entry.name.endsWith(".d.ts")) files.push(relative(root, path).split(sep).join("/"));
    }
  };
  walk(join(root, "dist"));
  for (const file of files.sort()) {
    hash.update(`${file}\0`);
    hash.update(readFileSync(join(root, file)));
    hash.update("\0");
  }
  return hash.digest("hex");
}

/** The host installation: the package directory and whether its digest is
 * checked. */
type Installation = { root: string; checked: boolean };

/** The audited installation: the package `typescript` the front end itself
 * resolves (`tools/package-lock.json` pins it), its real path. */
let audited: Installation | null = null;
/** A stand-in installation a test supplies (`useHostInstallationForTests`);
 * no entry point of the pipeline sets it. */
let standIn: Installation | null = null;
let digestChecked = false;

function installation(): Installation {
  if (standIn) return standIn;
  audited ??= { root: realpathSync(dirname(createRequire(import.meta.url).resolve(`${hostPackage.name}/package.json`))),
    checked: true };
  return audited;
}

/** Tests only: read the package at `root` as the host package, its digest
 * unchecked, until called again with null. */
export function useHostInstallationForTests(root: string | null): void {
  standIn = root === null ? null : { root: realpathSync(root), checked: false };
}

/** Whether `file` is a declaration of the host package: a file of the
 * audited installation, whose declarations have the reviewed digest. A
 * package elsewhere, whatever its manifest names, is no host. */
export function isHostFile(file: string): boolean {
  let real: string;
  try {
    real = realpathSync(file);
  } catch {
    return false;
  }
  const host = installation();
  if (!real.startsWith(host.root + sep)) return false;
  if (host.checked && !digestChecked) {
    const digest = declarationsDigest(host.root);
    if (digest !== hostDeclarationsDigest)
      throw Error(`the host package at ${host.root} is not the reviewed one: its declarations' digest is ${digest}, ` +
        `the contract was reviewed against ${hostDeclarationsDigest}`);
    digestChecked = true;
  }
  return true;
}
