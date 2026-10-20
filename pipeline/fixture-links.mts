// The fixture projects' installations, as Node finds them: each project whose
// sources import a host package gets a `node_modules` link beside them, so
// that Node and TypeScript resolve the package's specifiers by one rule,
// with no `paths` between them. The links are generated, never committed
// (`.gitignore`), and created idempotently by `make setup`, the case runner
// and the pipeline's suites.
//   node pipeline/fixture-links.mts
import { lstatSync, mkdirSync, readlinkSync, symlinkSync, unlinkSync } from "node:fs";
import { dirname, join, resolve } from "node:path";

const here = import.meta.dirname;

/** Each link: its path, and the target it holds, relative to its directory. */
export const fixtureLinks: readonly (readonly [string, string])[] = [
  // The compiler API's examples and the modules their project holds import
  // the audited installation.
  ["examples/node_modules", "../../tools/node_modules"],
  ["compiler-api-project/node_modules", "../../tools/node_modules"],
  // A project's augmentation of the package's modules names them as Node does.
  ["host-augmented-project/node_modules", "../../tools/node_modules"],
  // The string-tagged stand-in's examples import the stand-in package by
  // the name it stands in for.
  ["string-family-fixture-project/node_modules/typescript", "../../string-family-fixture"],
];

/** Create each link that is missing; a link holding another target is
 * replaced; any other file at a link's path is an error. */
export function linkFixtures(): void {
  for (const [path, target] of fixtureLinks) {
    const link = join(here, path);
    let current: string | null = null;
    try {
      const stat = lstatSync(link);
      if (!stat.isSymbolicLink()) throw Error(`${link} is no link: remove it to let the fixtures link their installation`);
      current = readlinkSync(link);
    } catch (error) {
      if (!(error instanceof Error && "code" in error && error.code === "ENOENT")) throw error;
    }
    if (current === target) continue;
    if (current !== null) unlinkSync(link);
    mkdirSync(dirname(link), { recursive: true });
    try {
      symlinkSync(target, link);
    } catch (error) {
      // Another process linked it meanwhile.
      if (!(error instanceof Error && "code" in error && error.code === "EEXIST") || readlinkSync(link) !== target) throw error;
    }
  }
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) linkFixtures();
