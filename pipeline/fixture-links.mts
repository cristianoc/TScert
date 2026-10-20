// The fixture projects' installations, as Node finds them: each project whose
// sources import a host package gets a `node_modules` link beside them, so
// that Node and TypeScript resolve the package's specifiers by one rule,
// with no `paths` between them. The links are generated, never committed
// (`.gitignore`), and created where missing by `make setup`, the case runner
// and the pipeline's suites; a single verification creates none.
//   node pipeline/fixture-links.mts
import { existsSync, lstatSync, mkdirSync, readlinkSync, realpathSync, symlinkSync } from "node:fs";
import { dirname, join, resolve, sep } from "node:path";

const here = import.meta.dirname;

/** Each link: its path, and the target it holds, relative to its directory. */
export const fixtureLinks: readonly (readonly [string, string])[] = [
  // The compiler API's examples and the modules their project holds import
  // the audited installation.
  ["examples/node_modules", "../../tools/node_modules"],
  ["compiler-api-project/node_modules", "../../tools/node_modules"],
  // A project's augmentation of the package's modules names them as Node does.
  ["host-augmented-project/node_modules", "../../tools/node_modules"],
  // The string-tagged stand-in's examples import the stand-in package by its
  // name, and its description names this installation.
  ["string-family-fixture-project/node_modules/string-family-fixture", "../../string-family-fixture"],
  // The compiler API's stand-ins, each the installation a test's
  // description names: the package of the host's name and version Node
  // finds from the project.
  ["host-fixture-project/node_modules/typescript", "../../host-fixture"],
  ["family-fixture-project/node_modules/typescript", "../../family-fixture"],
];

/** Create each link that is missing. Every link's directory, or its nearest
 * existing ancestor, must be a real directory inside the repository; a link
 * already in place must hold its target; any other file at a link's path,
 * or a link to another target, is an error. Every link is checked before
 * any is created, so a refusal changes nothing. */
export function linkFixtures(): void {
  const repository = realpathSync(join(here, ".."));
  const problems: string[] = [];
  const missing: (readonly [string, string])[] = [];
  for (const [path, target] of fixtureLinks) {
    const link = join(here, path);
    let directory = dirname(link);
    while (!existsSync(directory)) directory = dirname(directory);
    const stat = lstatSync(directory);
    const real = realpathSync(directory);
    if (!stat.isDirectory() || stat.isSymbolicLink() || (real !== repository && !real.startsWith(repository + sep)))
      problems.push(`${directory} is no real directory inside the repository`);
    else if (!lexists(link)) missing.push([link, target]);
    else if (!lstatSync(link).isSymbolicLink()) problems.push(`${link} is no link: remove it to link the fixtures' installation`);
    else if (readlinkSync(link) !== target)
      problems.push(`${link} links ${readlinkSync(link)}, not ${target}: remove it to link the fixtures' installation`);
  }
  if (problems.length) throw Error(`the fixtures' installation links are not set up, and nothing was changed:\n${problems.join("\n")}`);
  for (const [link, target] of missing) {
    mkdirSync(dirname(link), { recursive: true });
    try {
      symlinkSync(target, link);
    } catch (error) {
      // Another process linked it meanwhile.
      if (!(error instanceof Error && "code" in error && error.code === "EEXIST") || readlinkSync(link) !== target) throw error;
    }
  }
}

/** Whether anything, a dangling link included, is at `path`. */
function lexists(path: string): boolean {
  try {
    lstatSync(path);
    return true;
  } catch (error) {
    if (error instanceof Error && "code" in error && error.code === "ENOENT") return false;
    throw error;
  }
}

if (import.meta.filename === resolve(process.argv[1] ?? "")) linkFixtures();
