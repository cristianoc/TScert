#!/usr/bin/env node
/**
 * Everywhere the node side tells the compiler not to check something, found
 * with the compiler the project builds with. `tsc` has no option for any of
 * these, and `typescript-eslint` cannot check them here because it does not
 * support TypeScript 7.
 *
 * Three ways of saying it, one report:
 *
 * A written `any` is not a weaker type, it is the absence of one: the compiler
 * stops reading the expression, so a field that does not exist reads as
 * `undefined` rather than failing. That is not hypothetical here — two checks
 * on type-parameter defaults read `tp.default` through an `any` for as long as
 * they existed, and never once fired.
 *
 * An `as` says the value is something the compiler cannot see that it is, and
 * a `!` says it is there when the compiler cannot see that either. Both are
 * assertions: nothing checks them, and a decoder that establishes the fact is
 * what they stand in for.
 *
 * `as const` and `as unknown` are not counted: they assert nothing about a
 * value, the first only asking for the literal type of what is written there,
 * the second widening to the type every value has.
 *
 * Each one written must carry its reason, a comment `// asserted: REASON` at
 * the end of its line or alone on the line above: a decoder's last line, where
 * the checks it just ran become the type it returns, or an assertion whose
 * check would cost more than it guards. One without a reason is an error, and
 * the command fails.
 */
import fs from "node:fs";
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import { openText } from "./fragment-parse.mts";

/** What was written, which of the three it is, and the reason written with it. */
type Kind = "any" | "as" | "!";
interface Written {
  file: string;
  line: number;
  column: number;
  kind: Kind;
  text: string;
  reason: string | null;
}

/** `x as const` or `x as unknown`: an `as` asserting nothing. */
function assertsNothing(node: ts.Node): boolean {
  if (!ts.isAsExpression(node)) return false;
  const type = node.type;
  return type.kind === ts.SyntaxKind.UnknownKeyword ||
    (ts.isTypeReferenceNode(type) && ts.isIdentifier(type.typeName) && type.typeName.text === "const");
}

const KINDS: [number, Kind][] = [
  [ts.SyntaxKind.AnyKeyword, "any"],
  [ts.SyntaxKind.AsExpression, "as"],
  [ts.SyntaxKind.NonNullExpression, "!"],
];

const REASON = /\/\/ asserted: (\S.*)$/;

/** The reason given for what is written on `line` (0-based) of `lines`: at
 * the end of that line, or as the whole of the line above. */
function reasonAt(lines: string[], line: number): string | null {
  const own = REASON.exec(lines[line] ?? "");
  if (own?.[1]) return own[1];
  const above = (lines[line - 1] ?? "").trim();
  const alone = above.startsWith("//") ? REASON.exec(above) : null;
  return alone?.[1] ?? null;
}

/** Each one written in a file, in source order. */
function writtenAny(file: string): Written[] {
  const text = fs.readFileSync(file, "utf8");
  const lines = text.split("\n");
  const source = openText(path.resolve(file), text);
  const found: Written[] = [];
  const walk = (node: ts.Node): void => {
    const kind = KINDS.find(([syntax]) => syntax === node.kind)?.[1];
    if (kind !== undefined && !assertsNothing(node)) {
      const at = source.getLineAndCharacterOfPosition(node.getStart(source));
      found.push({
        file,
        line: at.line + 1,
        column: at.character + 1,
        kind,
        text: lines[at.line]?.trim() ?? "",
        reason: reasonAt(lines, at.line),
      });
    }
    node.forEachChild(walk);
  };
  source.forEachChild(walk);
  return found;
}

// The node side: every directory tools/tsconfig.json includes.
const roots = [".", "tools", "tests", "pipeline"];
const files = roots.flatMap((dir) =>
  fs
    .readdirSync(dir)
    .filter((name) => name.endsWith(".mts") || name.endsWith(".ts"))
    .map((name) => `${dir}/${name}`),
);
const found = files.flatMap(writtenAny);
const unreasoned = found.filter((w) => w.reason === null);
const show = (w: Written) => `${w.file}:${w.line}:${w.column}  [${w.kind}]  ${w.text}`;
if (process.argv.includes("--list"))
  for (const w of found) console.log(`${show(w)}${w.reason === null ? "" : `\n    asserted: ${w.reason}`}`);
else for (const w of unreasoned) console.log(`no reason: ${show(w)}`);
const counts = KINDS.map(([, kind]) => `${found.filter((w) => w.kind === kind).length} \`${kind}\``);
console.log(`\n${counts.join(", ")} in ${new Set(found.map((w) => w.file)).size} of ${files.length} files;` +
  ` ${found.length - unreasoned.length} with a reason, ${unreasoned.length} without`);
process.exitCode = unreasoned.length ? 1 : 0;
