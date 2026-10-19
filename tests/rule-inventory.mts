#!/usr/bin/env node
/*
 * The docs describe a rule set; Lean declares one. This keeps them the same set.
 *
 * Three checks, in decreasing strength:
 *
 *  1. REQUEST-PROTOCOL.md enumerates the rule names a derivation node may use.
 *     That is an enumerative claim about `Rule`, so it is checked as set
 *     equality. The wire names are not written anywhere: `RequestJson.lean`
 *     derives ToJson/FromJson for `Rule`, so a constructor added to the
 *     inductive extends the protocol whether or not anyone writes it down.
 *  2. Every constructor of the rule-bearing inductives must be named, in
 *     backticks, somewhere in the documentation. This catches a rule that
 *     exists and is checked but that no document mentions at all. It cannot
 *     catch a rule whose prose is stale, and a constructor whose name is an
 *     ordinary word can be matched by unrelated prose, so the report prints
 *     where each name was found and the reader judges.
 *  3. The constructor signatures are snapshotted. Prose cannot be checked
 *     against a type, but a changed signature is a diff in the snapshot, which
 *     is the moment to re-read the rule's paragraph. Regenerate with
 *     UPDATE_EXPECT=1.
 *
 * Extraction is textual, over declarations this file names. It refuses rather
 * than guesses: an inductive it cannot find, or a line inside one it cannot
 * read, fails the suite instead of silently contributing no constructors.
 */
import assert from "node:assert/strict";
import { existsSync, readdirSync, readFileSync, writeFileSync } from "node:fs";
import { join } from "node:path";

const LEAN = "lean/Verification";
const DOCS = "docs";

/** A rule-bearing inductive: the acceptance language the docs describe. */
const DECLARATIONS: readonly { type: string; file: string; what: string }[] = [
  { type: "HasTyWith", file: "Programs/ProgramTyping.lean", what: "typing rules" },
  { type: "Rule", file: "Programs/ProgramCertificates.lean", what: "evidence rules" },
  {
    type: "ArrowCert",
    file: "Types/PositiveCertificates.lean",
    what: "arrow certificates",
  },
  {
    type: "StepEvidence",
    file: "Programs/HeapExpressionRules.lean",
    what: "effect evidence",
  },
];

interface Constructor {
  name: string;
  signature: string;
}

/** Drop `/- -/` comments, keeping every newline so line structure survives. */
function withoutBlockComments(text: string): string {
  let out = "";
  let depth = 0;
  for (let i = 0; i < text.length; i++) {
    const here = text.charAt(i);
    if (text.startsWith("/-", i)) {
      depth++;
      i++;
      continue;
    }
    if (depth > 0 && text.startsWith("-/", i)) {
      depth--;
      i++;
      continue;
    }
    if (depth === 0) out += here;
    else if (here === "\n") out += here;
  }
  assert.equal(depth, 0, "unterminated Lean block comment");
  return out;
}

/** The lines of `inductive <name>`: everything indented under its header. */
function declarationBody(text: string, name: string): string[] {
  const lines = text.split("\n");
  const start = lines.findIndex((l) =>
    new RegExp(`^inductive ${name}\\b`).test(l),
  );
  assert.notEqual(start, -1, `no \`inductive ${name}\` to read`);
  // A header may continue over several lines; the body follows its `where`.
  let header = start;
  while (header < lines.length && !/\bwhere\s*$/.test(lines[header])) header++;
  const body: string[] = [];
  for (const line of lines.slice(header + 1)) {
    if (line.trim() === "") continue;
    if (!/^\s/.test(line)) break;
    body.push(line);
  }
  assert(body.length > 0, `\`inductive ${name}\` has no indented body`);
  return body;
}

/** Split a constructor line at its top-level `|`, so `| a | b` gives two. */
function alternatives(line: string): string[] {
  const out: string[] = [];
  let current = "";
  let depth = 0;
  for (const ch of line) {
    if ("([{".includes(ch)) depth++;
    else if (")]}".includes(ch)) depth--;
    if (ch === "|" && depth === 0) {
      out.push(current);
      current = "";
      continue;
    }
    current += ch;
  }
  out.push(current);
  assert.equal(depth, 0, `unbalanced brackets in "${line.trim()}"`);
  // Text before the first `|` is indentation, never an alternative.
  return out.slice(1);
}

function constructors(file: string, type: string): Constructor[] {
  const source = withoutBlockComments(
    readFileSync(join(LEAN, file), "utf8"),
  );
  const out: Constructor[] = [];
  for (const raw of declarationBody(source, type)) {
    const line = raw.replace(/(^|\s)--.*$/, "").trimEnd();
    if (line.trim() === "") continue;
    if (/^\s*deriving\b/.test(line)) break;
    if (!/^\s*\|/.test(line)) {
      const previous = out.at(-1);
      assert(previous, `${type}: "${line.trim()}" precedes any constructor`);
      previous.signature += " " + line.trim();
      continue;
    }
    for (const alternative of alternatives(line)) {
      const named = /^\s*([A-Za-z_][A-Za-z0-9_']*)/.exec(alternative);
      assert(named, `${type}: no constructor name in "${alternative.trim()}"`);
      const name = named[1];
      assert(
        name !== undefined,
        `${type}: no constructor name in "${alternative.trim()}"`,
      );
      out.push({ name, signature: alternative.trim().replace(/\s+/g, " ") });
    }
  }
  return out;
}

const declared = new Map(
  DECLARATIONS.map((d) => [d.type, constructors(d.file, d.type)] as const),
);
const lookup = (type: string): Constructor[] => {
  const found = declared.get(type);
  assert(found, `${type} was not extracted`);
  return found;
};

const findings: string[] = [];
const report = (text: string): void => {
  findings.push(text);
  console.log("  ✗ " + text);
};

/* 1. The one enumerative claim the documentation makes. */
const PROTOCOL = "REQUEST-PROTOCOL.md";
const protocol = readFileSync(join(DOCS, PROTOCOL), "utf8");
const ANCHOR = "it applies:";
const anchored = protocol.indexOf(ANCHOR);
assert.notEqual(
  anchored,
  -1,
  `${PROTOCOL} no longer says what a node "${ANCHOR}"`,
);
/** The claim is one sentence: read to the first period outside backticks. */
const listed = (() => {
  const rest = protocol.slice(anchored + ANCHOR.length);
  let code = false;
  for (let i = 0; i < rest.length; i++) {
    const ch = rest.charAt(i);
    if (ch === "`") code = !code;
    else if (ch === "." && !code) return rest.slice(0, i);
  }
  throw Error(`${PROTOCOL}: the rule-name sentence does not end`);
})();
const documented = new Set([...listed.matchAll(/`([^`]+)`/g)].map((m) => m[1]));
const wire = lookup("Rule").map((c) => c.name);
console.log(
  `${PROTOCOL} enumerates ${documented.size}; \`Rule\` declares ${wire.length}.`,
);
for (const name of wire)
  if (!documented.has(name))
    report(
      `\`Rule.${name}\` is accepted on the wire and absent from ${PROTOCOL}`,
    );
for (const name of documented)
  if (!wire.includes(name))
    report(`${PROTOCOL} lists \`${name}\`, which \`Rule\` does not declare`);

/* 2. Every rule must be named somewhere. */
const corpus = [".", DOCS].flatMap((dir) =>
  readdirSync(dir)
    .filter((f) => f.endsWith(".md"))
    .map((f) => ({
      file: join(dir, f),
      lines: readFileSync(join(dir, f), "utf8").split("\n"),
    })),
);
/** Every place `name`, or a qualified `HasTy.name`, is written as code. A
 * constructor whose name is an ordinary word can be matched by prose about
 * something else, so the inventory prints all of them rather than the first. */
const mentions = (name: string): string[] => {
  const pattern = new RegExp("`(?:[A-Za-z_][A-Za-z0-9_]*\\.)*" + name + "`");
  const found: string[] = [];
  for (const { file, lines } of corpus)
    lines.forEach((l, i) => {
      if (pattern.test(l)) found.push(`${file}:${i + 1}`);
    });
  return found;
};
const inventory = process.argv.includes("--inventory");
console.log();
for (const { type, what } of DECLARATIONS) {
  const rules = lookup(type).map((c) => ({ ...c, where: mentions(c.name) }));
  const missing = rules.filter((c) => c.where.length === 0);
  console.log(
    `\`${type}\` (${what}): ${rules.length} declared, ` +
      `${rules.length - missing.length} named in the docs.`,
  );
  if (inventory)
    for (const c of rules)
      console.log(
        `    ${c.name.padEnd(14)} ${c.where.length ? c.where.slice(0, 3).join(" ") : "—"}` +
          (c.where.length > 3 ? ` (+${c.where.length - 3})` : ""),
      );
  for (const c of missing)
    report(`\`${type}.${c.name}\` is named in no document`);
}

/* 3. A changed signature is a diff, and a diff is a prompt to re-read the prose. */
const snapshot =
  DECLARATIONS.map(
    ({ type, file }) =>
      `${type}  (${file})\n` +
      lookup(type)
        .map((c) => `  ${c.signature}`)
        .join("\n"),
  ).join("\n\n") + "\n";
const SNAP = join("tests", "rule-inventory.snap");
console.log();
if (process.env.UPDATE_EXPECT === "1") {
  writeFileSync(SNAP, snapshot);
  console.log(`  signatures written: ${SNAP}`);
} else if (!existsSync(SNAP)) {
  report(`${SNAP} does not exist; regenerate with UPDATE_EXPECT=1`);
} else if (readFileSync(SNAP, "utf8") !== snapshot) {
  report(
    `${SNAP} is stale: a rule's signature changed, so re-read its paragraph`,
  );
} else {
  const total = DECLARATIONS.reduce((n, d) => n + lookup(d.type).length, 0);
  console.log(`  ${total} signatures match ${SNAP}`);
}

console.log();
if (findings.length === 0) {
  console.log(
    "  rule inventory checks passed; prose meaning still requires review",
  );
} else {
  console.log(`  ${findings.length} inventory checks failed`);
  process.exitCode = 1;
}
