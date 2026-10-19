// The capture-shape reading of regular expression literals
// (`tools/regexp-shape.mts`), against the host: a table of patterns whose
// shapes are known, the counterexamples to earlier readings, and a seeded
// differential fuzz over a grammar of every form the reading treats by mode.
// A violation is a group the reading says always takes part that a host match
// leaves `undefined`. No build needed.
import assert from "node:assert/strict";
import { regexpShape } from "../tools/regexp-shape.mts";

const always = (pattern: string, flags: string = ""): boolean[] | null => regexpShape(pattern, flags)?.always ?? null;

// Known shapes.
const table: [string, string, boolean[] | null][] = [
  ["(a)b", "", [true]],
  ["(a)|b", "", [false]],
  ["(a|b)", "", [true]],
  ["((a)|b)", "", [true, false]],
  ["(?:(a)|b)+", "", [false]],
  ["(?:x(a))+", "", [true]],
  ["(a)?", "", [false]],
  ["(a)*", "", [false]],
  ["(a){0,2}", "", [false]],
  ["(a){1}", "", [true]],
  ["(a){1,}?", "", [true]],
  ["(?=(a))a", "", [false]],
  ["(?!(a))b", "", [false]],
  ["(?<=(a))b", "", [false]],
  ["[(](a)", "", [true]],
  ["\\((a)", "", [true]],
  ["[]|(a)", "", [false]],
  ["[^](a)", "", [true]],
  ["[\\]](a)", "", [true]],
  ["^([A-Z][A-Za-z]*(?: [a-z][A-Za-z]*){0,3}(?: \\((?:[^()]|\\([^()]*\\))*\\))?):\\s*(.*)$", "", [true, true]],
  ["(?<n>a)|(?<n>b)", "", [false, false]],
  ["(?<\\u0061>x)", "u", [true]],
  ["(?<\\u{62}>x)", "u", [true]],
  ["(?i:a)(b)", "", null],
  ["[a--b](c)", "v", null],
];
for (const [pattern, flags, expected] of table)
  assert.deepEqual(always(pattern, flags), expected, `/${pattern}/${flags}`);
assert.equal(regexpShape("(?<n>a)", "")?.named, true);
assert.equal(regexpShape("(a)", "g")?.global, true);

// Counterexamples to earlier readings, each with the host's match.
const regressions: [string, string, string][] = [
  // `[^]` and `[]` are complete classes: the `|` is a disjunction.
  ["[^]|x[](a)", "", "z"],
  // Outside Unicode mode `\p`, `\u` and `\k` (without a named group) are
  // letters, and the braces hide nothing.
  ["\\p{a|x}(b)", "", "p{a"],
  ["\\u{a|x}(b)", "", "u{a"],
  ["\\k<a|x>(b)", "", "k<a"],
];
for (const [pattern, flags, input] of regressions) {
  const match = new RegExp(pattern, flags).exec(input);
  assert.ok(match && match[1] === undefined, `/${pattern}/ on ${JSON.stringify(input)} leaves group 1 unmatched`);
  assert.deepEqual(always(pattern, flags), [false], `/${pattern}/${flags}: group 1 may not take part`);
}
// A `\u` escape in a name is its code point: the host's key.
assert.deepEqual(Object.keys(/(?<a>x)/u.exec("x")?.groups ?? {}), ["a"]);

// The differential fuzz: random patterns over classes, escapes read by mode,
// named and unnamed groups, back references, lookarounds, quantifiers and
// alternatives, each matched against random strings, with and without `u`.
let seed: number = 0x5eed;
const random = (n: number): number => { // mulberry32
  seed = (seed + 0x6d2b79f5) | 0;
  let t = Math.imul(seed ^ (seed >>> 15), 1 | seed);
  t = (t + Math.imul(t ^ (t >>> 7), 61 | t)) ^ t;
  return ((t ^ (t >>> 14)) >>> 0) % n;
};
const pick = <T,>(xs: readonly T[]): T => {
  const x = xs[random(xs.length)];
  if (x === undefined) throw Error("empty choice");
  return x;
};
const atoms = ["a", "b", ".", "[^]", "[]", "[ab]", "[\\]a]", "\\(", "[(]", "x", "]", "}", "{", "a{", "{1,",
  "\\p{L}", "\\P{L}", "\\p{a|x}", "\\u{a|x}", "\\u0061", "\\u{62}", "\\k<n0>", "\\k<a|x>", "\\k", "\\c", "\\cA",
  "\\c|", "\\1", "\\0", "\\d", "\\b", "^", "$", "\\u", "\\u{", "\\p"];
// Half the patterns name no group, where `\k` is a letter outside Unicode mode.
let names: number = 0, named: boolean = true;
const generate = (depth: number): string => {
  const alternatives: string[] = [];
  for (let a = 0, n = random(4) === 0 ? 2 + random(2) : 1; a < n; a++) {
    let s = "";
    for (let t = 0, terms = 1 + random(3); t < terms; t++) {
      const k = depth > 3 ? 4 : random(8);
      const inner = (): string => generate(depth + 1);
      const atom = k === 0 ? `(${inner()})` : k === 1 ? `(?:${inner()})` : k === 2 ? (named ? `(?<n${names++}>${inner()})` : `(${inner()})`)
        : k === 3 ? `(?${pick(["=", "!", "<=", "<!"])}${inner()})` : pick(atoms);
      s += atom + pick(["", "", "", "?", "*", "+", "{0,2}", "{1,2}", "{2}", "+?"]);
    }
    alternatives.push(s);
  }
  return alternatives.join("|");
};
const alphabet = ["a", "b", "x", "(", "]", "z", "p", "{", "u", "k", "<", "}", "\u0001"];
const inputs = [""];
for (let i = 0; i < 200; i++) {
  let s = "";
  for (let j = 0, n = random(7); j < n; j++) s += pick(alphabet);
  inputs.push(s);
}
let patterns: number = 0, read: number = 0, alwaysGroups: number = 0, matches: number = 0;
const violations: string[] = [];
for (let i = 0; i < 20000; i++) {
  names = 0;
  named = random(2) === 0;
  const pattern = generate(0);
  for (const flags of ["", "u"]) {
    let host: RegExp;
    try { host = new RegExp(pattern, flags); } catch { continue; }
    patterns++;
    const shape = regexpShape(pattern, flags);
    if (!shape) continue;
    read++;
    alwaysGroups += shape.always.filter(Boolean).length;
    for (const input of inputs) {
      const m = host.exec(input);
      if (!m) continue;
      matches++;
      shape.always.forEach((a, k) => {
        if (a && m[k + 1] === undefined) violations.push(`/${pattern}/${flags} on ${JSON.stringify(input)}: group ${k + 1}`);
      });
      if (shape.named !== (m.groups !== undefined)) violations.push(`/${pattern}/${flags}: named groups`);
    }
  }
}
assert.deepEqual(violations.slice(0, 5), [], "no group the reading says always takes part is unmatched");
assert.ok(read > 5000 && alwaysGroups > 1000 && matches > 300000,
  `the fuzz exercises the reading: ${patterns} patterns, ${read} read, ${alwaysGroups} always-groups, ${matches} matches`);
console.log(`regexp shapes: ${table.length} known, ${regressions.length} regressions; fuzz ${patterns} patterns, ${read} read, ${alwaysGroups} always-groups, ${matches} matches, 0 violations`);
