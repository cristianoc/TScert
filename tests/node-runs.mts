// Examples and native-contract counterexamples run under Node: each result is
// what the case's outcome and the contracts it relies on say. No build needed.
import assert from "node:assert/strict";
import { runEmitted, runExample, runImporting } from "../pipeline/run-example.mts";

{
  for (const [file, call] of [
    ["invalid-native-find-mutation", "wrong([1, 2], { value: 0 })"],
    ["invalid-native-map-mutation", "wrong([1, 2], { value: 0 })"],
    ["invalid-map-primitive-method-mutation", `wrong(["a", "b"])`],
    ["invalid-native-join-coercion", "wrong({ value: 0 })"],
    ["invalid-native-sort-coercion", "wrong({ value: 0 })"],
    // What `%Iterate:ForIn%`'s step read is not what a later read finds.
    ["invalid-for-in-entry-call", "wrong({ a: 1 }, (v) => { delete v.a; })"],
    ["invalid-for-in-entry-field", "wrong({ inner: { a: 1, b: 2 } }, {})"],
    ["invalid-for-in-entry-rebound", "wrong({ a: 1, b: 2 }, {})"],
    // A function's `length` is not enumerable: its copy lacks it.
    ["invalid-spread-function-length", "arity((a, b) => a + b)"],
  ])
    assert.equal(runExample(file, call), undefined,
      `${file}: the actual source returns undefined despite its number or string contract`);
  // The pattern steps a string by code point: the first is the whole emoji.
  assert.equal(runExample("invalid-for-of-pattern-string", `firsts(["\\u{1F600}b"])`), "\u{1F600}",
    "invalid-for-of-pattern-string: the pattern binds a code point, not the first code unit");
  // The step calling the closure constant reads `LIMIT` before it holds a value.
  assert.throws(() => runExample("invalid-initialization-closure-call", "scaled(1)"), /before initialization/,
    "invalid-initialization-closure-call: the module throws a ReferenceError while it initializes");
  // `map` over stable callbacks returns dense arrays; a callback popping the
  // array it maps leaves a hole below the result's length.
  for (const [file, call, expected] of [
    ["map-stable-local-counter", `lengths(["ab", "c"])`, "[2,1]"],
    ["map-stable-push", "twice([1, 2])", "[[1,1],[2,2]]"],
    ["map-stable-element-write", `relabel(["a", "b"], ["p", "q"])`, '["p","p"]'],
    ["map-stable-element-write", "extend([1, 2], [5, 6])", "[6,7]"],
    ["map-stable-element-write", `firsts(["a", "b"])`, '["a","b"]'],
    ["map-stable-element-write", `appendAll([["k", ""]], ["a", "b"])`, "[1,1]"],
    ["map-stable-element-write", `seconds(["a", "b"], ["p", "q"])`, "[0,0]"],
    ["map-stable-element-write", "thirds([1, 2], [5, 6])", "[0,0]"],
    ["map-stable-helper", `counts(["ab", "c"])`, "[2,1]"],
    ["map-stable-outer-cell", "runningTotals([1, 2, 3])", "[1,3,6]"],
    ["map-stable-for-of", "doubled([[1, 2], [3]])", "[[2,4],[6]]"],
    ["map-stable-for-of", "proses([\"a `b` c\"])", '["a   c"]'],
    ["map-stable-collection-write", `seen(["a", "b"], new Map())`, '["a","b"]'],
    ["map-stable-set", `distinct([["a", "b", "a"], []])`, "[2,0]"],
    ["map-stable-spread", "padded([[1], [2, 3]])", "[[0,1,0],[0,2,3,0]]"],
    ["map-stable-named-callback", `[escapedAll(["a&b", "c"])]`, '["a&amp;b,c"]'],
    ["map-stable-named-declaration", `escapedAll(["a&b", "c"])`, '["a&amp;b","c"]'],
    ["map-stable-named-declaration", `widths(["ab", ""])`, "[2,0]"],
    ["map-stable-named-declaration", `joinedWidths(["ab", ""]).split(",")`, '["2","0"]'],
    ["map-stable-fresh-store", `heads(["a   b", " c "])`, '["a","c"]'],
    ["map-stable-fresh-store", `lasts(["a,b", "c"])`, '["b","c"]'],
    ["map-stable-fresh-store", `backwards(["a,bc", "c"])`, '["2,1","1"]'],
    ["map-stable-fresh-store", `sizes(["a   b", ""])`, "[2,0]"],
    ["map-stable-spread-call", "peaks([[1, 5], []])", "[5,0]"],
    ["map-stable-spread-call", "boxedPeaks([{ values: [3, 200] }])", "[3]"],
    ["map-stable-spread", `matchCounts(["aba", "b"])`, "[2,0]"],
    ["map-stable-spread", `distinctCounts([["a", "a"], []])`, "[1,0]"],
    ["map-stable-spread", `codePoints(["h\u00e9llo"])`, "[5]"],
    ["map-stable-optional-chain", `lastWords([[{ kind: "w", text: "a" }, { kind: "space", text: " " }], []])`, "[0,-1]"],
  ] as const)
    assert.equal(runExample(file, `((r) => Object.keys(r).length === r.length && JSON.stringify(r))(${call})`),
      expected, `${file}: the result is dense`);
  assert.equal(runExample("invalid-map-unstable-pop", "Object.keys(shrink([1, 2, 3])).length"), 2,
    "invalid-map-unstable-pop: the result has three positions, two present");
  assert.equal(runExample("map-unstable-pop-sparse", "Object.keys(shrink([1, 2, 3])).length"), 2,
    "map-unstable-pop-sparse: the result has three positions, two present");
  assert.equal(runExample("invalid-map-optional-pop", "Object.keys(drained([1, 2, 3], undefined)).length"), 2,
    "invalid-map-optional-pop: the result has three positions, two present");
  assert.equal(runExample("invalid-map-class-constructor-pop", "Object.keys(shrinkAll([1, 2, 3])).length"), 2,
    "invalid-map-class-constructor-pop: the result has three positions, two present");
  // The callback's `set` writes the map it captures.
  assert.equal(runExample("map-stable-collection-write",
    `(() => { const counts = new Map(); seen(["a", "a"], counts); return counts.get("a"); })()`), 2,
    "map-stable-collection-write: the callback's call writes the map");
  // The declaration called by the callback writes the counter it is passed.
  assert.equal(runExample("invalid-declaration-write-callback",
    `(() => { const counter = { n: 0 }; counted(["a", "b"], counter); return counter.n; })()`), 2,
    "invalid-declaration-write-callback: the declaration's call writes its parameter's field");
  // The `filter` callback's `push` writes the array it captures.
  assert.equal(runExample("map-stable-filter-push",
    `(() => { const kept = []; const r = words(["a b", "c"], kept); return kept.join() + ":" + Object.keys(r).length; })()`), "a,b,c:2",
    "map-stable-filter-push: the callback's call writes the array it captures, and the result is dense");
  assert.equal(runExample("invalid-map-named-callback-pop", "Object.keys(drained()).length"), 2,
    "invalid-map-named-callback-pop: the result has three positions, two present");
  assert.equal(runExample("map-literal-at-expected-element", `tokens(["\`a\`", "b"]).map(t => t.kind).join()`), "code,word",
    "map-literal-at-expected-element: each token's kind is one the type names");
  assert.equal(runExample("invalid-map-literal-outside-element", `tokens([" "])[0].kind`), "space",
    "invalid-map-literal-outside-element: the actual source returns a kind its type does not name");
  assert.equal(runExample("array-spread-named-union", `sizes({ kind: "dot" }, [{ kind: "line", length: 2 }])`), "0, 2",
    "array-spread-named-union: each element's size");
  assert.equal(runExample("field-contents-exclusion", `[described({ kind: "b" }), described({ kind: "c", v: "x" }), chained({ kind: "d", n: 2 })].join()`),
    "b,x,2", "field-contents-exclusion: each arm's value");
  assert.equal(runExample("invalid-field-contents-call", `wrong({ kind: "b" })`), undefined,
    "invalid-field-contents-call: the call rewrote kind, and the read finds no v");
  assert.equal(runExample("json-parse-data", `[numbers('[1, "x", 2]').join(), count(JSON.parse('{"a": 1, "b": [2]}'))].join(";")`),
    "1,0,2;2", "json-parse-data: the numbers, and the keys counted");
  assert.equal(runExample("invalid-json-parse-class", `typeof wrong()`), "function",
    "invalid-json-parse-class: the class's prototype method where parsed JSON is promised");
  assert.equal(runExample("invalid-json-parse-inherited", `typeof wrong("{}")`), "function",
    "invalid-json-parse-inherited: Object.prototype's toString where parsed JSON is promised");
  assert.equal(runExample("json-parse-own-proto", `value('{"__proto__": 1, "a": 2}', "a")`), 2,
    "json-parse-own-proto: the own __proto__ member set no prototype");
  assert.equal(runExample("invalid-field-equality-call", `(() => { const c = { kind: "a" }; return wrong(c, () => { c.kind = "b"; }); })()`), "b",
    "invalid-field-equality-call: the call's \"b\" where \"a\" is promised");
  assert.equal(runExample("invalid-guard-ternary-false-arm", `wrong("a")`), "a",
    "invalid-guard-ternary-false-arm: \"a\" where \"b\" is promised");
  assert.equal(runExample("invalid-guard-footprint", `(() => { const a = ["x", "y", "z"]; return 2 in wrong(a, a); })()`), false,
    "invalid-guard-footprint: the popping guard leaves a hole in map's result");
  assert.equal(runExample("guard-footprint", `[presences(["dense", 1]).join(), texts(["a", 2], new Set()).join()].join(";")`), "true,false;true,false",
    "guard-footprint: the guards' answers");
  assert.equal(runExample("invalid-json-parse-mutation", `typeof wrong('{"a": 1}')`), "function",
    "invalid-json-parse-mutation: the function the alias stored where parsed JSON is promised");
  assert.equal(runExample("array-test-disjunction", `[lengths([1], [2, 3]), pairs({ exprs: [1, "x"], conts: [0, 0] }).join()].join(";")`),
    "3;1,2", "array-test-disjunction: the lengths, and the map over the parsed array");
  assert.equal(runExample("invalid-array-test-disjunction", `wrong(1, [2])`), undefined,
    "invalid-array-test-disjunction: the number's length where a number is promised");
  assert.equal(runExample("invalid-field-alias-binder", `wrong({ value: 5 })`), undefined,
    "invalid-field-alias-binder: the parameter is number, and the object has no n");
  assert.equal(runExample("field-tag-read", `[size({ mapping: [1, 2] }), size({ mapping: "abc" }), count({ mapping: [7] })].join()`),
    "2,3,1", "field-tag-read: each mapping's size");
  assert.equal(runExample("invalid-field-tag-alias", `(() => { const o = { mapping: [1] }; return wrong(o, o); })()`), 5,
    "invalid-field-tag-alias: the write through the alias leaves a number where an array is promised");
  assert.equal(runExample("invalid-field-tag-call", `(() => { const o = { mapping: [1] }; return wrong(o, () => { o.mapping = 5; }); })()`), 5,
    "invalid-field-tag-call: the call leaves a number where an array is promised");
  assert.equal(runExample("dictionary-field-tag-read", `[size({ mapping: [1, "x", 2] }), label({ label: 4 })].join()`), "3,5",
    "dictionary-field-tag-read: the entries counted, and the label read past its test");
  assert.equal(runExample("invalid-dictionary-field-tag-call", `(() => { const o = { mapping: [1] }; return wrong(o, () => { o.mapping = "x"; }); })()`), "x",
    "invalid-dictionary-field-tag-call: the call leaves a string where an array is promised");
  assert.equal(runExample("exceptional-footprint-handler",
    `JSON.stringify([orZero([1, -1]), halvesOrSelf([4, 3]), relayedOrOne([-2, 2]), largest(1, 2)])`),
    "[[1,0],[2,3],[1,2],2]", "exceptional-footprint-handler: each handler's value");
  assert.equal(runExample("exceptional-footprint-fresh", `JSON.stringify(counts(["a,b", "c"], 2))`), "[0,2]",
    "exceptional-footprint-fresh: the handler pushes onto the fresh store");
  assert.equal(runExample("invalid-exceptional-handler-fact", `wrong({ v: "x" })`), undefined,
    "invalid-exceptional-handler-fact: the handler reads the field the throwing call cleared");
  assert.equal(runExample("invalid-exceptional-handler-mutation", "(r => r.length === 3 && !(2 in r))(wrong([1, 2, 3]))"), true,
    "invalid-exceptional-handler-mutation: the callee's pop before its throw leaves a hole");
  assert.equal(runExample("json-stringify-recursive", `JSON.stringify(serialized([{ a: { b: [] } }, 1]))`), '["{\\"a\\":{\\"b\\":[]}}","1"]',
    "json-stringify-recursive: each value serialized");
  // Each hook runs code of the client's that pops the array `map` visits, so
  // the result has a hole below its length.
  for (const [file, call] of [
    ["invalid-json-stringify-tojson", "(() => { const xs = [1, 2, 3]; return wrong(xs, { toJSON() { xs.pop(); return \"\"; } }); })()"],
    ["invalid-json-stringify-replacer", "(() => { const xs = [1, 2, 3]; return wrong(xs, (k, v) => { xs.pop(); return v; }); })()"],
    ["invalid-error-options", "(() => { const xs = [\"a\", \"b\", \"c\"]; return wrong(xs, { get cause() { xs.pop(); return 0; } }); })()"],
  ])
    assert.equal(runExample(file, `(r => r.length === 3 && !(2 in r))(${call})`), true,
      `${file}: the hook shrinks the mapped array, leaving a hole in the result`);
  // A `toJSON` an array owns, or an open record holds beside its declared
  // fields, is called by `JSON.stringify`, whose result is then the hook's
  // `undefined` where the declared result is a string.
  assert.equal(runExample("invalid-array-own-tojson", "typeof text(Object.assign([1, 2], { toJSON: () => undefined }))"),
    "undefined", "invalid-array-own-tojson: an array's own toJSON makes stringify return undefined");
  assert.equal(runExample("invalid-json-stringify-record", "typeof encode({ x: 1, y: 2, toJSON: () => undefined })"),
    "undefined", "invalid-json-stringify-record: a record's undeclared toJSON makes stringify return undefined");
  assert.equal(runExample("json-parse-stringify-tojson-member",
    `[roundTrip('{"a":{"toJSON":1},"b":[{"toJSON":"x"}]}'), wrapped('{"toJSON":[1]}')].join(" ")`),
    '{"a":{"toJSON":1},"b":[{"toJSON":"x"}]} [{"toJSON":[1]},{"toJSON":{"toJSON":[1]}}]',
    "json-parse-stringify-tojson-member: noncallable toJSON members round-trip");
  assert.equal(runExample("json-stringify-arrays", "[nested([[1, 2], []]), ...mixed([[1, { a: [true] }], null])].join(\" \")"),
    '[[1,2],[]] [[1,{"a":[true]}],[[1,{"a":[true]}],null]] [null,[null,null]]', "json-stringify-arrays: strings");
  assert.equal(runExample("map-stable-json-error", `JSON.stringify([quotedAll(["a"]), checkedAll([1, 2])])`),
    '[["\\"a\\""],[1,2]]', "map-stable-json-error: dense results");
  assert.throws(() => runExample("map-stable-json-error", "checkedAll([-1])"), /negative: -1/,
    "map-stable-json-error: the callback's throw is an outcome");
  assert.equal(runExample("typeof-named-union-open-arms", `[nonString({ size: 2 }), nonString("x"), joined({ a: 1, b: 2 }), joined("y")].join()`),
    "2,-1,3,-1", "typeof-named-union-open-arms: the undecided arms are read");
  assert.equal(runExample("typeof-named-union", `[showKey("a"), showKey({ symbol: 2 }), symbolOf({ symbol: 3 }), symbolOf("x")].join()`),
    "a,sym#2,3,-1", "typeof-named-union: each arm reads its own representation");
  assert.equal(runExample("logical-narrowing-past-reads",
    `[safeInteger(3), safeInteger("3"), shorter(1, "ab"), digits("12"), digits(12), nonNegative(4), untested(2, "a")].join()`),
    "true,false,true,true,false,4,true", "logical-narrowing-past-reads: each test guards its operand");
  assert.throws(() => runExample("logical-narrowing-past-reads", "nonNegative(-1)"), /non-negative/,
    "logical-narrowing-past-reads: a failed test throws");
  assert.equal(runExample("logical-truth-narrowing", `[guarded("b", "x"), chosen("a", "x"), chosen("b", ""), classOf("kw", "e")].join()`),
    'b,,,<span class="m-kw">e</span>', "logical-truth-narrowing: the guarded branches see `r` at \"b\"");
  assert.equal(runExample("invalid-logical-truth-or-narrowing", `chosen("a", "x")`), "a",
    "invalid-logical-truth-or-narrowing: the actual source returns \"a\" at a \"b\" contract");
  assert.equal(runExample("set-string-construction", `letters("banana", [1, 2])`), 5,
    "set-string-construction: three letters, an \"a\" and a 1");
  assert.equal(runExample("invalid-set-string-at-number", `typeof [...digits("12")][0]`), "string",
    "invalid-set-string-at-number: the set at number holds strings");
  assert.equal(runExample("conditional-empty-array", `lineCount("a\\nb", true) + lineCount("a", false)`), 2);
  assert.equal(runExample("invalid-conditional-empty-array", `typeof lengths("a")[0]`), "string",
    "invalid-conditional-empty-array: the elements are strings");
  // A member access of null or undefined throws a TypeError, in the order
  // `nullish-member-order` states.
  assert.equal(runExample("nullish-member-reads",
    `JSON.stringify([lastLines(["a", "b\\nc"]), trimEnd(["x", " "]), size({ n: 2, tags: [] }), upper("a"), caught(undefined), startsBlank([]), appended([["k", "v"]], "w")])`),
    '[["b","c"],["x"],2,"A",-1,false,"vw"]');
  for (const call of ["size(undefined)", "upper(null)", "tagAt(undefined, 0)", "lastLines([\"a\", undefined])", "appended([], \"w\")"])
    assert.throws(() => runExample("nullish-member-reads", call), /TypeError|Cannot read properties|Cannot set properties/, call);
  assert.equal(runExample("nullish-member-order",
    `(() => { const log = []; try { keyFirst(undefined, log); } catch (e) { return e instanceof TypeError && log.join(); } })()`), "key");
  assert.equal(runExample("nullish-member-order",
    `(() => { const log = []; try { argumentsSkipped(null, log); } catch (e) { return e instanceof TypeError && log.join(); } })()`), "");
  assert.equal(runExample("nullish-member-order",
    `(() => { const log = []; try { bumped(undefined, log); } catch (e) { return e instanceof TypeError && log.join(); } })()`), "key");
  assert.equal(runExample("nullish-member-order",
    `(() => { const log = []; return [optionalKey(undefined, log), log.length, optionalKey({ n: 3, tags: [] }, log), log.join()]; })().join()`), ",0,3,key");
  assert.throws(() => runExample("nullish-member-order", "chained(undefined)"), /Cannot read properties/);
  assert.equal(runExample("invalid-nullish-member-reads", `typeof label({ n: 1 })`), "number",
    "invalid-nullish-member-reads: the member is a number");
  assert.throws(() => runExample("nullish-member-write-refused", "reset(undefined)"), /Cannot set properties/);
  assert.equal(runExample("split-non-empty", `[firstLine("").subject, firstField("a;b", true), firstWord("x y"), lastLines(["a", "b\\nc"])].join("|")`), "|a|X|2");
  assert.equal(runExample("split-non-empty", `[lineCount("a\\nb", true), lineCount("a", false), popped("a,b"), aliasShrunk("a"), annotated("a,b")].join()`), "2,0,1,0,2");
  assert.equal(runExample("invalid-split-alias-shrink", `String(first("a"))`), "undefined");
  assert.equal(runExample("invalid-split-element-write", `String(first("a", undefined))`), "undefined");
  assert.equal(runExample("split-array-members", `joined("a,b")`), "a;b");
  assert.equal(runExample("invalid-split-empty-separator", `String(first(""))`), "undefined");
  assert.equal(runExample("invalid-split-limit", `[first("a,b", 0), first("a,b", 4294967296)].map(String).join()`), "undefined,undefined");
  assert.equal(runExample("invalid-split-string-separator", `String(first("", ""))`), "undefined");
  assert.equal(runExample("cell-truthiness-narrowing", `named(["x"], { name: "a", block: [] }) + blocks(["p", "q"], { name: "", block: [] })`), "atrue3");
  assert.equal(runExample("invalid-cell-truthiness-narrowing", `String(kept({ name: "a" }))`), "undefined",
    "invalid-cell-truthiness-narrowing: the reset cell returns undefined at a Section");
  assert.equal(runExample("logical-string-values", `[both("x"), both(""), either("", "y"), joined("a", "b"), fallback("", "c")].join()`), "1,0,1,b,c");
  assert.equal(runExample("invalid-logical-string-values", `JSON.stringify(length("", 3))`), '""',
    "invalid-logical-string-values: the empty string, no number");
  assert.equal(runExample("flat-map-union-returns", `shown(new Map([["Lean", "x"]]))`), "Lean=x");
  assert.equal(runExample("invalid-flat-map-union-returns", `JSON.stringify(shown(new Map([["Parts", "ab"]])))`), "[2]",
    "invalid-flat-map-union-returns: the elements are numbers");
  for (const file of ["invalid-map-fresh-alias", "invalid-map-fresh-join", "invalid-map-fresh-reassigned",
    "invalid-map-fresh-parameter"])
    assert.equal(runExample(file, `Object.keys(drained(["a", "b", "c"])).length`), 2,
      `${file}: the result has three positions, two present`);
  assert.equal(runExample("map-fresh-handler-refused", `JSON.stringify(firsts(["ab", "c"]))`), '["a",""]',
    "map-fresh-handler-refused: no throw, a dense result");
  assert.equal(runExample("invalid-map-handler-after-pop", `Object.keys(drained(["a", "b", "c"])).length`), 2,
    "invalid-map-handler-after-pop: the result has three positions, two present");
  for (const call of ["aliased", "joined", "reassigned", "dropped"])
    assert.equal(runExample("map-fresh-controls-sparse", `Object.keys(${call}(["a", "b", "c"])).length`), 2,
      `map-fresh-controls-sparse: ${call}'s result has three positions, two present`);
  assert.equal(runExample("invalid-map-spread-call-pop", "Object.keys(totals([[9]])).length"), 2,
    "invalid-map-spread-call-pop: the result has three positions, two present");
  assert.equal(runExample("invalid-map-spread-pop", "Object.keys(drained([1, 2, 3])).length"), 2,
    "invalid-map-spread-pop: the result has three positions, two present");
  assert.equal(runExample("invalid-map-filter-pop", "Object.keys(trimmed([\"a\", \"b\", \"c\"])).length"), 2,
    "invalid-map-filter-pop: the result has three positions, two present");
  assert.equal(runExample("find-stable-counter", `firstLong(["ab", "abcd", "x"])`), 6,
    "find-stable-counter: two visits and a found element of length four");
  // `map` passes the index to the constant's second parameter, whose `tag`
  // is undefined.
  assert.equal(runExample("invalid-annotated-constant-callback", `tags(["a"])[0]`), undefined,
    "invalid-annotated-constant-callback: the actual source returns undefined at string");
  // `test` of a global regex leaves `lastIndex` where the match ended: the
  // same line tests true, then false.
  assert.equal(runExample("map-stable-regexp-test", `marks(["ab", "ab"]).join()`), "true,false",
    "map-stable-regexp-test: the callback's call writes the regex it captures, and the result is dense");
  assert.equal(runExample("invalid-map-structural-replace", `(() => {
      const xs = ["a", "b", "c"];
      const out = rewrite(xs, { [Symbol.replace](s, r) { xs.pop(); return r; } });
      return out.length + ":" + Object.keys(out).length;
    })()`), "3:2", "invalid-map-structural-replace: a structural replacement pops the mapped array, leaving a hole");
  assert.equal(runExample("map-stable-regexp-replace", `JSON.stringify(collapsed(["a  b", "c\\td"]))`), '["a b","c d"]',
    "map-stable-regexp-replace: each call replaces through a regex the literal allocates");
  // `Number` of an object calls its `valueOf`, which here writes `seen.value`.
  // A guard's promise, which TypeScript does not check: lying guards, of a
  // primitive, through a parameter's default and of an object, a lying
  // assertion function, and a `false` outcome TypeScript narrows.
  assert.throws(() => runExample("invalid-type-guard-promise", "shout(1)"), /toUpperCase is not a function/,
    "invalid-type-guard-promise: the narrowed argument is a number");
  assert.equal(runExample("invalid-type-guard-undefined", "label(undefined)"), undefined,
    "invalid-type-guard-undefined: the narrowed argument is undefined, returned at string");
  assert.equal(runExample("invalid-type-guard-default", "f(undefined)"), undefined,
    "invalid-type-guard-default: the narrowed argument is undefined, returned at string");
  assert.equal(runExample("invalid-type-guard-method", "size(new Box(), 1)"), undefined,
    "invalid-type-guard-method: the narrowed argument is a number, whose length is undefined");
  assert.equal(runExample("invalid-type-guard-field-test", `radius({ kind: "square", side: 1 })`), undefined,
    "invalid-type-guard-field-test: the narrowed argument is a square, whose radius is undefined");
  assert.equal(runExample("invalid-type-guard-object", `radius({ kind: "square", side: 1 })`), undefined,
    "invalid-type-guard-object: the narrowed argument is a square, whose radius is undefined");
  assert.equal(runExample("invalid-assertion-promise", "length(true)"), undefined,
    "invalid-assertion-promise: the asserted argument is a Boolean, whose length is undefined");
  assert.throws(() => runExample("invalid-type-guard-false-branch", "shout(-1)"), /toUpperCase is not a function/,
    "invalid-type-guard-false-branch: the `false` outcome's argument is a number");
  assert.equal(runExample("invalid-number-object", `const seen = { value: 0 };
    wrong({ a: 1, valueOf() { seen.value = 1; return 1; } }, seen)`), 1,
    "invalid-number-object: the actual source returns 1 despite its 0 contract");
  // `Math.max`, `Math.min`, `String.fromCodePoint` and `String.fromCharCode`
  // convert an object argument, a spread's elements included, by its own
  // `valueOf`, and `Object.getOwnPropertyDescriptor` its key by its own
  // `toString`.
  for (const [file, argument] of [["invalid-math-max-object", "o"], ["invalid-math-min-spread-object", "[o]"],
    ["invalid-from-code-point-object", "o"], ["invalid-from-char-code-object", "o"]])
    assert.equal(runExample(file, `const seen = { value: 0 };
      const o = { valueOf() { seen.value = 1; return 1; } };
      wrong(${argument}, seen)`), 1, `${file}: the actual source returns 1 despite its 0 contract`);
  assert.equal(runExample("invalid-own-property-descriptor-key-object", `const seen = { value: 0 };
    wrong({}, { toString() { seen.value = 1; return "a"; } }, seen)`), 1,
    "invalid-own-property-descriptor-key-object: the actual source returns 1 despite its 0 contract");
  assert.equal(runExample("invalid-own-property-descriptor-value", `first({ a: "x" })`), "x",
    "invalid-own-property-descriptor-value: the descriptor's value is a string returned at number");
  assert.equal(runExample("invalid-record-index-named-key", "classOf([], 0)"), undefined,
    "invalid-record-index-named-key: the element past the end is undefined, whose member is undefined at string");
  // An imported unit certified as preserving gives `map` dense results; one
  // popping the array `map` reads leaves a hole below the result's length.
  assert.equal(runImporting("certified-value-import", `JSON.stringify([doubled([1, 2]), labels([1, -1]), tallies([5, 6], []), values([{ value: 3 }]), innerValues([{ inner: { value: 4 } }])])`),
    '[[2,4],["positive","other"],[1,2],[3],[4]]', "certified-value-import: the results are dense");
  assert.equal(runImporting("certified-mts-value-import", "JSON.stringify(doubled([1, 2]))"), "[2,4]",
    "certified-mts-value-import: the result is dense");
  assert.equal(runImporting("certified-nested-value-import", "JSON.stringify([quadrupled([1, 2]), doubledRows([[1], [2, 3]])])"),
    "[[4,8],[[2],[4,6]]]", "certified-nested-value-import: the results are dense");
  assert.equal(runImporting("certified-cycle-value-import", "JSON.stringify([parity(3), parity(4)])"), "[1,0]",
    "certified-cycle-value-import: the cycle runs");
  assert.equal(runImporting("invalid-certified-write-value-import", "((r) => Object.keys(r).length)(zeros([1, 2, 3]))"), 2,
    "invalid-certified-write-value-import: the result has three positions, two present");
  assert.equal(runExample("invalid-json-stringify-boxed-key",
    `(() => { let ran = false; const k = new String("a"); k.toString = () => { ran = true; return "a"; }; keyed({ a: 1 }, k); return ran; })()`),
    true, "invalid-json-stringify-boxed-key: a String object's toString runs inside JSON.stringify");
  assert.equal(runExample("invalid-json-stringify-boxed-space",
    `(() => { let ran = false; const n = new Number(2); n.valueOf = () => { ran = true; return 2; }; spaced(1, n); return ran; })()`),
    true, "invalid-json-stringify-boxed-space: a Number object's valueOf runs inside JSON.stringify");
  assert.equal(runImporting("invalid-preserving-arrow-value-import", "2 in shrunk([1, 2, 3])"), false,
    "invalid-preserving-arrow-value-import: the last index is a hole in map's result, its element popped before map reached it");
  assert.equal(runImporting("invalid-builtin-iterator-return-value-import", "first(new Map()) === undefined"), true,
    "invalid-builtin-iterator-return-value-import: a done step's value is undefined, returned at string");
  assert.equal(runExample("invalid-loop-head-own-name", `(() => { try { total([1]); return "none"; } catch (e) { return e instanceof ReferenceError; } })()`),
    true, "invalid-loop-head-own-name: the head's read of its own binding throws a ReferenceError");
  assert.equal(runExample("early-bindings", `JSON.stringify([count([5, 20, 30]), later(), perIteration([1, 2]), boxed(),
    (() => { try { tooSoon(); return "none"; } catch (e) { return e instanceof ReferenceError; } })()])`),
    "[2,2,3,1,true]", "early-bindings: the closures read the bindings once initialized, and a read before throws a ReferenceError");
  assert.equal(runExample("function-declaration-in-body-refused", `(() => { try { early(); return "none"; } catch (e) { return e instanceof ReferenceError; } })()`),
    true, "function-declaration-in-body-refused: the hoisted declaration's call reads the binding before its initialization");
  assert.equal(runExample("module-cells", "JSON.stringify([bump(), bump(), cached(), limited(), afterCall()])"), "[1,2,\"computed\",6,3]",
    "module-cells: the functions read and write the module's cells");
  assert.throws(() => runExample("module-cell-before-initialization", "sum()"), /ReferenceError|before initialization/,
    "module-cell-before-initialization: the initialization's call reads the cell before its declaration");
  assert.equal(runExample("invalid-module-cell-stale", "stale()"), "s",
    "invalid-module-cell-stale: the call's write reaches the read TypeScript narrowed to number");
  assert.equal(runExample("module-cell-saved-value", "saved()"), 0,
    "module-cell-saved-value: the constant keeps the value read before the write");
  assert.throws(() => runImporting("certified-cell-cycle-value-import", "total()"), /ReferenceError|before initialization/,
    "certified-cell-cycle-value-import: `left` runs before `right`'s cell is initialized");
  assert.equal(runExample("invalid-early-binding-stale", "stale()"), "s",
    "invalid-early-binding-stale: the closure's write reaches the read TypeScript narrowed to number");
  assert.equal(runImporting("invalid-node-path-join-callback",
    `(() => { const xs = ["a", "b", "c"]; const path = process.getBuiltinModule("node:path"); const normalize = path.posix.normalize; path.posix.normalize = (p) => { xs.pop(); return normalize(p); }; try { return 2 in parents(xs); } finally { path.posix.normalize = normalize; } })()`),
    false, "invalid-node-path-join-callback: a replaced posix.normalize shrinks the array map visits, leaving a hole");
  assert.equal(runImporting("invalid-node-path-resolve-callback",
    `(() => { const xs = ["a", "b", "c"]; process.cwd = () => { xs.pop(); return "/"; }; return 2 in absolute(xs); })()`),
    false, "invalid-node-path-resolve-callback: a replaced process.cwd shrinks the array map visits, leaving a hole");
  assert.equal(runImporting("invalid-node-exec-stdout-ignored", `run(["-e", ""])`), null,
    "invalid-node-exec-stdout-ignored: standard output not piped, the result is null at string");
  assert.equal(runExample("invalid-array-flat-map-value", "first()"), 1,
    "invalid-array-flat-map-value: the flattened array's number is returned at number[]");
  // An `env` value's `toString`, which the host runs before it reads `stdio`.
  assert.equal(runImporting("node-exec-restricted", `JSON.stringify(outputs(["process.stdout.write('a')", "process.exit(1)"]))`),
    '["a",""]', "node-exec-restricted: a failed command's throw caught as no output");
  assert.equal(runImporting("invalid-node-exec-restricted-spread", `(() => {
    const scripts = ["", "", ""];
    const r = wrong(scripts, { encoding: "utf8", env: { X: { toString() { scripts.pop(); return "x"; } } } });
    return r.length === 3 && !(2 in r);
  })()`), true, "invalid-node-exec-restricted-spread: an env value's toString shrinks the mapped array");
  assert.equal(runImporting("invalid-node-exec-env-object", `(() => {
    const stdio = ["pipe", "pipe", "ignore"];
    const X = { toString() { stdio[1] = "ignore"; return "x"; } };
    return run(["-e", ""], { encoding: "utf8", stdio, env: { PATH: process.env.PATH, X } });
  })()`), null, "invalid-node-exec-env-object: standard output ignored by an env value's toString, null at string");
  // The further actual a rest of strings takes is a number.
  assert.equal(runExample("invalid-rest-function-longer-signature", `wrong()("s", 1)`), 1,
    "invalid-rest-function-longer-signature: the number is returned at string");
  assert.equal(runExample("native-sort-contracts", "noCoercion({ value: 7 })"), 7,
    "an explicit comparator never invokes the element's invalid conversion method");
  // A spread copies an own enumerable symbol-keyed property, which a type
  // stating no symbol key says nothing of.
  assert.equal(runExample("invalid-object-spread-symbol-index", `const s = Symbol();
    typeof open({ [s]: "x" })[s]`), "string",
    "invalid-object-spread-symbol-index: the copy holds a string under a symbol its type says holds a number");
  // A spread of a string copies its code units at its indices; of a class
  // value, its static fields.
  assert.equal(runExample("spread-string-class", `JSON.stringify([afterSpread(), afterClass()])`),
    '[{"a":""},{"x":1,"b":2}]', "spread-string-class: the copies JavaScript makes");
  assert.equal(runExample("recursive-constants", "String(main())"), "139",
    "recursive-constants: each recursive constant computes what the model's self entry does");
  assert.equal(runExample("invalid-spread-string-index", `typeof overIndex("x")[0]`), "string",
    "invalid-spread-string-index: the string's code unit overwrites the number under `0`");
  assert.equal(runExample("invalid-spread-class-static", `class D { static a = "s"; }
    typeof overStatic(D).a`), "string",
    "invalid-spread-class-static: the class's static field overwrites the number under `a`");
  // A class value's own enumerable properties are its own static fields: a
  // copy, a rest and `Object.assign` take those, not its base's, which it
  // reads through its prototype and `for...in` visits; no static method.
  assert.equal(runExample("class-static-inheritance", `JSON.stringify([copy(), rest(), keys(), Derived.inherited])`),
    '[{"own":2,"two":3},{"two":3},"own,two,inherited,",1]', "class-static-inheritance: the copies JavaScript makes");
  assert.equal(runExample("invalid-class-static-inherited-copy", `String(copy().inherited)`), "undefined",
    "invalid-class-static-inherited-copy: the copy lacks the base's static field");
  assert.equal(runExample("invalid-class-static-inherited-rest", `String(rest().inherited)`), "undefined",
    "invalid-class-static-inherited-rest: the rest lacks the base's static field");
  assert.equal(runExample("invalid-class-static-method-copy", `typeof copy().m`), "undefined",
    "invalid-class-static-method-copy: the copy lacks the static method");
  assert.equal(runExample("invalid-class-static-assign", `JSON.stringify(assign())`), '{"own":2}',
    "invalid-class-static-assign: Object.assign copies the own static field only");
  assert.equal(runExample("invalid-typeof-inherited-statics", `String(make().inherited)`), "undefined",
    "invalid-typeof-inherited-statics: the returned class lacks the inherited static TypeScript promises");
  // External code receiving a class value may write its static field; the
  // test supplies `change`, which the example declares.
  assert.equal(runExample("invalid-class-static-generic-external", `function change(k) { k.limit = 9; }
    run()`), 9, "invalid-class-static-generic-external: the read finds the written value");
  assert.equal(runExample("class-static-variadic", `JSON.stringify([run, copy()])`), "[19,7]",
    "class-static-variadic: the construction and the copy JavaScript makes");
  // A write at a string key known only at run time: `__proto__` runs the
  // prototype's setter where the object does not own the key, which with a
  // number changes nothing, and writes the property where it owns it; with an
  // object value the setter replaces the prototype, which the pipeline refuses.
  assert.equal(runExample("computed-key-write", `JSON.stringify([
    Object.keys(dictionary("__proto__")).length,
    Object.getPrototypeOf(dictionary("__proto__")) === Object.prototype,
    copied(JSON.parse('{"__proto__": 1}'), "__proto__")["__proto__"],
    Object.keys(multiLiteral("b")), Object.keys(numberKey(1.5))])`), '[0,true,5,["b"],["1.5"]]',
    "computed-key-write: JavaScript's write, which the lowering's dispatch and copies follow");
  assert.equal(runExample("computed-key-proto-refused", `typeof setProto("__proto__").a`), "string",
    "computed-key-proto-refused: the setter makes the object value the prototype, whose string the dictionary reads");
  // Object.assign writes a function's `name`, which is not writable: it throws.
  assert.throws(() => runExample("invalid-function-fields-inferred", "named()"), /read only property 'name'/);
  // A dictionary beside an array: TypeScript types its `length` `number`, and
  // an empty one has none.
  assert.equal(runExample("invalid-length-array-or-dictionary", "size({})"), undefined,
    "invalid-length-array-or-dictionary: the actual source returns undefined despite its number contract");
  // A view of `length` reads an array's store length, after a push too.
  assert.equal(runExample("length-view", "lengths([4]) + grown(0)"), 9,
    "length-view: one, three, two and one, then two after the push");
  // A mutable tuple's `length` grows past its arity.
  assert.equal(runExample("invalid-length-view-tuple", "tupleLength(0)"), 2,
    "invalid-length-view-tuple: the view reads 2 despite its 1 contract");
  // A literal inherits `Object.prototype`'s members.
  assert.equal(runExample("invalid-dictionary-inherited-key", `typeof inherited("toString")`), "function",
    "invalid-dictionary-inherited-key: the read finds Object.prototype.toString despite its number contract");
  // A member access, an optional field and a pattern each find
  // `Object.prototype`'s member under its name where the object lacks it.
  assert.equal(runExample("invalid-dictionary-inherited-named", "typeof named()"), "function",
    "invalid-dictionary-inherited-named: the read finds Object.prototype.__defineGetter__");
  assert.equal(runExample("invalid-word-count", "next({}, \"constructor\")"), "function Object() { [native code] }1",
    "invalid-word-count: the count of `constructor` is a string");
  assert.equal(runExample("invalid-optional-inherited-key", "typeof optional({})"), "function",
    "invalid-optional-inherited-key: the read finds Object.prototype.toString");
  assert.equal(runExample("invalid-pattern-inherited-key", "typeof destructured({})"), "function",
    "invalid-pattern-inherited-key: the pattern finds Object.prototype.valueOf");
  // A non-null assertion on a read the object lacks the key of.
  assert.equal(runExample("invalid-non-null-index", "wrong({}, 0)"), undefined,
    "invalid-non-null-index: the read is undefined despite the assertion");
  // A callee generic over `Array<A>` reverses a tuple found in `unknown`.
  assert.throws(() => runExample("invalid-open-array-generic-call", "caller()"), /toFixed is not a function/);
  // An array's `length` is not one of its own enumerable properties.
  assert.equal(runExample("invalid-array-spread-length", "count([1, 2])"), undefined,
    "invalid-array-spread-length: the copy has no length despite its number contract");
  // `Array.isArray` on `unknown`: TypeScript reads the array as `any[]`.
  assert.equal(runExample("invalid-isarray-unknown-element", `typeof head(["a"])`), "string",
    "invalid-isarray-unknown-element: the actual source returns a string despite its number contract");
  assert.equal(runExample("invalid-isarray-unknown-push", `const a = ["a"]; grow(a); typeof a[1]`), "number",
    "invalid-isarray-unknown-push: a number lands in an array of strings");
  // A rest typed by an intersection: TypeScript accepts the call at an instance
  // where the declared contract holds no array, and the result is no boolean.
  assert.equal(runExample("invalid-rest-intersection", "typeof wrong()"), "number",
    "invalid-rest-intersection: the actual source returns a number despite its boolean contract");
  // A rest typed by a type parameter typing a value too: TypeScript infers a
  // tagged instance, and the collected array returned at it has no tag.
  assert.equal(runExample("invalid-rest-pack-value", "typeof wrong()"), "undefined",
    "invalid-rest-pack-value: the actual source returns undefined despite its string contract");
  // Forwarding through an ordinarily annotated binding does not prevent the
  // callback from shortening the source; the final map position remains a hole.
  assert.equal(runExample("invalid-callback-effect-forwarding",
    "const result = wrong([1, 2]); JSON.stringify([result.length, 0 in result, 1 in result])"), "[2,true,false]");
  // Reading a hole gives undefined, so it satisfies the input annotation. map
  // skips it even when the callback preserves the heap and returns a number.
  assert.equal(runExample("invalid-map-hole-coalescing", `const xs = [1, 2]; delete xs[1];
    const result = coalescingCallback(xs); JSON.stringify([result.length, 1 in result, result[1]])`), "[2,false,null]");
  // A key added in place is seen by every reference to the object, at its own
  // type: through a parameter (TypeScript accepts the module), through a
  // constant bound to the object, through a destructured binding.
  assert.equal(runExample("invalid-key-adding-parameter-write", "seen"), "number number");
  // A call between the write and the default stores a string in the cell.
  assert.equal(runExample("invalid-array-read-cell-call", "typeof clobbered()"), "string",
    "invalid-array-read-cell-call: the actual source returns a string despite its number contract");
  for (const [file, call] of [["invalid-object-growth-alias", "grow()"],
    ["invalid-object-growth-reused-name", "reusedName()"], ["invalid-computed-key-alias", `grow("x")`]] as const)
    assert.throws(() => runExample(file, call), /toUpperCase is not a function/,
      `${file}: the actual source reads the added number as a string`);
  // A function the caller supplies may own a `call` property: `.call` of it
  // is not the standard method, so the gate refuses these sources.
  assert.equal(runExample("invalid-call-provenance-spread",
    `overridden({ read: Object.assign(function () { return 1; }, { call: () => "wrong" }) }, { value: 1 })`), "wrong");
  assert.equal(runExample("invalid-call-provenance-assign",
    `probe(Object.assign(() => 1, { call: () => "wrong" }))`), "wrong");
  assert.equal(runExample("invalid-call-provenance-escape",
    `probe((f) => { Object.assign(f, { call: () => "wrong" }); })`), "wrong");
  assert.equal(runExample("invalid-call-provenance-module-argument",
    `probe((f) => { Object.assign(f, { call: () => "wrong" }); })`), "wrong");
  // An importing module's write, made before it calls `probe`.
  assert.equal(runExample("invalid-call-provenance-module-export",
    `Object.assign(g, { call: () => "wrong" }); probe()`), "wrong");
  assert.equal(runExample("invalid-direct-eval", "probe()"), "wrong");
  assert.equal(runExample("invalid-call-provenance-shadow-loop",
    `probe([Object.assign(() => 1, { call: () => "wrong" })])`), "wrong");
  assert.equal(runExample("invalid-call-provenance-shadow-catch",
    `probe(() => { throw Object.assign(() => 1, { call: () => "wrong" }); })`), "wrong");
  // Run as a script: `g` is the global object's property. Another script's
  // write through it is what the trusted assumption that only the file
  // writes its top-level bindings excludes.
  assert.equal(runExample("script-global-assumption",
    `probe(() => { globalThis.g.call = () => "wrong"; })`), "wrong");
  assert.equal(runExample("invalid-call-provenance-let",
    `reassigned(Object.assign(function () { return 1; }, { call: () => "wrong" }), { value: 1 })`), "wrong");
  // Sloppy code converts a receiver that is not an object: a primitive to a
  // wrapper object, `undefined` to the global object. The pipeline refuses
  // sloppy code reading `this` at such a receiver type.
  assert.equal(runExample("sloppy-this-primitive-refused", "typeof caller()"), "object",
    "sloppy-this-primitive-refused: the actual source returns a String object despite its string contract");
  assert.equal(runExample("sloppy-this-closure-refused", "typeof count()"), "undefined",
    "sloppy-this-closure-refused: the actual source reads the global object despite its number contract");
  // A subclass of Array is its instances' `constructor`, so `map` constructs
  // its result through the subclass (ArraySpeciesCreate): the construction the
  // ordinary array construction assumption excludes, and why the pipeline
  // refuses the class (`invalid-array-subclass`).
  assert.equal(runExample("invalid-array-subclass", `let built = 0;
    class Loud extends Counted { constructor(...args) { super(...args); built++; } }
    const xs = Loud.from([1, 2]); built = 0;
    const result = doubled(xs);
    JSON.stringify([result instanceof Loud, built, Array.from(result)]);`), "[true,1,[2,4]]");
  // An enum member known only at run time: its reverse mapping replaces a
  // member named by its value's key; a member read before it is written is
  // undefined, through a closure or a module function; its value is a
  // number, not a literal.
  assert.equal(runEmitted("invalid-enum-computed-nan-name", "one()"), "X");
  assert.equal(runEmitted("invalid-enum-computed-forward", "first()"), undefined);
  assert.equal(runEmitted("invalid-enum-computed-call-order", "first()"), undefined);
  assert.equal(runEmitted("invalid-enum-computed-literal", "wrong()"), 2);
  assert.equal(runEmitted("invalid-enum-proto-member", "proto() === Object.prototype"), true);
  // Exact observation uses the native identity and ordinary constructor.
  // A fulfilled record may acquire a then member before it is observed.
  assert.equal(await runExample("native-promise-record-observation", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    const observed = [await read(p), await readAll([p]), (await gather([p]))[0].n];
    Object.assign(p, { constructor: undefined });
    const changed = [await read(p), await readAll([p]), (await gather([p]))[0]];
    return JSON.stringify([observed, changed]);
  })()`), "[[1,1,1],[null,null,42]]");
  // A genuine native subclass has no own constructor, but its inherited
  // constructor differs from the current realm's ordinary Promise.
  assert.equal(await runExample("native-promise-record-observation", `(async () => {
    class Derived extends Promise {}
    const record = { n: 1 };
    const p = new Derived(resolve => resolve(record));
    Object.assign(record, { then: resolve => resolve(42) });
    return JSON.stringify([p instanceof Promise, Object.hasOwn(p, "constructor"), await read(p)]);
  })()`), "[true,false,null]", "native identity and own-key exclusion also require the standard inherited constructor");
  // Reaction construction observes Symbol.species. External changes to it
  // execute construction outside the reviewed native operation's contract.
  assert.equal(await runExample("native-promise-reactions", `(async () => {
    let constructions = 0;
    class Counted extends Promise { constructor(executor) { super(executor); constructions++; } }
    const p = Promise.resolve(3);
    Object.defineProperty(Promise, Symbol.species, { value: Counted });
    const result = await finalized(p);
    return JSON.stringify([result, constructions > 0]);
  })()`), "[3,true]", "the host premise fixes standard species behavior for reaction construction");
  assert.equal(await runExample("invalid-native-promise-constructor-intersection", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    Object.assign(p, { constructor: Promise });
    return await modifyAndRead(p);
  })()`), undefined,
    "the actual constructor write through a typed structural alias invalidates the numeric result");
  // Native catch and finally construct a promise that re-adopts the payload.
  for (const file of ["invalid-native-promise-catch-record", "invalid-native-promise-catch-record-explicit", "invalid-native-promise-finally-record"])
    assert.equal(await runExample(file, `(async () => {
      const record = { n: 1 };
      const p = Promise.resolve(record);
      Object.assign(record, { then: resolve => resolve(42) });
      return await forward(p);
    })()`), 42, `${file}: native result construction adopts the record's added then member`);
  assert.equal(await runExample("native-promise-reactions", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    return JSON.stringify([await caught(Promise.resolve(2)), await finalized(Promise.resolve(3)), await mapped(p), await finalizedPromise(Promise.resolve(4), p)]);
  })()`), "[2,3,1,4]");
  // The external callback returns without mutating the cell. Only the hidden
  // then hook, absent from its open record contract, corrupts the typed cell.
  assert.equal(await runExample("invalid-native-promise-finally-cleanup", `
    function callbackResult(cell) {
      return { tag: 1, then(resolve) { cell.value = "changed"; resolve(undefined); } };
    }
    forward(Promise.resolve(4), { value: 1 });`), "changed",
    "finally cannot invoke an unconstrained cleanup result's hidden then hook");
  assert.equal(await runExample("invalid-native-promise-augmentation", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then: resolve => resolve(42) });
    Object.assign(p, { constructor: Promise });
    return await read(p);
  })()`), undefined, "a source merge cannot relax the native constructor invariant");
  assert.equal(runExample("invalid-native-promise-extra-field", "ownValue()"), undefined,
    "a source merge cannot manufacture fields on an async function's native promise result");
  assert.equal(await runExample("native-promise-catch-explicit", `caughtString(Promise.reject("failure"))`), "fallback");
  assert.equal(runExample("invalid-native-promise-copy", "fake(Promise.resolve(1)).then"), undefined,
    "a source spread copies no inherited native promise methods");
  assert.equal(runExample("native-promise-constructor-read", "constructorValue(Promise.resolve(1)) === Promise"), true,
    "excluding an own constructor keeps the inherited native constructor observable");
  assert.equal(await runExample("native-promise-qualified-return", `(async () => {
    let adoptedElements = 0;
    const element = { then(resolve) { adoptedElements++; resolve(42); } };
    const array = [element];
    const record = { tag: 1, then: 0 };
    return JSON.stringify([
      await stable(2), await fromNumber(3), await fromNative(Promise.resolve(4)),
      await stableUnknown(5), await adoptUnknown(Promise.resolve(6)),
      await stableArray(array) === array, await adoptArray(Promise.resolve(array)) === array,
      await resolvedArray(array) === array, await stableRecord(record) === record,
      widenResult(wrap) === wrap, adoptedElements
    ]);
  })()`), "[2,3,4,5,6,true,true,true,true,true,0]",
    "stable generic resolution preserves its payload, and resolving an array does not adopt its elements");
  assert.equal(await runExample("invalid-native-promise-qualified-view", `
    unstableView({ tag: 1, then(resolve) { resolve(42); } });`), 42,
    "an open record view does not establish the explicit non-thenable bound used by fresh resolution");
  // PromiseResolve's native branch returns the same promise even if its
  // fulfilled record later acquires then. Its mixed fresh branch admits a
  // primitive, and a stable record's explicit bound preserves its identity.
  assert.equal(await runExample("native-promise-resolve-identity", `(async () => {
    let adopted = 0;
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then(resolve) { adopted++; resolve(42); } });
    const stable = { tag: 1, then: 0 };
    return JSON.stringify([nativeIdentity(p) === p, nativeWiden(p) === p,
      mixedIdentity(p) === p, await readIdentity(p), adopted,
      await mixedIdentity(2), await freshStable(stable) === stable]);
  })()`), "[true,true,true,1,0,2,true]",
    "native resolution observes its existing payload through constructor identity");
  assert.equal(await runExample("invalid-native-promise-async-record-forward", `(async () => {
    const record = { n: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then(resolve) { resolve(42); } });
    return await forward(p);
  })()`), 42, "fresh async forwarding re-adopts the native promise's fulfilled record");
  assert.equal(await runExample("invalid-native-promise-resolve-receiver", `class Other extends Promise {}
    (async () => {
    const cell = { value: 1 };
    const record = { tag: 1 };
    const p = Promise.resolve(record);
    Object.assign(record, { then(resolve) { cell.value = "changed"; resolve(42); } });
    return await forward(p, cell);
  })()`), "changed", "a different PromiseResolve receiver constructs and adopts instead of taking native identity");
  for (const [file, fn, native] of [
    ["invalid-native-promise-async-unknown-value", "openValue", false],
    ["invalid-native-promise-async-unknown-native", "openNative", true],
    ["invalid-native-promise-resolve-input", "openResolve", false],
  ] as const)
    assert.equal(await runExample(file, `(async () => {
      const cell = { value: 1 };
      const record = {};
      const input = ${native ? "Promise.resolve(record)" : "record"};
      Object.assign(record, { then(resolve) { cell.value = "changed"; resolve(42); } });
      await ${fn}(input);
      return cell.value;
    })()`), "changed", `${file}: widening the result leaves the hidden then hook's heap effect observable`);
  // These values and the wrapper execute in the same realm. An array is a
  // stable resolution input even when its elements contain then hooks.
  assert.equal(await runExample("generic-promise-resolution", `(async () => {
    let elementAdoptions = 0;
    const values = [{ then(resolve) { elementAdoptions++; resolve(42); } }];
    let finish;
    const pending = new Promise(resolve => { finish = resolve; });
    const waiting = repeated(pending);
    finish(9);
    let rejected = false;
    try { await repeated(Promise.reject("expected")); }
    catch (reason) { rejected = reason === "expected"; }
    return JSON.stringify([
      await numeric(1), await stored(2), await aliasWrap(3),
      await native(Promise.resolve(4)), await repeated(Promise.resolve(5)),
      await array(values) === values, await union(Promise.resolve(values)) === values,
      await waiting, rejected, elementAdoptions, await forward(Promise.resolve(Promise.resolve(10))),
    ]);
  })()`), "[1,2,3,4,5,true,true,9,true,0,10]",
    "qualified wrapper forwarding preserves stable arrays, native fulfillment, rejection and pending resolution");
  assert.equal(runExample("generic-promise-associated-result", `
    const cell = { value: 6 };
    JSON.stringify([accept(7), exchange(cell, 8), cell.value]);`), "[7,6,8]",
    "associated-result storage keeps the numeric input and write contract");
  // An open record, a native promise of one, or a union with one, is
  // adopted where it holds a then hook: the wrapper does not settle to it.
  for (const [file, fn, input] of [
    ["invalid-generic-promise-open-record", "openRecord", "record"],
    ["invalid-generic-promise-open-native", "openNative", "Promise.resolve(record)"],
    ["invalid-generic-promise-open-union", "openUnion", "record"],
  ] as const)
    assert.equal(await runExample(file, `(async () => {
      const record = { n: 1 };
      const input = ${input};
      Object.assign(record, { then(resolve) { resolve(42); } });
      return await ${fn}(input);
    })()`), 42, `${file}: the open record's then hook is adopted, not settled to`);
  // The ambient wrapper implemented as `Promise.resolve`, which TypeScript
  // accepts at the declaration, adopts the open record's then hook too.
  assert.equal(await runExample("invalid-generic-promise-ambient-open-record", `
    function wrap(value) { return Promise.resolve(value); }
    (async () => {
    const record = { n: 1 };
    Object.assign(record, { then(resolve) { resolve(42); } });
    return await openRecord(record);
  })()`), 42, "an ambient Awaited<T> wrapper adopts the open record's then hook");
  assert.equal(await runExample("invalid-generic-promise-erased-call", `(async () => {
    const cell = { value: 1 };
    await erasedCall({ n: 1, then(resolve) { cell.value = "changed"; resolve(42); } });
    return cell.value;
  })()`), "changed", "a widened result does not constrain the adopted then hook's heap effect");
  assert.equal(await runExample("invalid-generic-promise-observed-input", `(async () => {
    return typeof (await unwrap(Promise.resolve(1)));
  })()`), "number", "the observation of a promise is its payload, not the promise");
  assert.equal(await runExample("generic-promise-resolvable", `(async () => JSON.stringify([
    await numeric(1), await native(Promise.resolve(2)), await union(Promise.resolve("3")),
    await settleUnknown(Promise.resolve(4)),
  ]))()`), '[1,2,"3",4]', "an explicitly qualified parameter settles as an implied one");
  assert.equal(await runExample("invalid-generic-promise-resolvable-result", `(async () => {
    return typeof (await settle(Promise.resolve(1)));
  })()`), "number", "a qualified parameter's result is not the parameter: a promise argument resolves");
  assert.equal(await runExample("invalid-generic-promise-resolvable-local", `(async () => {
    const cell = { value: 1 };
    await settle({ then(resolve) { cell.value = "changed"; resolve(42); } });
    return cell.value;
  })()`), "changed", "an ordinary bound named Resolvable does not constrain a hidden then hook");
  // An awaitable parameter is observed, never resolved again: a record that
  // acquires a then hook after its promise fulfilled is awaited as itself,
  // while returning it, or the promise, from an async function adopts it.
  assert.equal(await runExample("generic-promise-awaitable", `(async () => {
    const cell = { value: 1 };
    const box = { n: 1 };
    const input = Promise.resolve(box);
    await input;
    Object.assign(box, { then(resolve) { cell.value = "changed"; resolve(42); } });
    return JSON.stringify([await record(input), await numeric(2), await native(Promise.resolve(3)),
      await union(input), await union(4), cell.value]);
  })()`), "[null,null,null,null,null,1]", "awaiting an awaitable parameter observes it without adopting a later then hook");
  for (const [file, fn] of [
    ["invalid-generic-promise-awaitable-result", "settle"],
    ["invalid-generic-promise-awaitable-observation", "settle"],
    ["invalid-generic-promise-awaitable-return", "forward"],
  ] as const)
    assert.equal(await runExample(file, `(async () => {
      const cell = { value: 1 };
      const box = { n: 1 };
      const input = Promise.resolve(box);
      await input;
      Object.assign(box, { then(resolve) { cell.value = "changed"; resolve(42); } });
      return JSON.stringify([await ${fn}(input), cell.value]);
    })()`), '[42,"changed"]', `${file}: async return resolves the observation again, adopting its then hook`);
  assert.equal(await runExample("invalid-generic-promise-awaitable-local", `(async () => {
    const cell = { value: 1 };
    await settle({ then(resolve) { cell.value = "changed"; resolve(42); } });
    return cell.value;
  })()`), "changed", "an ordinary bound named Awaitable does not constrain a hidden then hook");
  assert.equal(await runExample("invalid-generic-promise-unknown-output", `(async () => {
    const cell = { value: 1 };
    const input = { n: 1, then(resolve) { cell.value = "changed"; resolve(42); } };
    await erasedOutputCall(input);
    return cell.value;
  })()`), "changed", "an unknown generic output does not constrain a hidden then hook's heap effect");
  // A function value known only by its type may read a position its type
  // does not mention: `map` passes `g` the index, which `g` returns.
  assert.equal(runExample("invalid-named-function-arity-value", "JSON.stringify([main(), typeof main()[0]])"), '[[0],"number"]',
    "a callback typed (x: number) => string reads the index map passes");
  process.stdout.write("native-contract counterexamples run under Node: as the contracts say\n");
}

{
  for (const [file, expression, expected] of [
    ["loose-equality", "[samePrimitive(false, ''), samePrimitive(null, undefined), samePrimitive(9007199254740993n, 9007199254740992), platform('native')].join()", "true,true,false,native"],
    ["loose-equality", "const box = {value: 0}; const result = evaluatedOperands(box, '1'); JSON.stringify([result, box.value])", "[true,1]"],
    ["loose-equality", "const xs = []; [differentArrays(xs, xs), readonlyIdentity(xs, []), namedNullish({valueOf(){throw Error('called')}}, null)].join()", "false,false,false"],
    ["invalid-loose-equality-narrowing", "typeof wrongNumber('1', 1)", "string"],
    ["loose-equality-array-conversion-refused", "const xs = [1]; let calls = 0; xs.valueOf = () => { calls++; return 2; }; JSON.stringify([arrayConversion(xs, 2), calls])", "[true,1]"],
    ["callable-bag-union", "[readWrite(true, true), readWrite(false, true)].join()", "false,false"],
    ["invalid-callable-bag-union", "wrong(false, true)", false],
    ["recursive-callable", "selfLoop()", false],
    ["invalid-recursive-callable", "wrong()", true],
    ["non-regular-alias", "first({ v: 1, next: null })", 1],
    ["invalid-non-regular-alias", "wrong({ v: 1, next: null })", null],
    ["assertion-snapshot", "assertedSnapshot({ value: 3 })", 3],
    ["saved-field-comparison", "const box = { value: 7 }; JSON.stringify([comparedBeforeWrite(box), box.value])", "[true,null]"],
    ["array-assign-field-target", "const pair = { first: 1, second: 2 }; const rest = { items: [] }; JSON.stringify([swapInto(pair, rest), pair, rest.items])", '[5,{"first":2,"second":2},[3,4]]'],
    ["array-assign-field-target", "const box = { slot: 'x' }; JSON.stringify([keyBeforeRead({ order: '' }, box), box.slot])", '["kd","kd"]'],
    // The array's iterator stays finished once a step found the end: a later
    // step finds it finished though code grew the array in between.
    ["array-pattern-exhausted-refused", "holeThenGrow()", 9],
    ["array-pattern-exhausted-rest-refused", "JSON.stringify(restAfterGrow())", "[9]"],
    ["array-binding-exhausted-refused", "defaultGrows()", 100],
    ["array-pattern-steps", "JSON.stringify([freshSource({ slot: 0 }, { n: 0 }), heldSource([], { first: 0, second: 0 }), heldSource([5, 6, 7, 8], { first: 0, second: 0 }), boundDefaults([]), boundDefaults([4, 5, 6, 7])])", "[10,6,19,2,11]"],
    ["instanceof-unknown-refused", "typeof px(Object.create(Point.prototype))", "undefined"],
    ["invalid-call-own-override", "JSON.stringify(copyReaderArgument({ read: Object.assign(function () { return this.value; }, { call() { return 'wrong'; } }) }, new PrototypeReader()))", '"wrong"'],
    ["invalid-spread-symbol-nonenumerable", "const input = {}; Object.defineProperty(input, sym, { value: 1, writable: true, enumerable: false }); const out = symbolBranch(input); JSON.stringify([input[sym], sym in out, 'b' in out])", "[1,false,false]"],
    ["relational-conversion", "JSON.stringify([negativeFirst([]), negativeFirst([-1]), belowLimit(1, 2n)])", "[false,true,true]"],
    ["relational-boolean-comparison", "JSON.stringify([order(false, true), order(true, false), atMostTrue(true)])", "[true,false,true]"],
    ["saved-field-comparison", "currentAfterWrite({ value: 7 })", null],
    ["invalid-saved-field-comparison", "wrong({ value: 7 })", null],
    // A closure reads a captured cell when it runs, and sees its own write.
    ["invalid-closure-graph-captured-cell", "counter()", null],
    // A closure created before a write, or an iteration before one, reads
    // the written value; a throw after a write leaves the try with it.
    ["invalid-capture-before-write", "String(stale()())", "undefined"],
    ["invalid-capture-next-iteration", "String(loopCapture(2)())", "undefined"],
    ["invalid-slot-catch-entry", "midTry('a', 'b', () => { throw 1; })", "b"],
    ["slot-object-growth", "JSON.stringify(grownSlot('x', false)()) + JSON.stringify(grownSlot('x', true)())", "{\"x\":1,\"count\":2}{\"x\":1,\"count\":2}"],
    ["invalid-evolving-use-contract", "build(6)", "many"],
    ["invalid-generic-callee-use-contract", "count(3).head", "many"],
    ["generic-callee-use-contract", "JSON.stringify(fromArray(1, 2))", "{\"head\":1,\"tail\":{\"head\":2,\"tail\":null}}"],
    ["evolving-use-contract", "JSON.stringify(reverse({ head: 1, tail: { head: 2, tail: null } }))", "{\"head\":2,\"tail\":{\"head\":1,\"tail\":null}}"],
    ["activation-slots", "[survivesCall('a', 'b', () => { throw 1; }), absorbedInnerTry('a', 'b', () => { throw 1; }), capturedAfterWrites(false)(), JSON.stringify(reverse({ head: 1, tail: { head: 2, tail: null } }))].join()", "a,a,no,{\"head\":2,\"tail\":{\"head\":1,\"tail\":null}}"],
    // A generic function type's result: a pair where it holds, the argument
    // itself where another scheme was passed for it.
    ["generic-function-type-member", "pass({ twice: () => (x) => [x, x] }).twice()(1).join()", "1,1"],
    ["invalid-generic-function-type-member", "wrong({ twice: () => (x) => x }).twice()(1)", 1],
    // A generic function type in an annotation: a value of it is used at an
    // instance; another scheme, a narrower bound or a constant result gives a
    // value outside it there.
    ["generic-function-type-annotation", "[local(), bounded(), impredicative()].join()", "a,abc,1"],
    ["invalid-generic-function-type-annotation", "typeof wrong()", "string"],
    ["invalid-generic-function-type-bound", "typeof unbounded()", "number"],
    ["invalid-generic-closure-field", "typeof wrong()", "number"],
    ["invalid-generic-constructor-type", "typeof wrong()", "string"],
  ] as const)
    assert.equal(runExample(file, expression), expected, file);
  // Imported unique symbols as Node's modules give them: a re-export is the
  // symbol it re-exports, and two constants made by `Symbol.for` of one
  // string hold one symbol; `Symbol()` makes another.
  assert.equal(runImporting("unique-symbol-reexport-value-import", "same()"), true);
  assert.equal(runImporting("unique-symbol-registry-value-import", "same()"), true);
  assert.equal(runImporting("invalid-unique-symbol-value-import", "held === brand"), false);
  // An imported computed alias's keys index the table that names them.
  assert.equal(runImporting("computed-alias-value-import", 'show("branch")'), "branch if");
  assert.equal(runImporting("invalid-computed-alias-value-import", 'only("branch")'), "branch");
  // Members of two namespace imports whose names differ only by where the
  // `$` stands: `lib.limit$double` is 3, `lib$limit.double(1)` is 2.
  assert.equal(runImporting("namespace-import-value-import", "twoMembers()"), 5);
  // Names lowered specially only where they are the standard library's: a
  // namespace `Object`'s `assign`, an export `call`, a local `Math`, a
  // parameter `JSON` and an object's own `call` are ordinary bindings.
  assert.equal(runImporting("shadowed-library-names-value-import", "`${assigned()}|${called()}`"), "assigned 1|2");
  assert.equal(runExample("shadowed-library-names",
    "[localMax(), parameterJson({ stringify: (n) => n * 10 }), ownCall()].join()"), "local 3,30,8");
  // Imported constants stated by their literals.
  assert.equal(runImporting("literal-constant-value-import", "`${greeted()}|${shifted()}`"), "hello|0");
  // An import bound to the name `undefined` reads the imported number.
  assert.equal(runImporting("invalid-undefined-import-value-import", "read()"), 10);
  // `Object.assign(1)` is the standard copy whatever a declaration augments:
  // a `Number` object, not the string the augmenting declarations state.
  for (const file of ["invalid-augmented-object-assign", "invalid-fake-lib-object-assign", "invalid-lib-collision-object-assign"])
    assert.equal(runExample(file, "typeof assigned()"), "object", file);
  // A namespace member is an import binding: writing it throws.
  assert.throws(() => runImporting("invalid-namespace-member-write-value-import", "reset()"), /read only|read-only|Cannot assign/);
  // `map` over an array named only through declarations, its callback
  // shrinking it: the result has three positions, two present.
  assert.equal(runImporting("invalid-array-through-declaration-value-import", "Object.keys(shrunk()).length"), 2);
  // A class has no plain call: calling it throws.
  assert.throws(() => runExample("invalid-class-as-function", "go()"), /cannot be invoked without 'new'/);
  // A construction in a static initializer reads a static not yet defined.
  assert.equal(runExample("invalid-class-static-constructs-early", "String(read())"), "undefined");
  // A generic method's contract read as `unknown` admits 42, which no call
  // can run.
  assert.throws(() => runExample("invalid-generic-method-nested-scheme", "wrong().run({ id: (x) => x })"),
    /is not a function/);
  // The iterator protocol a program's iterable runs: its iterator's `return`
  // is called on `break`, `return` and a throw out of the body, and not at the
  // end or on `continue`; a throw out of the body wins over one out of the
  // close. The parser's lowering (`protocolForOf`) calls `return` exactly there.
  const list = "new LinkedList(new Cell(1, new Cell(5, new Cell(9, null))), { closed: 0 })";
  const closes = (call: string) =>
    runExample("for-of-program-iterable", `const l = ${list}; const r = ${call}; JSON.stringify([r, l.log.closed])`);
  assert.equal(closes("sum(l)"), "[15,0]");
  assert.equal(closes("firstAbove(l, 3)"), "[5,1]");
  assert.equal(closes("firstOver(l, 3)"), "[5,1]");
  assert.equal(closes("skipSmall(l, 3)"), "[14,0]");
  assert.equal(runExample("for-of-program-iterable",
    "const log = { closed: 0 }; JSON.stringify([firstEven(new Countdowns(5, log)), log.closed])"), "[4,1]");
  assert.equal(runExample("for-of-program-iterable", "bodyThrows(new Brittle()).message"), "body");
  process.stdout.write("examples run as JavaScript: results as their outcomes say\n");
}

{
  // `new` at a variadic construct signature reads a spread where it is
  // written, its copy taken before a later actual runs; a class whose code
  // binds positions the rest may leave out is refused at the signature, as
  // Node shows it throwing there.
  assert.equal(runExample("constructor-rest-spread", "order"), 218);
  assert.equal(runExample("constructor-rest-spread", "run"), 14);
  assert.throws(() => runExample("invalid-constructor-rest-class", "made"), /reading 'toFixed'/);
}
{
  // A packed class binder: `run` spreads the stored array into the
  // callback; a shorter array stored by `set` leaves the callback's
  // parameter `undefined`, as Node shows it throwing.
  assert.equal(runExample("class-rest-binder", "kept"), 52);
  assert.equal(runExample("class-rest-binder", "paired"), 7);
  assert.throws(() => runExample("invalid-class-rest-binder-set", "lost"), /reading 'toFixed'/);
}
{
  // Regular expressions: what the refused programs return under Node, each
  // against the type TypeScript gives it.
  // A capture under an alternative, after a `[^]` class, or after a `\k`
  // that is a letter outside Unicode mode, is `undefined`, typed `string`.
  assert.equal(runExample("invalid-regexp-unmatched-group", `first("b")`), undefined);
  assert.equal(runExample("invalid-regexp-class-alternative", `first("z")`), undefined);
  assert.equal(runExample("invalid-regexp-legacy-escape", `first("k<a")`), undefined);
  assert.equal(runExample("invalid-regexp-structural-capture", `key(/(a)|b/, "b")`), undefined);
  // A split splices an unmatched capture in as `undefined`, typed `string`.
  assert.equal(runExample("invalid-regexp-split-captures", `parts("a1b")[2]`), undefined);
  // `lastIndex` is a regex's own property, not enumerable: `in` finds it, a
  // copy lacks it.
  assert.equal(runExample("invalid-regexp-lastindex-in", "hasState(/a/)"), true);
  assert.equal(runExample("invalid-regexp-lastindex-view", "viewed()"), undefined);
  // `matchAll` converts its argument's `flags` before dispatching: client
  // code runs on a structural regex.
  assert.equal(runExample("invalid-regexp-structural-matchall", `const seen = { ran: false };
    count({ [Symbol.match]: true, flags: { toString() { seen.ran = true; return "g"; } },
      [Symbol.matchAll]: () => [][Symbol.iterator]() }, "x");
    seen.ran`), true);
  // `compile` gives an existing regex another pattern: one group fewer.
  assert.equal(runExample("invalid-regexp-compile", `recompiled().exec("c").length`), 1);
  // A subclass's `exec` is what `replace` calls: no match is replaced.
  assert.equal(runExample("invalid-regexp-subclass", "make()"), "ab");
  // The positive cases run as their types say.
  assert.equal(JSON.stringify(runExample("regexp-literals", `[assignment("k=v"), digits("-"), escape("<\`a\`>"),
    words(" a b "), tokens("ab 12"), count("a1b22")]`)),
    JSON.stringify([["k", "v"], "none", "&lt;<code>a</code>>", ["a", "b"], "<w>ab</w>12@3", 3]));
}
{
  // Native footprints (SOURCE-CONTRACTS.md, "Native footprints"): what each
  // array mutator does to `map`'s result when its callback calls it on the
  // array being mapped. The removing ones leave holes; the growing ones and
  // element writes leave none.
  const holes = (call: (xs: number[], i: number) => unknown): number => {
    const xs = [1, 2, 3];
    const ys = xs.map((x, i) => { call(xs, i); return x; });
    return ys.length - Object.keys(ys).length;
  };
  const removing: [string, (xs: number[], i: number) => unknown][] = [
    ["pop", (xs) => xs.pop()],
    ["shift", (xs) => xs.shift()],
    ["reverse after growth", (xs, i) => { if (i === 0) { xs.length = 5; xs.reverse(); } }],
    ["a shorter length", (xs, i) => { if (i === 0) xs.length = 1; }],
    ["splice removing", (xs, i) => { if (i === 0) xs.splice(1, 1); }],
    ["delete", (xs, i) => { if (i === 0) delete xs[1]; }],
  ];
  for (const [name, call] of removing) assert.ok(holes(call) > 0, `${name} in map's callback leaves a hole`);
  const growing: [string, (xs: number[], i: number) => unknown][] = [
    ["push", (xs) => xs.push(9)],
    ["unshift", (xs) => xs.unshift(9)],
    ["sort", (xs) => xs.sort((a, b) => b - a)],
    ["an element write", (xs, i) => { xs[i] = 7; }],
    ["a longer length", (xs, i) => { if (i === 0) xs.length = 5; }],
    ["splice inserting", (xs, i) => { if (i === 0) xs.splice(1, 0, 8); }],
  ];
  for (const [name, call] of growing) assert.equal(holes(call), 0, `${name} in map's callback leaves no hole`);
  // A nested `map` is part of the outer callback: its callback's `pop` leaves
  // holes in the outer result, its `push` none.
  assert.ok(holes((xs) => xs.map((x) => { xs.pop(); return x; })) > 0, "a nested map's pop leaves a hole");
  assert.equal(holes((xs) => xs.map((x) => { xs.push(x); return x; })), 0, "a nested map's push leaves none");
  // `sort`'s writeback deletes every index from its snapshot's count up to
  // the length it read first: index 3, which held a value, is a hole after.
  const ys: number[] = [3, 1];
  ys[3] = 2;
  ys.sort((a, b) => { ys[2] = 0; return a - b; });
  assert.deepEqual([Object.keys(ys), ys.length], [["0", "1", "2"], 4], "sort's writeback deletes past its count");
  // `unshift` ends by setting the length: a trailing hole stays one.
  const trailing: number[] = [1];
  trailing.length = 2;
  trailing.unshift(9);
  assert.deepEqual([trailing.length, Object.keys(trailing)], [3, ["0", "1"]], "unshift keeps a trailing hole");
  // An element-returning or receiver-returning native returns an existing
  // value, never a fresh one; `map` allocates its result.
  const old = [1];
  const nested = [old];
  assert.equal(nested.find(() => true), old, "find returns an existing element");
  assert.equal(nested.at(0), old, "at returns an existing element");
  assert.equal(nested.sort(), nested, "sort returns its receiver");
  assert.equal(nested.reverse(), nested, "reverse returns its receiver");
  assert.notEqual(nested.map((x) => x), nested, "map allocates its result");
  // A Set iterator reads the set's state at each step: it sees a later `add`.
  const set = new Set([1]);
  const values = set.values();
  values.next();
  set.add(2);
  assert.equal(values.next().value, 2, "a Set iterator observes the set's state");
  // A regex literal is a fresh object at each evaluation; one regex shared
  // keeps its `lastIndex` between calls; `replace` of a global regex writes it.
  const shared = /a/g;
  assert.deepEqual([shared.test("a"), shared.test("a")], [true, false], "a shared global regex keeps lastIndex");
  const literal = (): boolean => /a/g.test("a");
  assert.deepEqual([literal(), literal()], [true, true], "a regex literal is fresh at each evaluation");
  const global = /&/g;
  global.lastIndex = 2;
  assert.deepEqual(["a&b&".replace(global, "+"), global.lastIndex], ["a+b+", 0], "replace writes lastIndex");
}
{
  // A callable `then` reaching a resolution is called: each operation the
  // pipeline refuses at a thenable settles to what that `then` passes, 42,
  // not to the object (`invalid-*-thenable*`, `invalid-await-*`).
  for (const [file, call] of [
    ["invalid-await-thenable-literal", "settle()"],
    ["invalid-async-return-thenable", "adopt()"],
    ["invalid-promise-resolve-thenable", "wrap()"],
    ["invalid-then-callback-thenable", "chain(Promise.resolve(1))"],
    ["invalid-catch-callback-thenable", "recover(Promise.reject(0))"],
    ["invalid-new-promise-thenable", "make()"],
    ["invalid-await-thenable-width", "widened()"],
    ["invalid-await-inherited-then", "inherited()"],
    ["invalid-await-promise-like", "awaited({ then(resolve) { resolve(42); } })"],
    ["invalid-awaited-alias-thenable", "adopted()"],
  ] as const) {
    const settled: unknown = await runExample(file, call);
    assert.equal(settled, 42, `${file}: the thenable's then is called and settles the result`);
  }
  // `finally` resolves its cleanup result: the thenable's `then` runs.
  const cleaned: unknown = await runExample("invalid-finally-thenable",
    "(async () => { const log = []; await cleanup(Promise.resolve(1), log); return log.length; })()");
  assert.equal(cleaned, 1, "invalid-finally-thenable: the cleanup result's then is called");
  // An object given the tag beside `then`, `catch` and `finally` has a
  // promise's shape, yet `Promise.resolve` takes it for no native promise.
  assert.equal(runExample("invalid-tag-write",
    "(() => { const o = { then() {}, catch() {}, finally() {} }; forge(o); " +
    "return JSON.stringify([Object.prototype.toString.call(o), Promise.resolve(o) === o]); })()"),
  '["[object Promise]",false]', "invalid-tag-write: the tagged object is no native promise");
  assert.equal(runExample("invalid-tag-computed-write", "Object.prototype.toString.call(tagged(Symbol.toStringTag))"),
    "[object Promise]", "invalid-tag-computed-write: a computed write gives the object the tag");
}
