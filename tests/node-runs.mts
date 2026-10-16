// Examples and native-contract counterexamples run under Node: each result is
// what the case's outcome and the contracts it relies on say. No build needed.
import assert from "node:assert/strict";
import { runEmitted, runExample, runImporting } from "../pipeline/run-example.mts";

{
  for (const [file, call] of [
    ["invalid-native-find-mutation", "wrong([1, 2], { value: 0 })"],
    ["invalid-native-map-mutation", "wrong([1, 2], { value: 0 })"],
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
      `${file}: the actual source returns undefined despite its number contract`);
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
  assert.equal(runExample("invalid-type-guard-object", `radius({ kind: "square", side: 1 })`), undefined,
    "invalid-type-guard-object: the narrowed argument is a square, whose radius is undefined");
  assert.equal(runExample("invalid-assertion-promise", "length(true)"), undefined,
    "invalid-assertion-promise: the asserted argument is a Boolean, whose length is undefined");
  assert.throws(() => runExample("invalid-type-guard-false-branch", "shout(-1)"), /toUpperCase is not a function/,
    "invalid-type-guard-false-branch: the `false` outcome's argument is a number");
  assert.equal(runExample("invalid-number-object", `const seen = { value: 0 };
    wrong({ a: 1, valueOf() { seen.value = 1; return 1; } }, seen)`), 1,
    "invalid-number-object: the actual source returns 1 despite its 0 contract");
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
