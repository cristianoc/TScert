// Examples and native-contract counterexamples run under Node: each result is
// what the case's outcome and the contracts it relies on say. No build needed.
import assert from "node:assert/strict";
import { fileURLToPath, pathToFileURL } from "node:url";
import { spawnSync } from "node:child_process";
import { createHash } from "node:crypto";
import { mkdirSync, mkdtempSync, realpathSync, rmSync, symlinkSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { runEmitted, runExample, runImporting, runNode } from "../pipeline/run-example.mts";

{
  assert.equal(runImporting("invalid-node-url-write-only", '(() => { const u = new URL("file:///x"); moved(u); return u.protocol; })()'), "http:");
  assert.equal(runImporting("node-url-strings", 'pathOf("file:///tmp/x")'), "/tmp/x");
  assert.equal(runImporting("node-url-strings", 'file("/tmp/x")'), "file:///tmp/x");
  assert.equal(runImporting("node-url-strings", 'relative("file:///tmp/")'), "file:///tmp/x");
  assert.equal(runImporting("invalid-node-url-input", '(() => { let n = 0; const u = new URL("file:///x"); Object.defineProperty(u, "pathname", { get() { n++; return "/hook"; } }); return pathOf(u) + n; })()'), "/hook1");
  assert.equal(runImporting("invalid-node-url-base", '(() => { let n = 0; const u = new URL("file:///tmp/"); const p = u.searchParams; p.toString = () => { n++; return "a=b"; }; p.append("a", "b"); relative(u); return n; })()'), 1);
  assert.equal(runImporting("invalid-node-url-read", '(() => { let n = 0; const u = new URL("file:///tmp/"); const p = u.searchParams; p.toString = () => { n++; return "a=b"; }; p.append("a", "b"); hrefOf(u); return n; })()'), 1);
  // blocker-node-url-import imports the boundary tools/url-strings.mts, so
  // it runs in place.
  const urls: {
    pathOf: (url: string) => string; hrefOf: (path: string) => string;
    target: (specifier: string, parent: string) => string | null; fileOf: (url: string | null) => string | null;
  } = await import("../pipeline/examples/blocker-node-url-import.ts");
  assert.equal(urls.pathOf("file:///tmp/x"), "/tmp/x");
  assert.equal(urls.hrefOf("/tmp/x"), "file:///tmp/x");
  assert.equal(urls.target("x", "/tmp/parent"), "/tmp/x");
  // The rewritten string tests answer as the URL members they replace, on
  // what the resolver answers with and without --preserve-symlinks, which
  // keeps an empty query or fragment, and on other serialized URLs.
  const members = (href: string): string | null => {
    const u = new URL(href);
    return u.protocol === "file:" && u.search === "" && u.hash === "" ? fileURLToPath(u) : null;
  };
  const resolving = mkdtempSync(join(tmpdir(), "tscert-resolve-"));
  try {
    mkdirSync(join(resolving, "real"));
    writeFileSync(join(resolving, "real", "f.mjs"), "");
    symlinkSync(join(resolving, "real"), join(resolving, "link"));
    const specifiers = ["./f.mjs", "./f.mjs?", "./f.mjs#", "./f.mjs?#", "./f.mjs?q", "./f.mjs#h", "./f.mjs?q#", "./f.mjs?#h", "./%3F.mjs", "./%23.mjs"];
    writeFileSync(join(resolving, "link", "main.mjs"),
      `console.log(JSON.stringify(${JSON.stringify(specifiers)}.map(s => import.meta.resolve(s))))`);
    const kept: string[] = [];
    for (const flags of [[], ["--preserve-symlinks", "--preserve-symlinks-main"]]) {
      const run = spawnSync(process.execPath, [...flags, join(resolving, "link", "main.mjs")], { encoding: "utf8" });
      assert.equal(run.status, 0, run.stderr);
      const hrefs: unknown = JSON.parse(run.stdout);
      assert.ok(Array.isArray(hrefs));
      for (const href of hrefs) {
        assert.equal(typeof href, "string");
        const text = String(href);
        assert.equal(urls.fileOf(text), members(text), text);
        if (/[?#]$/.test(text)) kept.push(text);
      }
    }
    assert.ok(kept.length >= 3, "--preserve-symlinks keeps empty delimiters");
  } finally {
    rmSync(resolving, { recursive: true, force: true });
  }
  for (const href of ["file:///tmp/x?q", "file:///tmp/x#f", "file:///tmp/x?", "file:///tmp/x#", "file:///tmp/x?#", "file:///tmp/x?#f",
    "file:///tmp/x#a?b", "file:///tmp/%3F", "file:///tmp/%23", "file:///tmp/a%20b", "node:fs", "data:text/javascript,"])
    assert.equal(urls.fileOf(href), members(href), href);
  for (const [specifier, parent] of [["./x.ts", "/tmp/a/b.ts"], ["../%3F.ts", "/tmp/sp ace/b.ts"], ["./q.ts?x#h", "/tmp/#h/b.ts"], ["http://[", "/tmp/b.ts"]])
    assert.equal(urls.target(specifier ?? "", parent ?? ""), (() => {
      try { return fileURLToPath(new URL(specifier ?? "", pathToFileURL(parent ?? ""))); } catch { return null; }
    })(), specifier);
  assert.equal(runImporting("invalid-node-url-unknown-parameter",
    'escaped((u) => { Object.defineProperty(u, "href", { get: () => 7 }); })'), 7);
  assert.equal(runImporting("invalid-node-url-unknown-return",
    '(() => { const m = make(); Object.defineProperty(m.leaked, "href", { get: () => 7 }); return read(m); })()'), 7);
  assert.equal(runImporting("invalid-node-url-options", 'windowsPath("file:///C:/x")'), "C:\\x");
  assert.equal(runImporting("invalid-node-url-program-object", 'pathOf(() => "/callback")'), "/callback");
  assert.equal(runImporting("invalid-node-url-member", 'pathnameOf(new URL("file:///x?q"))'), "/x");
  assert.equal(runImporting("invalid-node-url-spread", 'copied(new URL("file:///x")) === undefined'), true);
  assert.equal(runImporting("invalid-node-url-write", 'moved()'), "http://example.com/a");
  assert.equal(runImporting("invalid-node-url-fresh-escape", '(() => { let n = 0; const href = escaped((u) => { const p = u.searchParams; p.toString = () => { n++; return "a=b"; }; p.append("a", "b"); }); return n > 0 && href; })()'), "file:///tmp/x?a=b");
  assert.equal(runImporting("invalid-node-url-replaced", '(() => { replace(() => "file:///elsewhere/"); return new URL("x", new URL("file:///tmp/")).href; })()'), "file:///elsewhere/x");
  // Each hook is on an instance; all standard prototypes stay unchanged.
  for (const operation of ["new URL('x', u)", "fileURLToPath(u)", "u.href"]) {
    for (const hook of ["toString", "primitive", "size"]) {
      assert.equal(runImporting("node-url-strings", `(() => {
        let calls = 0;
        const u = new URL('file:///tmp/x');
        const p = u.searchParams;
        if (${JSON.stringify(hook)} === 'size') Object.defineProperty(p, 'size', { get() { calls++; return 1; } });
        else Object.defineProperty(p, ${JSON.stringify(hook)} === 'primitive' ? Symbol.toPrimitive : 'toString', { value() { calls++; return 'a=b'; } });
        p.append('a', 'b');
        ${operation};
        return calls > 0;
      })()`), true, `${operation}: own ${hook} serialization callback`);
    }
  }
  for (const key of ["auth", "path", "hostname", "pathname"]) {
    assert.equal(runImporting("node-url-strings", `(() => {
      let calls = 0; const u = new URL('file:///tmp/x');
      Object.defineProperty(u, ${JSON.stringify(key)}, { get() { calls++; return ${JSON.stringify(key)} === 'pathname' ? '/tmp/x' : ${JSON.stringify(key)} === 'hostname' ? '' : undefined; } });
      fileURLToPath(u); return calls > 0;
    })()`), true, `fileURLToPath: own ${key} getter`);
  }
  // tools/child-output.mts runs a child and hands back plain values. Each
  // scenario runs in a process of its own, where a diagnostics-channel
  // subscriber, which sees the child before `spawn` returns, does what other
  // code may, every standard prototype unchanged: the result's types hold,
  // its values may be forged, and a promise left pending is reported as
  // such after three seconds.
  const boundary = pathToFileURL(join(import.meta.dirname, "..", "tools", "child-output.mts")).href;
  const ran = (subscriber: string, command: readonly string[] = [process.execPath, "-e", "process.stdout.write('ok')"]): unknown => {
    const script = `process.getBuiltinModule("node:diagnostics_channel").subscribe("child_process", ({ process: child }) => { ${subscriber} });
      const { runChild } = await import(${JSON.stringify(boundary)});
      const pending = new Promise((done) => setTimeout(() => done("pending"), 3000));
      const result = runChild(${JSON.stringify(command[0])}, ${JSON.stringify(command.slice(1))}).catch((e) => e.message);
      console.log(JSON.stringify(await Promise.race([result, pending])));
      process.exit(0);`;
    const run = spawnSync(process.execPath, ["--input-type=module", "-e", script], { encoding: "utf8", timeout: 30_000 });
    assert.equal(run.status, 0, run.stderr);
    return JSON.parse(run.stdout.trim().split("\n").pop() ?? "null");
  };
  assert.deepEqual(ran(""), { code: 0, signal: null, stdout: "ok" });
  assert.deepEqual(ran(`child.on("spawn", () => child.stdout.setEncoding("latin1"));`), { code: 0, signal: null, stdout: "ok" });
  assert.deepEqual(ran("", ["/bin/sh", "-c", "kill -TERM $$"]), { code: null, signal: "SIGTERM", stdout: "" });
  assert.match(String(ran(`child.on("spawn", () => child.stdout.emit("data", 123));`)), /delivered no text/);
  assert.match(String(ran(`child.on("spawn", () => child.stdout.emit("data", "ok", "bad"));`)), /delivered no text/);
  assert.match(String(ran(`child.on("spawn", () => child.emit("close", "bad", 42));`)), /unexpected arguments/);
  assert.match(String(ran(`child.on("spawn", () => child.emit("close", 0, null, "bad"));`)), /unexpected arguments/);
  assert.match(String(ran(`Object.defineProperty(child, "stdout", { get() { return 123; }, set() {} });`)), /no standard output stream/);
  assert.match(String(ran(`let n = 0; Object.defineProperty(child, "stdout", { get() { return n++ === 0 ? { setEncoding() {}, on() {} } : 7; }, set() {} });`)),
    /standard output changed/);
  assert.match(String(ran("", ["/no/such/command"])), /failed to start/);
  // What spawn or a replaced method throws is not read: the rejection's
  // message is the boundary's own.
  assert.match(String(ran("child.on = () => { throw 42; };")), /starting the child or reading its standard output threw/);
  assert.match(String(ran("", ["/bin/ec\u0000ho"])), /starting the child or reading its standard output threw/);
  // Valid events another holder emits are taken as Node's: forged values of
  // the stated types (the child itself prints "real" and exits 7).
  const real = [process.execPath, "-e", "setTimeout(() => { process.stdout.write('real'); process.exit(7); }, 300)"];
  assert.deepEqual(ran(`child.on("spawn", () => { child.stdout.emit("data", "forged"); child.emit("close", 0, null); });`, real),
    { code: 0, signal: null, stdout: "forged" });
  // A stable substitute stream, and a replaced instance method.
  assert.deepEqual(ran(`const fake = { setEncoding() {}, on(event, f) { if (event === "data") setTimeout(() => f("fake")); return fake; } };
    Object.defineProperty(child, "stdout", { get() { return fake; }, set() {} });`, real), { code: 7, signal: null, stdout: "fake" });
  assert.deepEqual(ran(`child.on = (event, f) => { if (event === "close") setTimeout(() => f(0, null), 10); return child; };`, real),
    { code: 0, signal: null, stdout: "" });
  // Listeners removed: the promise stays pending after the child exits.
  assert.equal(ran(`child.on("spawn", () => child.removeAllListeners("close"));`), "pending");
  // An error whose every read throws: rejected, before and after settling,
  // and the process does not end.
  const hostile = `const e = new Error(); Object.defineProperty(e, "message", { get() { throw new Error("read"); } });
    for (const key of ["name", "stack", "code"]) Object.defineProperty(e, key, { get() { throw new Error("read"); } });`;
  assert.match(String(ran(`${hostile} child.on("spawn", () => child.emit("error", e));`)), /failed to start or was signalled an error/);
  assert.deepEqual(ran(`${hostile} child.on("spawn", () => { child.emit("close", 0, null); child.emit("error", e); });`),
    { code: 0, signal: null, stdout: "" });
  // Another holder's encoding: the output is a string, decoded otherwise.
  const accented = [process.execPath, "-e", "process.stdout.write(String.fromCharCode(233))"];
  assert.deepEqual(ran("", accented), { code: 0, signal: null, stdout: String.fromCharCode(233) });
  assert.deepEqual(ran(`child.on("spawn", () => child.stdout.setEncoding("latin1"));`, accented),
    { code: 0, signal: null, stdout: String.fromCharCode(195, 169) });
  // Out of file descriptors, `spawn` returns before it assigns `stdout`.
  {
    const script = `const fs = process.getBuiltinModule("node:fs");
      const { runChild } = await import(${JSON.stringify(boundary)});
      const fds = []; try { while (true) fds.push(fs.openSync("/dev/null", "r")); } catch {}
      const result = await runChild(process.execPath, ["-e", "1"]).catch((e) => e.message);
      for (const fd of fds) fs.closeSync(fd);
      console.log(JSON.stringify(result));`;
    const run = spawnSync("/bin/sh", ["-c", 'ulimit -n 64; exec "$0" --input-type=module -e "$1"', process.execPath, script], { encoding: "utf8" });
    assert.equal(run.status, 0, run.stderr);
    assert.match(String(JSON.parse(run.stdout)), /no standard output stream/);
  }
}

{
  // tools/module-hooks.mts runs Node's resolution and loading through hooks
  // of its own and hands back plain values. Hooks other code registered run
  // inside: one registered earlier forges a resolution or throws, and one a
  // loaded module registers calls the boundary's load hook with a URL that
  // is no string, which an earlier hook answers with a source of its own.
  // The values keep their types and may be forged.
  const boundary = pathToFileURL(join(import.meta.dirname, "..", "tools", "module-hooks.mts")).href;
  const directory = realpathSync(mkdtempSync(join(tmpdir(), "tscert-hooks-")));
  try {
    writeFileSync(join(directory, "x.mjs"), "export {};");
    writeFileSync(join(directory, "b.cjs"), "module.exports = 2;");
    writeFileSync(join(directory, "a.cjs"), `const { registerHooks } = require("node:module");
      registerHooks({ load: (u, c, n) => u.endsWith("/b.cjs") ? n(42, c) : n(u, c) });
      module.exports = 1 + require("./b.cjs");`);
    writeFileSync(join(directory, "t.cjs"), "throw 7;");
    // A hook a loaded module registers keeps the continuation that calls
    // the boundary's load hook and throws; the continuation, called after
    // loadObserved returned, passes the call on and records nothing.
    writeFileSync(join(directory, "d.cjs"), "module.exports = 4;");
    writeFileSync(join(directory, "c.cjs"), `const { registerHooks } = require("node:module");
      registerHooks({ load: (u, c, n) => { if (u.endsWith("/d.cjs")) { globalThis.kept = n; throw 8; } return n(u, c); } });
      require("./d.cjs");`);
    const script = `const { registerHooks } = await import("node:module");
      const { createHash } = await import("node:crypto");
      const { readFileSync } = await import("node:fs");
      const { loadObserved, resolutionConditions, resolveWithNode } = await import(${JSON.stringify(boundary)});
      const at = (name) => ${JSON.stringify(directory)} + "/" + name;
      const parent = new URL("file://" + at("main.mjs")).href;
      const digest = (name) => createHash("sha256").update(readFileSync(at(name))).digest("hex");
      const out = { plain: resolveWithNode("./x.mjs", parent), missing: resolveWithNode("./none.mjs", parent),
        conditions: resolutionConditions(), threw: loadObserved(at("t.cjs")), t: digest("t.cjs"), a: digest("a.cjs") };
      registerHooks({ load: (u, c, n) => u === 42 ? { format: "commonjs", source: "module.exports = 40;", shortCircuit: true } : n(u, c) });
      out.loaded = loadObserved(at("a.cjs"));
      registerHooks({ resolve: (s, c, n) => s === "./x.mjs" ? { url: "file:///forged", shortCircuit: true }
        : s === "./boom.mjs" ? (() => { throw 9; })() : n(s, c) });
      out.forged = resolveWithNode("./x.mjs", parent);
      out.thrown = resolveWithNode("./boom.mjs", parent);
      const kept = loadObserved(at("c.cjs"));
      const before = kept.reads.length;
      const late = typeof globalThis.kept("file://" + at("b.cjs"), { format: "commonjs" }).source;
      out.retained = { outcome: kept.outcome, grew: kept.reads.length - before, late };
      console.log(JSON.stringify(out));`;
    const run = spawnSync(process.execPath, ["--conditions=tscert", "--input-type=module", "-e", script], { encoding: "utf8", timeout: 30_000 });
    assert.equal(run.status, 0, run.stderr);
    const out: unknown = JSON.parse(run.stdout);
    assert.ok(out !== null && typeof out === "object");
    const field = (key: string): unknown => Object.getOwnPropertyDescriptor(out, key)?.value;
    assert.match(String(field("plain")), /^file:\/\/\/.*\/x\.mjs$/);
    assert.equal(field("missing"), null);
    assert.deepEqual(field("conditions"), ["node", "import", "module-sync", "node-addons", "tscert"]);
    const t = String(field("t")), a = String(field("a"));
    assert.deepEqual(field("threw"), { reads: [{ url: pathToFileURL(join(directory, "t.cjs")).href, digest: t }],
      outcome: { k: "threw", thrown: 7 } });
    const loaded = field("loaded");
    assert.ok(loaded !== null && typeof loaded === "object");
    const reads: unknown = Object.getOwnPropertyDescriptor(loaded, "reads")?.value;
    assert.ok(Array.isArray(reads) && reads.length === 3);
    assert.equal(Object.getOwnPropertyDescriptor(reads[0], "digest")?.value, a);
    assert.deepEqual(reads[1], { url: "node:module", digest: null });
    assert.deepEqual(reads[2], { url: null, digest: createHash("sha256").update("module.exports = 40;").digest("hex") });
    assert.deepEqual(Object.getOwnPropertyDescriptor(loaded, "outcome")?.value, { k: "loaded", value: 41 });
    assert.equal(field("forged"), "file:///forged");
    assert.equal(field("thrown"), null);
    assert.deepEqual(field("retained"), { outcome: { k: "threw", thrown: 8 }, grew: 0, late: "string" });
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
  // The negatives: a hook `registerHooks` installs runs inside a later
  // resolution, and `userInfo` with the buffer encoding answers `Buffer`s.
  assert.equal(runImporting("invalid-module-register-hooks",
    '(() => { const seen = counting(); import.meta.resolve("node:fs"); return seen.count; })()'), 1);
  assert.equal(runImporting("invalid-node-os-user-info-buffer", "home()"), "object");
}

{
  for (const [file, call] of [
    ["invalid-native-find-mutation", "wrong([1, 2], { value: 0 })"],
    // The function a field holds when the call runs, a `(n: number) =>
    // boolean`, shrinks the list and is handed `undefined` on the next visit:
    // written into a `Test`'s field, or held by a record that is a `Test`.
    ["invalid-field-call-effect",
      "(() => { const xs = [1, 2], seen = [], t = new Test(); t.check = (n) => { seen.push(n); xs.pop(); return false; }; first(t, xs); return seen.length === 2 ? seen[1] : 0; })()"],
    ["invalid-field-call-effect-alias", "wrong([1, 2], { value: 0 })"],
    // A recursive constant, a record's field or a cell reached by the
    // callback shrinks the list, and the next visit hands it `undefined`.
    ["invalid-find-recursive-constant-mutation", "wrong([1, 2], { value: 0 })"],
    ["invalid-find-recursive-constant-field", "wrong([1, 2], { value: 0 })"],
    ["invalid-find-recursive-cell", "wrong([1, 2], { value: 0 })"],
    // A recursive constant's self read or a name its body rebinds, called
    // with a value outside the closure's parameter or with `map`'s index as
    // a further parameter; a self read passed to `find` while the closure
    // shrinks the array, handed `undefined` on a later visit.
    ["invalid-recursive-constant-self-wider",
      `wrong({ k: "a", parts: [] }, { k: undefined, parts: [{ k: "b", parts: [] }] })`],
    ["invalid-recursive-constant-escape-wider", `wrong({ k: "a", parts: [] }, { k: undefined, parts: [] })`],
    ["invalid-recursive-constant-callback-mutation", `wrong([{ k: "a" }, { k: "b" }, { k: "c" }])[3]`],
    ["invalid-recursive-cell-callback", `wrong({ k: "a", parts: [{ k: "b", parts: [] }] })`],
    ["invalid-recursive-constant-exceptional", `exceptional({ v: "a" })`],
    ["invalid-recursive-constant-shadowed",
      `wrong({ k: "a", parts: [{ k: "b", parts: [] }] }, [(u, at) => at.name])`],
    ["invalid-field-call-effect-cell", "wrong([1, 2], { value: 0 })"],
    ["invalid-find-union-method-effect",
      "(() => { const xs = [{ size: 1 }, { size: 2 }], seen = []; wrong(xs, { size: 0, shrink(x) { seen.push(x); xs.pop(); return false; } }); return seen.length === 2 ? seen[1] : 0; })()"],
    ["invalid-readonly-field-call-effect",
      "(() => { const xs = [1, 2], seen = []; first({ check: (n) => { seen.push(n); xs.pop(); return false; } }, xs); return seen.length === 2 ? seen[1] : 0; })()"],
    ["invalid-native-map-mutation", "wrong([1, 2], { value: 0 })"],
    // A function over an interface extending the element's, handed a base
    // without `size`; a closure over a base calling an extending object's
    // narrower method with a string; a closure over a base shrinking the
    // array of an extending interface it is mapped over.
    ["invalid-closure-offer-extends-narrower", `wrong([{ label: "a" }], { of: (b) => b.size })[0]`],
    ["invalid-closure-offer-extends-method", `typeof wrong([{ step: (by) => by }])[0] === "string" ? undefined : 0`],
    ["invalid-closure-offer-extends-receiver", `wrong([{ label: "a", step() { return this.size; } }])[0]`],
    ["invalid-closure-offer-extends-mutation", `1 in wrong([{ label: "a", size: 1 }, { label: "b", size: 2 }]) ? 0 : undefined`],
    // A value of `Names`' type whose `local` pops the mapped array: `map`
    // skips the index it removed, a hole in the `string[]`.
    ["invalid-map-method-call-effect",
      `(() => { const xs = ["a", "b"]; return 1 in wrong({ prefix: "", local: (n) => { xs.pop(); return n; } }, xs) ? "dense" : undefined; })()`],
    ["invalid-map-primitive-method-mutation", `wrong(["a", "b"])`],
    ["invalid-native-join-coercion", "wrong({ value: 0 })"],
    ["invalid-native-sort-coercion", "wrong({ value: 0 })"],
    // What `%Iterate:ForIn%`'s step read is not what a later read finds.
    ["invalid-for-in-entry-call", "wrong({ a: 1 }, (v) => { delete v.a; })"],
    ["invalid-for-in-entry-field", "wrong({ inner: { a: 1, b: 2 } }, {})"],
    ["invalid-for-in-entry-rebound", "wrong({ a: 1, b: 2 }, {})"],
    // A readonly field of a callable may be a non-enumerable property, which
    // a copy lacks; an arm with no value supplies no field to the copy.
    ["spread-intersection-callable-named", `copied(Object.defineProperty(() => 1, "tag", { value: "t" })).tag`],
    ["spread-intersection-callable-direct", `copied(Object.defineProperty(() => 1, "tag", { value: "t" })).tag`],
    ["invalid-spread-intersection-empty-arm-result", "copied({ b: 1 }).a"],
    // A function's `length` is not enumerable: its copy lacks it.
    ["invalid-spread-function-length", "arity((a, b) => a + b)"],
    // The closure calls its callable parameter with a number, which a
    // function of strings reads `length` of.
    ["invalid-closure-contextual-callable", "narrow.run((s) => s.length)"],
    // A read at an index computed from a length is past the end, or before
    // the start, of an empty, shrunk or sparse array, and of a record that
    // owns no such key.
    ["invalid-array-last-element", "last([])"],
    ["invalid-array-last-sparse", `last(["a", , ])`],
    ["invalid-array-last-after-pop", `stale(["a"])`],
    ["invalid-array-last-alias", `(() => { const a = ["a"]; return aliased(a, a); })()`],
    ["invalid-array-last-callback", `(() => { const a = ["a"]; return called(a, () => { a.pop(); }); })()`],
    ["invalid-length-record-last", "last({ length: 1 })"],
    ["invalid-length-union-last", "last({ length: 1 })"],
    ["invalid-program-node-array-last", "last({ length: 1 })"],
    ["invalid-array-past-end", `pastTheEnd(["a"])`],
    ["invalid-optional-chain-dynamic-index", `at(["a"], 1)`],
    ["invalid-optional-chain-dynamic-index", `argAt({ args: ["a"] }, 1)`],
    ["invalid-array-before-last", `beforeLast(["a"])`],
    // `map`'s result holds a hole where its callback shrank the array; a
    // spread passes it to `push` as `undefined`.
    ["invalid-push-spread-sparse", "wrong([1, 2])"],
    // The protocol's `next` of a union's host: called with no actual, on
    // the iterator as receiver, its effect (and a getter's) on a tested field.
    ["invalid-bind-union-host-arity", "first(new From())"],
    ["invalid-for-of-next-arity", "first(new From())"],
    ["invalid-bind-union-host-this", "first(new Borrowed())"],
    ["invalid-bind-union-host-effect", "(() => { const b = new Box(1); return kept(new Drain(b), b); })()"],
    ["invalid-bind-union-host-getter", "(() => { const b = new Box(1); return kept(new Lazy(b), b); })()"],
    // Past a read that does not complete on every path, or past a write of
    // its receiver, the receiver is still the `undefined` an empty list's
    // element is.
    ["invalid-read-narrows-optional", "wrong([])"],
    ["invalid-read-narrows-write", "wrong([{}])"],
    ["invalid-read-narrows-expression-write", "wrong([{}])"],
    ["invalid-read-narrows-loop", "wrong([{}])"],
    ["invalid-read-narrows-finally", "wrong([{}])"],
    ["invalid-read-narrows-join", "wrong([{}], true, true)"],
    ["invalid-read-narrows-alias", "wrong([{}])"],
    ["invalid-read-narrows-catch", "wrong([])"],
    ["invalid-read-narrows-branch", "wrong([], false)"],
    ["invalid-read-narrows-and", "wrong([], false)"],
    ["invalid-read-narrows-closure", "wrong([])"],
    ["invalid-read-narrows-getter", "wrong()"],
    // A path of a receiver a completed read narrowed: a `fail` that
    // returns, a write of the root, a write of the member through another
    // reference, a call that writes it, before the read or as an earlier
    // actual, each leave `undefined` where a string is returned.
    ["invalid-read-narrows-path-returning", "wrong([{}])"],
    ["invalid-read-narrows-path-write", "wrong([{ initializer: 'a' }], {})"],
    ["invalid-read-narrows-path-alias-write", "wrong([{ initializer: 'a' }])"],
    ["invalid-read-narrows-path-call", "(() => { const l = [{ initializer: 'a' }]; return wrong(l, () => { l[0].initializer = undefined; }); })()"],
    ["invalid-read-narrows-path-argument-call", "(() => { const l = [{ initializer: 'a' }]; return wrong(l, () => { l[0].initializer = undefined; return 1; }); })()"],
    // A method called on a union of hosts: an actual clearing the tested
    // field, a member called on another receiver, and a template literal
    // converting an object by its own `toString`, which clears the field.
    ["invalid-union-method-head-refinement", `bad({ tag: "a", m() {} }, { v: "s" })`],
    ["invalid-union-method-borrowed", `borrowed({ tag: "a", n: 1, k() { return this.n; } }, { tag: "b", k() { return 0; } })`],
    ["invalid-template-own-to-string", `(() => { const box = { v: "s" }; return bad({ v: 1, toString() { box.v = undefined; return ""; } }, box); })()`],
  ])
    assert.equal(runExample(file, call), undefined,
      `${file}: the actual source returns undefined despite its number or string contract`);
  // A guard answering `true` of a value outside its promise: each call
  // returns the tag the promise excludes, or the member it says is there.
  for (const [file, call, found] of [
    ["invalid-condition-stale-call", `(() => { const b = { k: "union" }; return staleCall(b) ? b.k : ""; })()`, "intersection"],
    ["invalid-condition-stale-read", `(() => { const b = { k: "union" }; return staleRead(b) ? b.k : ""; })()`, "intersection"],
    ["invalid-condition-partial-tag", `(() => { const b = { k: "union" }; return partialTag(b) ? b.k : ""; })()`, "union"],
    ["invalid-guard-disjunction-left-true", `(() => { const p = { k: "a" }; return right(p) ? p.k : ""; })()`, "a"],
    ["invalid-guard-disjunction-nested", `(() => { const p = { k: "a" }; return nested(p) ? typeof p.a : ""; })()`, "undefined"],
    ["invalid-guard-disjunction-write",
      `(() => { const b = { k: "b" }; return written(b, (x) => { x.k = "a"; }) ? b.k : ""; })()`, "a"],
  ])
    assert.equal(runExample(file, call), found, `${file}: the guard answers true of a value outside its promise`);
  // `Reflect.get` calls an accessor's getter, which empties the caller's
  // array.
  assert.equal(runExample("invalid-reflect-get-getter",
    "(() => { const xs = [1]; read({ get x() { xs.pop(); return 0; } }); return xs.length; })()"), 0,
    "invalid-reflect-get-getter: the getter runs at Reflect.get");
  // An `if` and `||`'s false outcome past a call that writes the tested
  // field: the read returns what the call wrote.
  assert.equal(runExample("invalid-condition-stale-branch", `(() => { const b = { k: "union" }; return staleIf(b, () => { b.k = "intersection"; }); })()`),
    "intersection");
  assert.equal(runExample("invalid-condition-stale-disjunction", `(() => { const b = { k: "union" }; return staleOr(b, () => { b.k = "intersection"; return false; }); })()`),
    "intersection");
  assert.equal(runExample("invalid-condition-negated-stale-call", `(() => { const b = { k: "union" }; return negatedStale(b, () => { b.k = "intersection"; }); })()`),
    "intersection");
  // A method call on a union of hosts runs the member of the object read
  // before its actual, which replaces the receiver's cell or binding.
  assert.equal(runExample("union-method-head",
    `(() => { const a = { tag: "a", name(n) { return "a" + n; } }, b = { tag: "b", name(n) { return "b" + n; } }; return [first({ o: a }, b), local(a, b)].join(); })()`),
    "a1,a2", "union-method-head: the call's receiver is the object read before the actual");
  // `find` visits the hole a `length` write leaves, handing the callback
  // `undefined`, which the recursive constant returns as its number.
  assert.equal(runExample("invalid-find-recursive-constant-sparse", "wrong()"), 1,
    "invalid-find-recursive-constant-sparse: the hole's visit finds a result that is no number");
  // A union's host whose `next` yields a string where its overload says a
  // number; a done step's value, the host's return value, read as a number.
  assert.equal(runExample("invalid-bind-union-host-overload", "first(new Mixed())"), "s",
    "invalid-bind-union-host-overload: the loop's value is a string despite the number contract");
  assert.equal(runExample("invalid-bind-union-host-return", "peek(new Repeat(0))"), "finished",
    "invalid-bind-union-host-return: a done step's value is the host's return value");
  // A step's result that is no object, and an absent `next`: the protocol throws.
  for (const file of ["invalid-bind-union-host-primitive", "invalid-bind-union-host-tag-set"])
    assert.throws(() => runExample(file, "first(new Source(1))"), /not an object/,
      `${file}: GetIterator throws on a numeric iterator`);
  assert.throws(() => runExample("invalid-bind-union-host-nullable", "first(new Source(undefined))"), /not an object/,
    "invalid-bind-union-host-nullable: GetIterator throws on an undefined iterator");
  assert.throws(() => runExample("invalid-bind-union-host-missing-member", "first(new Source(new Missing()))"), /not a function/,
    "invalid-bind-union-host-missing-member: the step calls an absent next");
  assert.throws(() => runExample("invalid-bind-union-host-non-object", "first(new Bare())"), /not an object/,
    "invalid-bind-union-host-non-object: IteratorStepValue throws on a number");
  assert.throws(() => runExample("invalid-bind-union-host-optional", "first(new Maybe())"), /not a function/,
    "invalid-bind-union-host-optional: the step calls an absent next");
  assert.equal(await runExample("invalid-block-type-awaited", `test("text")`), "text",
    "invalid-block-type-awaited: y holds a string despite the local alias's number contract");
  // `outer.v` is the enclosing `T`, here a string: the result is the number
  // stored there at `Both`'s own `T`.
  assert.equal(runExample("invalid-block-type-captured-shadow", `swap("s", 1)`), 1,
    "invalid-block-type-captured-shadow: a number returned at T := string");
  // Past the block, `Box` is the module's `{ v: string }`: the result holds
  // the number the block's `Box` admitted.
  assert.equal(runExample("invalid-block-type-scope", "typeof leak(1).v"), "number",
    "invalid-block-type-scope: the result's `v` is a number despite its string contract");
  // A spread copies a key the earlier field holds: from an object a written
  // result `{}` states no bound of, a literal arm, an open arm, a filled
  // dictionary, a later spread's literal and a getter's value.
  for (const [file, call, value] of [
    ["invalid-object-spread-annotated-result", "label()", 1],
    ["invalid-object-spread-optional-key", "label(true)", 1],
    ["invalid-object-spread-union-open", "label({ name: 1 }, false)", 1],
    ["invalid-object-spread-returned-dictionary", "label()", 1],
    ["invalid-object-spread-two-sources", "count(true)", "s"],
    ["invalid-object-spread-getter", "label()", 1],
    ["invalid-object-spread-exact-alias", "label()", 1],
  ] as const)
    assert.equal(runExample(file, call), value, `${file}: the copy holds the spread's key`);
  // At `B := { name: "a"; size: number }`, a value meeting the binder: the
  // copy's `name` is "x", which the binder excludes.
  assert.equal(runExample("invalid-spread-binder-result", `relabel({ name: "a", size: 1 }).name`), "x",
    "invalid-spread-binder-result: the copy returned as B holds a name outside B");
  // A value of `Counter & { next: () => number; tag: string }` whose `next`
  // is its prototype's: the copy has none.
  assert.equal(runExample("invalid-spread-intersection-method",
    `typeof copied(Object.assign(new Counter(), { tag: "t" })).next`), "undefined",
    "invalid-spread-intersection-method: the copy returned with a `next` function has none");
  // The pattern steps a string by code point: the first is the whole emoji.
  assert.equal(runExample("invalid-for-of-pattern-string", `firsts(["\\u{1F600}b"])`), "\u{1F600}",
    "invalid-for-of-pattern-string: the pattern binds a code point, not the first code unit");
  // The step calling the closure constant reads `LIMIT` before it holds a value.
  assert.throws(() => runExample("invalid-initialization-closure-call", "scaled(1)"), /before initialization/,
    "invalid-initialization-closure-call: the module throws a ReferenceError while it initializes");
  // A call of a function returning `never` throws: the statement after it
  // runs only on the condition's other edge, and its throw reaches the
  // handler and the `finally` block.
  assert.equal(runExample("never-call-narrowing", `checked("a")`), "a", "never-call-narrowing: checked");
  assert.throws(() => runExample("never-call-narrowing", "checked(1)"), /not a string/, "never-call-narrowing: thrown");
  assert.equal(runExample("never-call-narrowing", "caught(1)"), "caught!", "never-call-narrowing: caught");
  assert.equal(runExample("never-call-narrowing", `caught("a")`), "a!", "never-call-narrowing: completed");
  // A comma in a test position runs its left operand first, once: the
  // counter is 1 at the test, the write seen by it, and a throwing left
  // operand's exception is the comma's.
  assert.equal(runExample("comma-test-refinement", `counted({ kind: 1, a: "" })`), 1, "comma-test-refinement: counted");
  assert.equal(runExample("comma-test-refinement", "written()"), 5, "comma-test-refinement: written");
  assert.throws(() => runExample("comma-test-refinement", `thrown({ kind: 3, c: "" })`), /left/, "comma-test-refinement: thrown");
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
    ["map-stable-object-spread", `bounded([{ name: "a", bound: null }])`, '[{"name":"a","bound":1}]'],
    ["map-stable-object-spread", `renamed([{ name: "a", bound: 2 }], "p")`, '[{"name":"pa","bound":2}]'],
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
  // Optional chains nested, shadowed, in a closure and skipping a key's
  // effect: each result at the type the case verifies.
  for (const [call, expected] of [
    [`deep([{ inner: { leaf: { value: 7 } } }])`, 7],
    [`deep([{ inner: {} }, { inner: { leaf: { value: 7 } } }])`, 0],
    [`deep([])`, 0],
    [`shadowed({ inner: { leaf: { value: 2 } } }, [{ inner: { leaf: { value: 3 } } }])`, 203],
    [`shadowed(undefined, [{}])`, 0],
    [`values([{ inner: { leaf: { value: 1 } } }, {}, { inner: {} }]).join(",")`, "1,-1,-1"],
    [`keysRun(undefined)`, 5],
    [`keysRun({ inner: {} })`, 5],
    [`keysRun({ inner: { list: [4] } })`, 14],
  ] as const)
    assert.equal(runExample("optional-chain-nesting", call), expected, `optional-chain-nesting: ${call}`);
  // A chain compared with a literal: each result at the type the case
  // verifies, a nullish receiver's included.
  for (const [call, expected] of [
    [`strict({ k: "d", t: 2 })`, 2],
    [`strict(undefined)`, 0],
    [`unequal({ k: "e", u: "" })`, 0],
    [`literalFirst({ k: "e", u: "x" })`, "x"],
    [`loose(null)`, ""],
    [`defined({ v: null })`, null],
    [`absent({ v: "y" })`, "y"],
    [`value(undefined)`, false],
    [`found([{ k: "f" }, { k: "d", t: 4 }])`, 4],
    [`nested(undefined).k`, "f"],
  ] as const)
    assert.equal(runExample("optional-chain-test", call), expected, `optional-chain-test: ${call}`);
  // Where a chain's test leaves its receiver possibly nullish, or a call
  // rewrote it, or a getter answered the second read anew, the actual
  // source returns what its contract excludes.
  for (const [file, call] of [
    ["invalid-optional-chain-test-false", "wrong(undefined)"],
    ["invalid-optional-chain-test-undefined", "wrong(undefined)"],
    ["invalid-optional-chain-test-operand", "wrong(undefined, undefined)"],
    ["invalid-optional-chain-test-loose", "wrong(undefined)"],
    ["invalid-optional-chain-test-write", `wrong({ k: "d", t: 1 }, undefined)`],
  ])
    assert.equal(runExample(file, call), undefined, `${file}: the source returns undefined despite its object contract`);
  assert.equal(runExample("invalid-optional-chain-test-ambient",
    `(() => { let n = 0; Object.defineProperty(globalThis, "current", { configurable: true, get: () => ++n === 1 ? { k: "d", t: 1 } : { k: "e", u: "" } }); try { return wrong(); } finally { delete globalThis.current; } })()`),
    undefined, "invalid-optional-chain-test-ambient: a global accessor answers the second read with another arm");
  assert.equal(runExample("invalid-optional-chain-test-getter", "wrong(new Flip())"), "e",
    `invalid-optional-chain-test-getter: the second read answers "e" despite the "d" contract`);
  // A chain read for its truthiness: each result at the type the case
  // verifies; as a value, `&&` keeps `undefined` where the receiver is
  // nullish.
  for (const [call, expected] of [
    [`pick(new Map([["a", { ok: true, value: 1 }]]), "a")`, 1],
    [`pick(new Map([["b", { ok: false, refused: "r" }]]), "b")`, null],
    [`pick(new Map(), "z")`, null],
    [`literal({ ok: true, value: { literal: "L" } })`, "L"],
    [`literal({ ok: true, value: 3 })`, null],
    [`literal(undefined)`, null],
    [`early(undefined)`, ""],
    [`early({ ok: true, value: "v" })`, "v"],
    [`either(null, false)`, "none"],
    [`either({ ok: false, refused: "r" }, false)`, "r"],
    [`kept(undefined)`, undefined],
    [`first({ name: "" })`, "anonymous"],
    [`first({ name: "n" })`, "n"],
  ] as const)
    assert.equal(runExample("optional-chain-discriminant", call), expected, `optional-chain-discriminant: ${call}`);
  // Where the chain's truthiness failed, or a call rewrote the tested
  // `let`, or a global accessor answered the second read anew, the source
  // returns what its contract excludes.
  for (const [file, call] of [
    ["invalid-optional-chain-discriminant-else", "wrong(undefined)"],
    ["invalid-optional-chain-discriminant-write", `wrong({ ok: true, value: 1 }, { ok: false, refused: "r" })`],
  ])
    assert.equal(runExample(file, call), undefined, `${file}: the source returns undefined despite its contract`);
  assert.equal(runExample("invalid-optional-chain-discriminant-ambient",
    `(() => { let n = 0; Object.defineProperty(globalThis, "current", { configurable: true, get: () => ++n === 1 ? { ok: true, value: 1 } : { ok: false, refused: "r" } }); try { return wrong(); } finally { delete globalThis.current; } })()`),
    undefined, "invalid-optional-chain-discriminant-ambient: a global accessor answers the second read with another arm");
  assert.equal(runExample("optional-chain-receiver-narrowed", "guarded(undefined)"), 0,
    "optional-chain-receiver-narrowed: a nullish receiver takes the other arm");
  // A negated `||` or `&&` of tests: where its answer leaves a tested field
  // otherwise, a call or a test's operand wrote it, or a getter answered the
  // read anew, the source returns a name its contract excludes.
  for (const [file, call] of [
    ["invalid-negated-disjunction-else", `wrong({ name: "a" })`],
    ["invalid-negated-disjunction-arm", `wrong({ name: "a" })`],
    ["invalid-negated-conjunction", `wrong({ name: "a" }, 2)`],
    ["invalid-negated-disjunction-write", `wrong({ name: "c" })`],
    ["invalid-negated-disjunction-operand", `wrong({ name: "c" })`],
    ["invalid-negated-disjunction-getter", "wrong(new Flip())"],
  ])
    assert.equal(runExample(file, call), "a", `${file}: the source returns "a" despite its contract`);
  assert.equal(runExample("invalid-negated-disjunction-saved", `wrong({ name: "b" }, 1)`), 2,
    "invalid-negated-disjunction-saved: the saved test permits a return of 2 despite the contract 1");
  for (const [call, expected] of [
    [`rest({ name: "c" })`, "c"],
    [`rest({ name: "a" })`, "x"],
    [`tested({ name: "b" })`, "b"],
    [`conjunction({ name: "c" })`, "c"],
    [`conjunction({ name: "a" })`, "x"],
    [`other({ name: "b" }, 1)`, "b"],
    [`exact({ name: "b" }, 1)`, 1],
    [`exact({ name: "b" }, 2)`, 1],
    [`exact({ name: "a" }, 2)`, 1],
    [`doubled({ name: "b" })`, "b"],
    [`nested({ name: "d" })`, "d"],
    [`nested({ name: "c" })`, "x"],
    [`chosen({ name: "d" })`, "d"],
    [`chosenOther({ name: "b" }, 1)`, "b"],
    [`chosenOther({ name: "b" }, 2)`, "x"],
    [`operand({ name: "c" }, true)`, true],
    [`unusual([{ k: "literal", name: "bigint" }])`, true],
    [`unusual([{ k: "atom", name: "string" }])`, false],
  ] as const)
    assert.equal(runExample("negated-disjunction-test", call), expected, `negated-disjunction-test: ${call}`);
  assert.equal(runExample("invalid-map-unstable-pop","Object.keys(shrink([1, 2, 3])).length"), 2,
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
  // The manifest's member converted by its arms throws and returns what
  // `String` of it does, a TypeError of an object owning `toString` too.
  for (const text of ['{"version":{"toString":1}}', '{"version":[1,[{"toString":null}]]}', '{"version":[1,null,[2,"a"]]}',
    '{"version":{}}', '{"version":null}', '{"name":"a"}', "[]"])
    assert.equal(runExample("json-parse-manifest", `(() => { const t = ${JSON.stringify(text)}; ` +
      `const run = (f) => { try { return f(); } catch (e) { return e.constructor.name + ": " + e.message; } }; ` +
      `const v = JSON.parse(t); const s = run(() => v !== null && typeof v === "object" && "version" in v ? String(v.version) : ""); ` +
      `return run(() => version(t)) === s ? "same" : s; })()`), "same", `json-parse-manifest: ${text} converts as String does`);
  assert.equal(runExample("json-parse-manifest", `(() => { try { version('{"version":{"toString":1}}'); } catch (e) { ` +
    `return e instanceof TypeError ? e.message : "other"; } })()`), "Cannot convert object to primitive value",
    "json-parse-manifest: an object owning toString throws String's TypeError");
  assert.equal(runExample("type-error-construct", `(() => { try { fail("m"); } catch (e) { ` +
    `return [e instanceof TypeError, made("n"), (() => { try { caused("c", 7); } catch (f) { return f.cause; } })()].join(); } })()`),
    "true,TypeError: n,7",
    "type-error-construct: a TypeError thrown, and its inherited name");
  assert.equal(runExample("json-parse-own-proto", `value('{"__proto__": 1, "a": 2}', "a")`), 2,
    "json-parse-own-proto: the own __proto__ member set no prototype");
  assert.equal(runExample("invalid-field-equality-call", `(() => { const c = { kind: "a" }; return wrong(c, () => { c.kind = "b"; }); })()`), "b",
    "invalid-field-equality-call: the call's \"b\" where \"a\" is promised");
  // `!v` decides `||` where the guard answered `false`; the right operand
  // runs only where it answered `true`, after the guard's own effects.
  assert.equal(runExample("guard-negated-short-circuit", "JSON.stringify([ordered([], {}), ordered([], 5)])"),
    '[["a","b","c"],["a","c"]]', "guard-negated-short-circuit: the guard runs once, the right operand after it");
  assert.equal(runExample("guard-negated-short-circuit", "JSON.stringify([bounded({ a: 1 }, 0), both({}, {}), neither(5, 4)])"),
    '[{"a":1},[{},{}],0]', "guard-negated-short-circuit: the guarded values");
  assert.equal(runExample("invalid-guard-negated-and", "wrong(5, 0)"), 5,
    "invalid-guard-negated-and: 5 returned where a record is promised");
  assert.equal(runExample("invalid-guard-array-promise", `isNumbers(["a"])`), true,
    "invalid-guard-array-promise: the guard answers true of a string array");
  assert.equal(runExample("guard-array-promise", "JSON.stringify([count([1, 2]), count(3), isNumbers([1])])"), "[2,0,true]",
    "guard-array-promise: the guards' answers");
  assert.equal(runExample("invalid-guard-boolean-return", "isText(null)"), true,
    "invalid-guard-boolean-return: the guard answers true of null, which is no string");
  assert.equal(runExample("guard-boolean-return-boundaries", `(() => {
    const log = [];
    const answers = [counted("a", log), counted(1, log), finished("a", log), overridden("a"), nested("ab"), nested(""),
      guardOf()(1), atLeast(1, 2), atLeast(3)];
    let thrown = false;
    try { nonEmpty(""); } catch { thrown = true; }
    return JSON.stringify([answers, log, thrown]);
  })()`), '[[true,false,true,false,true,false,true,false,true],["tested","finally"],true]',
    "guard-boolean-return-boundaries: each test runs once, its effect and its throw as written, the finally after the answer");
  assert.equal(runExample("guard-boolean-return", `JSON.stringify([size({ a: 1 }), size([1, 2]), size(3), size(null), isMode("read")])`),
    "[1,2,3,0,true]", "guard-boolean-return: the guards' answers");
  assert.equal(runExample("invalid-guard-closure-callback", "allPresent([null])"), true,
    "invalid-guard-closure-callback: the guard answers true of null, which is no string");
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
    ["invalid-stated-effect-stringify", "(() => { const xs = [1, 2, 3]; return wrong(xs, { k: \"a\", span: 0, toJSON() { xs.pop(); return \"\"; } }); })()"],
    ["invalid-error-options", "(() => { const xs = [\"a\", \"b\", \"c\"]; return wrong(xs, { reason: \"r\", get cause() { xs.pop(); return 0; } }); })()"],
    ["invalid-type-error-options", "(() => { const xs = [\"a\", \"b\", \"c\"]; return wrong(xs, { reason: \"r\", get cause() { xs.pop(); return 0; } }); })()"],
    ["invalid-error-options-getter", "wrong([\"a\", \"b\", \"c\"])"],
    ["invalid-error-options-proxy", "wrong([\"a\", \"b\", \"c\"])"],
    ["invalid-error-options-class-accessor", "wrong([\"a\", \"b\", \"c\"])"],
    ["invalid-error-implicit-options-getter", "(() => { const xs = [\"a\", \"b\", \"c\"]; return wrong(xs, { reason: \"r\", get cause() { xs.pop(); return 0; } }); })()"],
    ["invalid-error-options-spread", "(() => { const xs = [\"a\", \"b\", \"c\"]; return wrong(xs, { reason: \"r\", get cause() { xs.pop(); return 0; } }); })()"],
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
  {
    // The audited listener contract under Node: a signal listener called with
    // the signal's name, exit listeners with the code, a listener ignoring
    // it; `kill` of the process's own pid at a signal with no listener ends
    // it by that signal.
    const delivered = runNode("node-process-listeners",
      "register((code) => console.log(\"exit\", code), (s) => console.log(\"signal\", s)); process.kill(process.pid, \"SIGHUP\"); setTimeout(() => { process.exitCode = 4; }, 100);");
    assert.deepEqual([delivered.stdout.split("\n"), delivered.status],
      [["signal SIGHUP", "exit 4", "exit 4"], 4], "node-process-listeners: arguments as audited");
    const killed = runNode("node-process-listeners", "register(() => {}, () => {}); stop(); setTimeout(() => console.log(\"alive\"), 500);");
    assert.deepEqual([killed.stdout, killed.signal], ["", "SIGTERM"], "node-process-listeners: kill ends the process by the signal");
    // A once listener re-delivering its signal, as `runRoot` does: the
    // process ends by it.
    const redelivered = runNode("node-process-listeners",
      "process.once(\"SIGTERM\", (s) => { console.log(\"got\", s); process.kill(process.pid, s); }); stop(); setTimeout(() => console.log(\"alive\"), 500);");
    assert.deepEqual([redelivered.stdout, redelivered.signal], ["got SIGTERM", "SIGTERM"], "node-process-listeners: re-delivery");
    // `beforeExit` again after its listener scheduled another job: two
    // invocations, each with the code and the process as `this`.
    const idle = runNode("node-process-listeners",
      "let n = 0; whenIdle(function (code) { n++; console.log(\"beforeExit\", code, this === process, n); if (n === 1) setTimeout(() => {}, 1); });");
    assert.deepEqual(idle.stdout.split("\n"), ["beforeExit 0 true 1", "beforeExit 0 true 2"],
      "node-process-listeners: beforeExit repeated, its arguments and receiver");
    // A narrowing made at registration is stale when the listener runs.
    const stale = runNode("invalid-node-process-listener-stale", "const box = { v: 1 }; register(box); box.v = undefined;");
    assert.equal(stale.status, 1, "invalid-node-process-listener-stale: the listener reads undefined and throws at exit");
    // An exit listener changes the array and throws into the caller's handler.
    const handled = runNode("invalid-node-process-exit-handler",
      "const xs = [1, 2]; process.on(\"exit\", () => { if (xs.length === 2) { xs.pop(); throw new Error(\"listener\"); } }); console.log(1 in rows(xs)); process.exitCode = 0;");
    assert.equal(handled.stdout, "false", "invalid-node-process-exit-handler: the handler goes on and the result has a hole");
  }
  {
    // `import.meta` as audited: a `data:` module has no `dirname`; a resolve
    // hook's thrown ERR_MODULE_NOT_FOUND has its `url` returned, a number;
    // other code handed the object writes a number at `url`.
    const reload = "if (import.meta.url.startsWith(\"file:\")) { const { readFileSync } = await import(\"node:fs\"); " +
      "const m = await import(\"data:text/javascript,\" + encodeURIComponent(readFileSync(new URL(import.meta.url), \"utf8\"))); " +
      "console.log(typeof m.directory()); }";
    assert.equal(runNode("invalid-import-meta-dirname", reload).stdout, "undefined",
      "invalid-import-meta-dirname: a data: module reads no dirname");
    const thrown = runNode("import-meta", reload);
    assert.deepEqual([thrown.stdout, thrown.status], ["", 1], "import-meta: a data: module's directory() throws");
    const hooked = runNode("invalid-import-meta-resolve", "const { registerHooks } = await import(\"node:module\"); " +
      "registerHooks({ resolve: (s, c, next) => { if (s !== \"probe:x\") return next(s, c); " +
      "throw Object.assign(new Error(\"hooked\"), { code: \"ERR_MODULE_NOT_FOUND\", url: 42 }); } }); " +
      "console.log(typeof located(\"probe:x\"));");
    assert.equal(hooked.stdout, "number", "invalid-import-meta-resolve: the thrown error's url is returned");
    const leaked = runNode("invalid-import-meta-escape", "console.log(typeof leaked((m) => { m.url = 1; }));");
    assert.equal(leaked.stdout, "number", "invalid-import-meta-escape: the writer replaces url");
    // The module required, other code reaches its wrapper through
    // `require.cache`: a number at the wrapper's `url` is what `import.meta.url`
    // reads, and a getter at its `isMain` runs at the module's first
    // `import.meta`.
    const wrapped = (file: string, statements: string): string => runNode(file,
      "const { createRequire } = await import(\"node:module\"); const require = createRequire(import.meta.url); " +
      `const p = ${JSON.stringify(join(import.meta.dirname, "..", "pipeline", "examples", `${file}.ts`))}; ` +
      "const m = require(p); const cached = require.cache[p]; " +
      "const w = cached[Object.getOwnPropertySymbols(cached).find((s) => s.description === \"kRequiredModuleSymbol\")]; " +
      statements).stdout;
    assert.equal(wrapped("invalid-import-meta-url", "w.url = 42; console.log(typeof m.where());"), "number",
      "invalid-import-meta-url: the wrapper's url is read");
    assert.equal(wrapped("invalid-import-meta-stale", "const box = { v: \"a\" }; " +
      "Object.defineProperty(w, \"isMain\", { get() { box.v = undefined; return false; } }); console.log(typeof m.stale(box));"),
      "undefined", "invalid-import-meta-stale: the getter runs at the first import.meta");
  }
  {
    // A timer's extra arguments reach its callback.
    const ticked = runNode("invalid-node-set-timeout-parameter", "later((n) => console.log(typeof n));");
    assert.equal(ticked.stdout, "number", "invalid-node-set-timeout-parameter: the callback receives the argument after the delay");
  }
  assert.equal(runImporting("invalid-node-structured-clone-result",
    "(() => { const outer = [0, 2]; const inner = [1]; Object.defineProperty(inner, \"extra\", { enumerable: true, get() { outer.pop(); return 0; } }); outer[0] = inner; const c = copy(outer); return [c.length, 1 in c].join(); })()"),
    "2,false", "invalid-node-structured-clone-result: a getter popping the enclosing array leaves a hole in the copy");
  assert.equal(runImporting("invalid-node-structured-clone-preserving",
    "(() => { const xs = [1, 2]; const v = [1]; Object.defineProperty(v, \"extra\", { enumerable: true, get() { xs.pop(); return 0; } }); return 1 in rows(xs, v); })()"),
    false, "invalid-node-structured-clone-preserving: a getter beside a JSON array's elements shrinks the mapped array");
  // `JSON.stringify` of that array serializes its elements alone: the getter
  // does not run.
  assert.equal(runExample("node-structured-clone",
    "(() => { let ran = 0; const v = [1]; Object.defineProperty(v, \"extra\", { enumerable: true, get() { ran++; return 0; } }); return JSON.stringify(v) + ran; })()"),
    "[1]0", "JSON.stringify of a JSON array reads its elements only");
  assert.equal(runImporting("invalid-node-readdir-buffer-encoding", "typeof names(\".\")[0]"), "object",
    "invalid-node-readdir-buffer-encoding: a Buffer name");
  assert.equal(runImporting("invalid-node-readdir-options-alias",
    "typeof names(\".\", { withFileTypes: true, encoding: \"buffer\" })[0]"), "object",
    "invalid-node-readdir-options-alias: a Buffer name through options typed by withFileTypes alone");
  assert.equal(runImporting("invalid-node-spawn-sync-stdout", "output(\"tscert-no-such-command\") === undefined"), true,
    "invalid-node-spawn-sync-stdout: a command that cannot be spawned leaves stdout undefined");
  assert.equal(runImporting("invalid-node-spawn-sync-stdio", "output(\"true\") === null"), true,
    "invalid-node-spawn-sync-stdio: an ignored stream leaves stdout null");
  assert.equal(runImporting("invalid-node-readdir-options-signal",
    "typeof names(\".\", { withFileTypes: true, encoding: \"utf8\", get signal() { this.encoding = \"buffer\"; return undefined; } })[0]"),
    "object", "invalid-node-readdir-options-signal: a signal getter switching encoding gives a Buffer name");
  assert.equal(runImporting("invalid-node-stat-test-result",
    "(() => { const P = process.getBuiltinModule(\"node:fs\").Stats.prototype; const saved = P._checkModeProperty; P._checkModeProperty = () => 7; try { return isFile(\".\"); } finally { P._checkModeProperty = saved; } })()"),
    7, "invalid-node-stat-test-result: a replaced _checkModeProperty answers 7");
  assert.equal(runImporting("invalid-node-stat-bigint", "typeof size(\".\")"), "bigint",
    "invalid-node-stat-bigint: bigint: true gives a bigint size");
  assert.equal(runImporting("invalid-node-stat-options-getter",
    "size(\".\") - process.getBuiltinModule(\"node:fs\").statSync(\".\").size"), 1,
    "invalid-node-stat-options-getter: the getter runs once inside the call");
  assert.equal(runImporting("invalid-node-stat-date-getter",
    "(() => { Object.defineProperty(process.getBuiltinModule(\"node:fs\").Stats.prototype, \"mtime\", { get() { return 42; } }); return modified(\".\"); })()"),
    42, "invalid-node-stat-date-getter: a replaced getter answers a number");
  assert.equal(runImporting("invalid-node-stat-method-getter",
    "(() => { const xs = [1, 2]; hook(xs); return 1 in rows(xs, \".\"); })()"),
    false, "invalid-node-stat-method-getter: reading isFile in a map callback leaves a hole");
  assert.equal(runImporting("invalid-node-readdir-test-result",
    "(() => { const fs = process.getBuiltinModule(\"node:fs\"); fs.Dirent.prototype.isDirectory = () => 7; return typeof flags(\".\")[0]; })()"),
    "number", "invalid-node-readdir-test-result: a replaced isDirectory answers a number");
  assert.equal(runImporting("invalid-node-readdir-recursive",
    "(() => { const fs = process.getBuiltinModule(\"node:fs\"); let ran = 0; const test = fs.Dirent.prototype.isDirectory; fs.Dirent.prototype.isDirectory = function () { ran++; return test.call(this); }; walk(\".\"); return ran > 0; })()"),
    true, "invalid-node-readdir-recursive: the walk calls each entry's isDirectory through its prototype");
  assert.equal(runImporting("invalid-node-dirent-name-accessor",
    "(() => { hide(); const fs = process.getBuiltinModule(\"node:fs\"); const e = fs.readdirSync(\".\", { withFileTypes: true })[0]; return [typeof e.name, Object.hasOwn(e, \"name\")].join(); })()"),
    "number,false", "invalid-node-dirent-name-accessor: the entry's name is the accessor's 7, not own");
  assert.equal(runImporting("invalid-node-dirent-method-getter",
    "(() => { const xs = [1, 2]; hook(xs); const fs = process.getBuiltinModule(\"node:fs\"); fs.readdirSync(\".\", { withFileTypes: true })[0].isDirectory; return xs.length; })()"),
    1, "invalid-node-dirent-method-getter: the lookup pops the array");
  assert.equal(runImporting("invalid-node-dirent-chain-insert",
    "(() => { insert({ set name(v) {}, get name() { return 7; } }); const fs = process.getBuiltinModule(\"node:fs\"); const e = fs.readdirSync(\".\", { withFileTypes: true })[0]; return [typeof e.name, Object.hasOwn(e, \"name\")].join(); })()"),
    "number,false", "invalid-node-dirent-chain-insert: an inserted ancestor's accessor takes the constructor's name");
  for (const [act, expected] of [["replace", "number"], ["remove", "undefined"]] as const)
    assert.equal(runImporting("invalid-node-dirent-test-replaced",
      `(() => { ${act}(); const fs = process.getBuiltinModule("node:fs"); return typeof fs.readdirSync(".", { withFileTypes: true })[0].isDirectory; })()`),
      expected, `invalid-node-dirent-test-replaced: after ${act}, isDirectory is no function`);
  assert.equal(runImporting("invalid-node-dirent-prototype-write",
    "(() => { replace(); const fs = process.getBuiltinModule(\"node:fs\"); return fs.readdirSync(\".\", { withFileTypes: true }).every((e) => e.isDirectory() === true); })()"),
    true, "invalid-node-dirent-prototype-write: every entry reads the replaced member");
  // `node:crypto`'s `Hash`: a second `digest` throws, `digest()` returns a
  // Buffer, a copy has no `digest`, a SHAKE algorithm reads
  // `process.noDeprecation` inside `createHash`, an inherited `_options`
  // setter runs inside it, and an `update` getter runs at the lookup.
  assert.equal(runImporting("node-crypto-hash",
    "(() => { try { twice(\"x\"); return \"returned\"; } catch (e) { return e.code; } })()"),
    "ERR_CRYPTO_HASH_FINALIZED", "node-crypto-hash: a second digest throws");
  assert.equal(runImporting("node-crypto-hash", "digestOf(\"1\", [\"a\"]).length"), 64,
    "node-crypto-hash: the hex digest of SHA-256 is 64 digits");
  assert.equal(runImporting("invalid-node-crypto-hash-buffer", "Buffer.isBuffer(use(\"x\"))"), true,
    "invalid-node-crypto-hash-buffer: digest() returns a Buffer");
  assert.equal(runImporting("invalid-node-crypto-hash-spread",
    "(() => { try { use(\"x\"); return \"returned\"; } catch (e) { return e.constructor.name; } })()"),
    "TypeError", "invalid-node-crypto-hash-spread: the copy's digest is no function");
  assert.equal(runImporting("invalid-node-crypto-hash-algorithm",
    "(() => { let ran = 0, inside = false; Object.defineProperty(process, \"noDeprecation\", { configurable: true, get() { if (inside) ran++; return true; } }); inside = true; use(\"shake128\", \"x\"); inside = false; return ran > 0; })()"),
    true, "invalid-node-crypto-hash-algorithm: at shake128 createHash reads process.noDeprecation");
  assert.equal(runImporting("invalid-node-crypto-hash-callback",
    "(() => { const xs = [\"a\", \"b\", \"c\"]; const crypto = process.getBuiltinModule(\"node:crypto\"); Object.defineProperty(Object.getPrototypeOf(crypto.createHash(\"sha256\")), \"_options\", { set(v) { xs.pop(); }, get() { return undefined; } }); return 2 in hashed(xs); })()"),
    false, "invalid-node-crypto-hash-callback: an inherited _options setter shrinks the array map visits, leaving a hole");
  assert.equal(runImporting("invalid-node-crypto-hash-method-getter",
    "(() => { const xs = [1, 2]; hook(xs); const crypto = process.getBuiltinModule(\"node:crypto\"); crypto.createHash(\"sha256\").update; return xs.length; })()"),
    1, "invalid-node-crypto-hash-method-getter: the lookup pops the array");
  // Node's `Buffer` and `TextDecoder`: a byte past the end is `undefined`, a
  // write keeps its value modulo 256, a copy has no `length`, `JSON.stringify`
  // calls `toJSON`, a replaced `toString` answers what it returns, a
  // `subarray` getter runs at the lookup; a BOM selects UTF-16, and a
  // malformed byte throws at `fatal`.
  assert.equal(runImporting("invalid-node-bytes-past-end", "last(Buffer.from(\"ab\")) === undefined"), true,
    "invalid-node-bytes-past-end: a byte past the end is undefined");
  assert.equal(runImporting("invalid-node-bytes-write", "write(Buffer.from(\"a\"), 300)"), 44,
    "invalid-node-bytes-write: 300 reads back as 44");
  assert.equal(runImporting("invalid-node-bytes-spread", "copied(Buffer.from(\"ab\")) === undefined"), true,
    "invalid-node-bytes-spread: the copy has no length");
  assert.equal(runImporting("invalid-node-bytes-json", "JSON.parse(serialized(Buffer.from(\"a\"))).type"), "Buffer",
    "invalid-node-bytes-json: JSON.stringify calls Buffer.prototype.toJSON");
  assert.equal(runImporting("invalid-node-bytes-method-replaced",
    "(() => { replace(() => 7); return typeof Buffer.from(\"a\").toString(\"utf8\"); })()"), "number",
    "invalid-node-bytes-method-replaced: a replaced toString answers a number");
  assert.equal(runImporting("invalid-node-bytes-method-getter",
    "(() => { const xs = [1, 2]; hook(xs); Buffer.from(\"ab\").subarray; return xs.length; })()"), 1,
    "invalid-node-bytes-method-getter: the lookup pops the array");
  assert.equal(runImporting("invalid-node-bytes-length-record", "measured(Buffer.from(\"ab\")) === undefined"), true,
    "invalid-node-bytes-length-record: the copy has no length");
  assert.equal(runImporting("invalid-node-bytes-program-object",
    "(() => { try { return decoded(); } catch (e) { return e.code; } })()"), "ERR_INVALID_ARG_TYPE",
    "invalid-node-bytes-program-object: decode throws on a program's object");
  assert.equal(runImporting("invalid-node-bytes-decoder-replaced",
    "(() => { replace(() => 7); return typeof new TextDecoder().decode(Buffer.from(\"a\")); })()"), "number",
    "invalid-node-bytes-decoder-replaced: a replaced decode answers a number");
  assert.equal(runImporting("invalid-node-bytes-length-shadowed",
    "(() => { shadow(\"wrong\"); return typeof Buffer.from(\"ab\").length; })()"), "string",
    "invalid-node-bytes-length-shadowed: a shadowing length answers a string");
  assert.equal(runImporting("invalid-node-bytes-in", "measured(Buffer.from(\"a\"))"), true,
    "invalid-node-bytes-in: a view has length on its prototype chain");
  assert.equal(runImporting("node-bytes-text-decoder", "decoded(Buffer.from([0xff, 0xfe, 0x61, 0x00, 0x62]))"), "a",
    "node-bytes-text-decoder: a UTF-16LE byte order mark decodes the rest's whole code units");
  assert.equal(runImporting("node-bytes-text-decoder",
    "(() => { try { return decoded(Buffer.from([0xc3, 0x28])); } catch (e) { return e.code; } })()"),
    "ERR_ENCODING_INVALID_ENCODED_DATA", "node-bytes-text-decoder: a malformed byte throws");
  assert.equal(runImporting("node-fs-stat-bigint", "/^\\d+:\\d+:\\d+:\\d+:\\d+$/.test(signature(\".\"))"), true,
    "node-fs-stat-bigint: the nanosecond times a BigIntStats owns print as integers");
  assert.equal(runImporting("invalid-node-readdir-dirent-path", "paths(\".\").every((p) => p === undefined)"), true,
    "invalid-node-readdir-dirent-path: an entry has no path");
  assert.equal(runImporting("invalid-node-assert-deep-preserving",
    "(() => { const s = Symbol(\"k\"); const xs = []; const hooked = (pop) => { const o = { a: 1 }; Object.defineProperty(o, s, { enumerable: true, get() { if (pop) xs.pop(); return 1; } }); return o; }; xs.push(hooked(true), hooked(false)); return 1 in checked(xs, hooked(false)); })()"),
    false, "invalid-node-assert-deep-preserving: a symbol getter a passing deepEqual reads shrinks the mapped array");
  assert.equal(runImporting("invalid-node-assert-catch-continue",
    "(() => { const xs = [1, 2]; const saved = Error.prepareStackTrace; Error.prepareStackTrace = () => { xs.pop(); return \"\"; }; try { return 1 in rows(xs, 2); } finally { Error.prepareStackTrace = saved; } })()"),
    false, "invalid-node-assert-catch-continue: prepareStackTrace run by a failing equal shrinks the mapped array");
  assert.equal(runImporting("invalid-node-assert-throws-callback",
    "(() => { const xs = [1, 2]; return 1 in rows(xs, () => { xs.pop(); throw new Error(\"x\"); }); })()"),
    false, "invalid-node-assert-throws-callback: the block shrinks the mapped array");
  assert.equal(runImporting("node-assert-strict",
    "(() => { const saved = Error.prepareStackTrace; Error.prepareStackTrace = () => { throw 7; }; try { return [reason(2), reason(1), first([4]), same([1, 2]).length].join(); } finally { Error.prepareStackTrace = saved; } })()"),
    "a number,same,4,2", "node-assert-strict: a hook's thrown number reaches the handler; passing calls");
  assert.equal(runExample("invalid-parse-int-overload", "Number.isNaN(fromFlag(true))"), true,
    "invalid-parse-int-overload: parseInt of a Boolean converts it to \"true\", NaN");
  assert.equal(runExample("invalid-from-entries-iterable",
    "(() => { let ran = 0; build({ *[Symbol.iterator]() { ran++; yield [\"a\", 1]; } }); return ran; })()"),
    1, "invalid-from-entries-iterable: Object.fromEntries steps a program's iterator");
  assert.equal(runExample("invalid-array-from-iterator",
    "(() => { const xs = [1, 2]; const items = { length: 1, *[Symbol.iterator]() { xs.pop(); yield 0; } }; return 1 in grow(xs, items); })()"),
    false, "invalid-array-from-iterator: a length record's own iterator shrinks the mapped array, leaving a hole");
  assert.equal(runExample("invalid-regexp-object-pattern",
    "(() => { let read = 0; copied({ get [Symbol.match]() { read++; return true; }, source: \"a\", flags: \"\" }); return read; })()"),
    1, "invalid-regexp-object-pattern: new RegExp reads an object pattern's Symbol.match getter");
  assert.equal(runExample("invalid-instanceof-error-message",
    "typeof text(Object.create(Error.prototype, { message: { value: 5 } }))"),
    "number", "invalid-instanceof-error-message: an object holding Error.prototype has a numeric message");
  // An `Error`-derived message: read through the chain, `""` where omitted,
  // seen by `in`, left out of keys and spreads, serialized where a replacer
  // names it.
  assert.equal(runExample("error-subclass",
    `[decode("a\\\\b"), decode("ab"), located([0, 1]).message, deeper(), JSON.stringify(omitted()), observed()].join(";")`),
    'declined;ab;here;deep@0;"";true,at,true,true', "error-subclass: the messages and observations");
  // A native weak table: an entry set through the table and read twice, its
  // deletion of another key through the alias `set` returns.
  assert.equal(runExample("native-weakmap", "lookup({}, {})"), 14);
  assert.equal(runExample("invalid-native-weakmap-key", `(() => {
    try { wrong(); } catch (error) { return error instanceof TypeError; }
    return false;
  })()`), true, "a primitive key makes set throw TypeError");
  assert.equal(runExample("native-weakmap", `(() => {
    const table = new WeakMap();
    for (const key of [undefined, null, false, 1, 1n, "key", Symbol.for("key")]) {
      if (table.get(key) !== undefined || table.has(key) || table.delete(key)) return false;
      try { table.set(key, 1); return false; } catch (error) {
        if (!(error instanceof TypeError)) return false;
      }
    }
    for (const key of [{}, () => {}, Symbol("key")]) {
      if (table.set(key, 1) !== table || table.get(key) !== 1 || !table.has(key) || !table.delete(key)) return false;
    }
    return true;
  })()`), true, "native weak keys: objects and unregistered symbols; invalid keys are absent on reads");
  assert.equal(runExample("invalid-native-weakmap-iterable", `(() => {
    let calls = 0;
    wrong({ [Symbol.iterator]() { calls++; return [][Symbol.iterator](); } });
    return calls;
  })()`), 1, "iterable construction executes client code");
  assert.equal(runExample("invalid-native-weakmap-missing", "wrong({})"), undefined);

  assert.equal(runExample("error-subclass-methods", `[direct(), deeper()].join(";")`), "at: x;at: y (2)at: ",
    "error-subclass-methods: the methods through the chain");
  // `Error`'s options at a stated `cause`: each construction gives the
  // message; a write of the own `cause` keeps it non-enumerable.
  assert.equal(runExample("error-options", `[...make("m", 1, { cause: 2 }, undefined), ...dense(["a", "b"])].join()`),
    "m,m,m,m,m,m,m,m,m,a,b", "error-options: each construction's message");
  assert.equal(runExample("invalid-error-super-options-getter", `(() => { let runs = 0; make("m", { get cause() { runs++; return 0; } }); return runs; })()`), 1,
    "invalid-error-super-options-getter: super(m, o) runs the getter at cause");
  assert.equal(runExample("invalid-error-subclass-cause-write", "keys().length"), 0,
    "invalid-error-subclass-cause-write: the assigned own cause stays non-enumerable");
  assert.throws(() => runExample("invalid-error-subclass-stack-method", "trace()"), /not a function/,
    "invalid-error-subclass-stack-method: the own stack shadows the method");
  assert.equal(runExample("invalid-error-subclass-null-message", "read()"), "null",
    "invalid-error-subclass-null-message: ToString converts null");
  for (const file of ["invalid-error-subclass-stack-copy", "invalid-error-subclass-alias-stack"])
    assert.equal(runExample(file, "copied()"), undefined, `${file}: the copy has no stack`);
  // A write of `message` or `stack` onto an instance: `stack` stays
  // non-enumerable; `message` does where one was passed, and becomes
  // enumerable where none was.
  assert.equal(JSON.stringify(runExample("invalid-error-subclass-assign-target", "relabelled()")), '["message"]',
    "invalid-error-subclass-assign-target: an enumerable message");
  assert.equal(JSON.stringify(runExample("invalid-error-subclass-assign-alias", "relabelled()")), '["message","tag"]',
    "invalid-error-subclass-assign-alias: the hidden message copied, enumerable");
  for (const file of ["invalid-error-subclass-narrowed-write", "invalid-error-subclass-narrowed-computed"])
    assert.equal(JSON.stringify(runExample(file,
      `(() => { const box = { v: { kind: "record", name: 1 } }; return traced(box, (b) => { b.v = new Decline("x"); }, "stack"); })()`)),
      '["kind"]', `${file}: the callback put an instance there, whose stack stays non-enumerable`);
  // A reserved write through a structural parameter an instance meets: the
  // instance's `stack` stays non-enumerable.
  for (const file of ["invalid-error-subclass-pattern-write", "invalid-reserved-update",
      "invalid-reserved-logical", "invalid-reserved-callback"])
    assert.equal(JSON.stringify(runExample(file, `traced(new (class extends Error {})("x"))`)), "[]",
      `${file}: the instance's stack stays non-enumerable`);
  assert.equal(runExample("invalid-error-subclass-spread", "main()"), undefined,
    "invalid-error-subclass-spread: the copy has no message");
  assert.equal(runExample("error-name",
    `[named(), described(new Failure("y")), inherited(), found(), listed().length, both().length, wrapped().message].join(";")`),
    "Error;Error: y;Error;true;0;2;boom", "error-name: the name Error.prototype holds, read, found and not listed");
  assert.equal(runExample("blocker-error-options-return", "use().name"), "Error", "blocker-error-options-return: the name");
  assert.equal(runExample("blocker-error-super-options-return", "use().name"), "Error",
    "blocker-error-super-options-return: the name a subclass inherits");
  assert.equal(runExample("invalid-error-name-spread", "main()"), undefined, "invalid-error-name-spread: the copy has no name");
  assert.equal(runExample("invalid-error-name-write", "main()"), 5, "invalid-error-name-write: a number written over the name");
  assert.equal(runExample("invalid-error-prototype-name-getter", "main()"), 5,
    "invalid-error-prototype-name-getter: the getter's number");
  for (const file of ["invalid-error-subclass-name-field", "invalid-error-subclass-name-write"])
    assert.equal(runExample(file, "main()"), "Failure", `${file}: the instance's own name`);
  assert.equal(runExample("error-subclass-json-replacer", "text()"), '{"message":"x"}',
    "error-subclass-json-replacer: the replacer reads the message");
  assert.equal(runExample("instanceof-error", "[isError(new Error(\"x\")), isError({ message: \"x\" })].join()"),
    "true,false", "instanceof-error: the walk");
  // `instanceof Map` and `instanceof Set`: a copy of nested collections
  // keeps their sharing; an object holding the prototype without the slots
  // passes the test and the native members throw on it; a subclass's own
  // iterator is the program's; a write through the test breaks the caller's
  // element contract.
  assert.equal(runExample("blocker-instanceof-map-set", `(() => {
    const inner = new Set([1]); const outer = new Map([["a", inner], ["b", inner]]);
    const copy = copied(outer, new Map());
    return [copy !== outer, copy.get("a") !== inner, copy.get("a") === copy.get("b"), [...copy.get("a")].join()].join();
  })()`), "true,true,true,1", "blocker-instanceof-map-set: the copy");
  assert.throws(() => runExample("invalid-instanceof-map-counterfeit", "counterfeit()"), /incompatible receiver/,
    "invalid-instanceof-map-counterfeit: get on an object holding Map.prototype");
  assert.throws(() => runExample("invalid-instanceof-set-counterfeit", "counterfeit()"), /incompatible receiver/,
    "invalid-instanceof-set-counterfeit: has on an object holding Set.prototype");
  assert.equal(runExample("invalid-instanceof-map-shadowed", "shadowed()"), 1,
    "invalid-instanceof-map-shadowed: the loop ran the subclass's iterator");
  assert.equal(runExample("invalid-instanceof-map-write", "typeof caller()"), "string",
    "invalid-instanceof-map-write: the caller's map holds a string");
  // An imported class's `instanceof` walks the chain for the prototype its
  // declaration creates; where it fails, a record with the class's members
  // is still returned, and a class binding its module writes tests another
  // class's prototype.
  assert.equal(runImporting("instanceof-class-value-import",
    "[tests(), isFailure({ operation: \"x\" }), atStart, lineOf(new ParseFailure(2))].join()"),
    "true,false,true,2", "instanceof-class-value-import: the walk");
  assert.equal(runImporting("invalid-instanceof-class-else-value-import",
    "typeof label({ operation: \"x\", message: \"m\", name: \"n\" })"),
    "object", "invalid-instanceof-class-else-value-import: the failed arm returns the record");
  assert.equal(runImporting("invalid-instanceof-rebound-value-import", "rebound(new Rebound())"),
    false, "invalid-instanceof-rebound-value-import: an instance made before the write is no instance");
  assert.equal(runImporting("invalid-instanceof-hooked-value-import", "String(f(\"text\"))"),
    "undefined", "invalid-instanceof-hooked-value-import: the hook answers true of a string");
  assert.equal(runImporting("invalid-instanceof-suppressed-value-import", "suppressed(new Suppressed())"),
    false, "invalid-instanceof-suppressed-value-import: an instance made before the write is no instance");
  assert.equal(runImporting("invalid-instanceof-getter-value-import", "1 in marked()"),
    false, "invalid-instanceof-getter-value-import: the getter shrinks the mapped array, leaving a hole");
  for (const form of ["default", "heritage", "setter"])
    assert.equal(runImporting(`invalid-instanceof-${form}-hook-value-import`, "String(f(\"text\"))"),
      "undefined", `invalid-instanceof-${form}-hook-value-import: the defined method answers true of a string`);
  assert.equal(runExample("invalid-number-value-object",
    "(() => { const xs = [{}, {}]; xs[0] = { valueOf() { xs.pop(); return 1; } }; return 1 in values(xs); })()"),
    false, "invalid-number-value-object: an object's valueOf shrinks the mapped array, leaving a hole");
  assert.equal(runExample("number-value", "parts(\"1.20.3\").join()"), "1,20,3", "number-value: the parts");
  assert.equal(runExample("json-stringify-arrays","[nested([[1, 2], []]), ...mixed([[1, { a: [true] }], null])].join(\" \")"),
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
  // A complete `ReadonlySet<string>` and `ReadonlyMap<string, number>`,
  // each answering values of its declared types, whose iterator, or an entry's
  // getter, pops a separate array: the copy holds strings, and the call
  // changed the store.
  assert.equal(runExample("invalid-set-from-readonly-set",
    `(() => { const xs = [1, 2]; const inner = new Set(["a"]); const names = { get size() { return inner.size; }, has: (k) => inner.has(k), forEach(f, t) { inner.forEach((v) => f.call(t, v, v, names)); }, entries: () => inner.entries(), keys: () => inner.keys(), values: () => inner.values(), [Symbol.iterator]() { xs.pop(); return inner.values(); } }; return [xs.length, typeof [...copy(names)][0], xs.length].join(); })()`),
    "2,string,1", "invalid-set-from-readonly-set: new Set runs the set's iterator, which pops another array");
  assert.equal(runExample("invalid-map-from-readonly-map",
    `(() => { const xs = [1, 2]; const inner = new Map([["a", 5]]); const entry = ["a", 5]; Object.defineProperty(entry, 0, { get() { xs.pop(); return "a"; } }); const names = { get size() { return inner.size; }, get: (k) => inner.get(k), has: (k) => inner.has(k), forEach(f, t) { inner.forEach((v, k) => f.call(t, v, k, names)); }, entries: () => inner.entries(), keys: () => inner.keys(), values: () => inner.values(), [Symbol.iterator]: () => [entry][Symbol.iterator]() }; const copied = copy(names); return [typeof [...copied.keys()][0], typeof copied.get("a"), xs.length].join(); })()`),
    "string,number,1", "invalid-map-from-readonly-map: new Map reads an entry's getter, which pops another array");
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
  for (const file of ["invalid-field-narrowing-for-of-closure", "invalid-field-narrowing-for-of-callback"])
    assert.throws(() => runExample(file,
      `(() => { const h = { statement: { k: "block", statements: [1] } }; return count(h, h); })()`), /length/,
      `${file}: the reread after the loop reads \`length\` of undefined`);
  assert.throws(() => runExample("invalid-field-narrowing-for-of-write",
    `(() => { const h = { statement: { k: "block", statements: [1] } }; return count(h, h); })()`), /length/,
    "invalid-field-narrowing-for-of-write: the reread after the loop reads `length` of undefined");
  assert.equal(runExample("invalid-own-property-descriptors-value", `extra({ a: 1, x: "s" })`), "s",
    "invalid-own-property-descriptors-value: the descriptor's value is a string returned at number");
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
  assert.equal(runExample("function-declaration-before-initialization", `JSON.stringify([early, throughClosure].map((f) => {
    try { f(); return "none"; } catch (e) { return e instanceof ReferenceError; } }))`),
    "[true,true]", "function-declaration-before-initialization: the declaration's call, direct or through a closure, reads the binding before its initialization");
  assert.equal(runExample("function-declarations-in-body", `JSON.stringify([hoisted(), factorial(5), parity(10), parity(7),
    filtered(["a", "b", "c"], ["b"]), pair(4), inBlock(true)])`), `[4,120,true,false,["a","c"],2,1]`,
    "function-declarations-in-body: each declaration is callable from its block's entry");
  assert.equal(runExample("function-declaration-early-recursion", "start()"), 0,
    "function-declaration-early-recursion: the early declaration calls itself through its binding");
  assert.equal(runExample("invalid-function-declaration-stale", "stale()"), "s",
    "invalid-function-declaration-stale: the declaration's write reaches the read TypeScript narrowed to number");
  assert.equal(runExample("module-cells", "JSON.stringify([bump(), bump(), cached(), limited(), afterCall()])"), "[1,2,\"computed\",6,3]",
    "module-cells: the functions read and write the module's cells");
  assert.throws(() => runExample("module-cell-before-initialization", "sum()"), /ReferenceError|before initialization/,
    "module-cell-before-initialization: the initialization's call reads the cell before its declaration");
  assert.equal(runExample("invalid-module-cell-stale", "stale()"), "s",
    "invalid-module-cell-stale: the call's write reaches the read TypeScript narrowed to number");
  assert.equal(runExample("module-cell-saved-value", "saved()"), 0,
    "module-cell-saved-value: the constant keeps the value read before the write");
  assert.equal(runExample("blocker-module-assignment",
    `JSON.stringify([(use(), use(), next()), (release(), next()), (kept("a"), kept("b"), retire("x")), retire("y")])`),
    `[{"generation":3},{"generation":3},"x","x"]`,
    "blocker-module-assignment: the updates and logical assignments read and write the module's cells");
  assert.equal(runExample("early-cell-update-order", "JSON.stringify([compound(), logical(), postfix(), local()])"),
    `[6,"vvvfalse3",607,21]`,
    "early-cell-update-order: each update reads before its right side, each logical assignment runs its right side only where it writes");
  for (const name of ["invalid-early-const-update", "invalid-early-const-assign"])
    assert.throws(() => runExample(name, "test()"), /TypeError|Assignment to constant/,
      `${name}: the write of the constant throws`);
  assert.throws(() => runExample("module-cell-update-before-initialization", "total()"), /ReferenceError|before initialization/,
    "module-cell-update-before-initialization: the initialization's update reads the cell before its declaration");
  assert.equal(runExample("invalid-module-cell-update-stale", "retire('x')"), null,
    "invalid-module-cell-update-stale: the call's write reaches the read TypeScript narrowed to string");
  assert.throws(() => runImporting("certified-cell-cycle-value-import", "total()"), /ReferenceError|before initialization/,
    "certified-cell-cycle-value-import: `left` runs before `right`'s cell is initialized");
  for (const name of ["invalid-object-growth-early-alias", "invalid-loop-object-growth-early-alias"]) {
    assert.equal(runExample(name, `(() => { try { stale(); return "none"; } catch (e) { return e instanceof TypeError; } })()`),
      true, `${name}: the retained alias reads a number as a string`);
  }
  for (const [name, input] of [["invalid-loop-object-growth-escape", `["y", "x"]`],
    ["invalid-loop-object-growth-outer-escape", `[["y"], ["x"]]`]] as const) {
    assert.equal(runExample(name, `(() => { try { aliased(${input}); return "none"; } catch (e) { return e instanceof TypeError; } })()`),
      true, `${name}: the view bound in an earlier iteration reads the number 1 at x as a string`);
  }
  assert.equal(runExample("invalid-early-binding-stale", "stale()"), "s",
    "invalid-early-binding-stale: the closure's write reaches the read TypeScript narrowed to number");
  assert.equal(runImporting("invalid-node-path-join-callback",
    `(() => { const xs = ["a", "b", "c"]; const path = process.getBuiltinModule("node:path"); const normalize = path.posix.normalize; path.posix.normalize = (p) => { xs.pop(); return normalize(p); }; try { return 2 in parents(xs); } finally { path.posix.normalize = normalize; } })()`),
    false, "invalid-node-path-join-callback: a replaced posix.normalize shrinks the array map visits, leaving a hole");
  // `crypto.fips`, declared `boolean`, is a deprecated accessor answering a
  // number on the module's object, and no named export holds it.
  assert.equal(runImporting("invalid-node-default-import-unreviewed",
    `(() => { process.noDeprecation = true; return [typeof probe(), "fips" in process.getBuiltinModule("node:crypto"), Object.getOwnPropertyDescriptor(process.getBuiltinModule("node:crypto"), "fips").enumerable].join(); })()`),
    "number,true,false", "invalid-node-default-import-unreviewed: crypto.fips answers a number and is no enumerable own property, so no named export");
  // A class's method replaced through its `prototype`: a write changes
  // what every instance's call answers; `Reflect.set` of a function
  // returning a number makes the `boolean` call return 7.
  assert.equal(runExample("invalid-class-prototype-write", "(() => { const before = check(); replace(); return [before, check()].join(); })()"),
    "false,true", "invalid-class-prototype-write: the written prototype answers every instance's call");
  assert.equal(runExample("invalid-reflect-method-replaced",
    "(() => { replace(); return typeof check(); })()"),
    "number", "invalid-reflect-method-replaced: the replaced method returns a number where boolean is declared");
  // `argon2`, which an augmentation states as an enum whose `tag` is 1, is
  // a function under Node, whose `tag` is undefined.
  assert.equal(runImporting("invalid-node-augmented-enum", `[typeof process.getBuiltinModule("node:crypto").argon2, probe() === undefined].join()`),
    "function,true", "invalid-node-augmented-enum: argon2 is a function and its tag undefined");
  // A program module's re-export of `node:os`'s `hostname`, by name or by
  // `export *`, binds `node:os`'s own function.
  for (const name of ["invalid-node-reexport-named", "invalid-node-reexport-star"])
    assert.equal(runImporting(name, `probe() === process.getBuiltinModule("node:os").hostname()`), true,
      `${name}: the re-exported hostname is node:os's own`);
  // A member of `node:path`'s object replaced through its default import,
  // written or through an alias of the object: the replaced `dirname`
  // shrinks the array `map` visits, leaving a hole.
  for (const name of ["invalid-node-default-import-write", "invalid-node-default-import-value"])
    assert.equal(runImporting(name,
      `(() => { const path = process.getBuiltinModule("node:path"); const dirname = path.dirname; const xs = ["a", "b", "c"]; hook(xs); try { return 2 in parents(xs); } finally { path.dirname = dirname; } })()`),
      false, `${name}: a replaced dirname shrinks the array map visits, leaving a hole`);
  assert.equal(runImporting("invalid-node-path-resolve-callback",
    `(() => { const xs = ["a", "b", "c"]; process.cwd = () => { xs.pop(); return "/"; }; return 2 in absolute(xs); })()`),
    false, "invalid-node-path-resolve-callback: a replaced process.cwd shrinks the array map visits, leaving a hole");
  assert.equal(runImporting("invalid-node-exec-stdout-ignored", `run(["-e", ""])`), null,
    "invalid-node-exec-stdout-ignored: standard output not piped, the result is null at string");
  assert.equal(runExample("invalid-array-flat-map-value", "first()"), 1,
    "invalid-array-flat-map-value: the flattened array's number is returned at number[]");
  assert.equal(runExample("invalid-array-flat-objects", "typeof flatObjects([[1]])[0]"), "number",
    "invalid-array-flat-objects: the flattened element is a number at object[]");
  assert.equal(runExample("invalid-array-splice-tuple", "emptied([1, 2])"), undefined,
    "invalid-array-splice-tuple: the spliced tuple's second position is missing");
  assert.equal(runExample("array-splice-flat", "JSON.stringify([removed([\"a\", \"b\", \"c\"], 1), total([[1, , 2], [3]]), levels([[[1]], [[2, 3]]])])"),
    '[["b","c","end"],6,[[1],[2,3]]]', "array-splice-flat: the removed elements, a sum over a holey row, one level flattened");
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
  assert.equal(runExample("invalid-push-spread-wider", `wrong([1], ["s"])`), "s",
    "invalid-push-spread-wider: a string pushed through the wider view lands in the array of numbers");
  assert.equal(runExample("invalid-push-receiver-element", "wrong([], null)"), "other",
    "invalid-push-receiver-element: the array of Stmt holds a { k: \"other\" }");
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
  // An enum's reverse keys: at each value's key a member's name, the last
  // member with the value, a member known only at run time replacing an
  // earlier name; at a number outside the values, at a string member's
  // value, and on an environment's object without them, undefined.
  assert.equal(runEmitted("enum-reverse-keys",
    "JSON.stringify([closedName(4), openName(7), openLiteral(), objectName(openObject()), suffixed(1)])"),
    '["C","D","D","E",true]');
  assert.throws(() => runEmitted("invalid-enum-reverse-number", "levelName(5)"), /reading .length./);
  assert.throws(() => runEmitted("invalid-enum-reverse-outside", "outside()"), /reading .length./);
  assert.throws(() => runEmitted("invalid-string-enum-reverse", `unitName("name")`), /reading .length./);
  assert.throws(() => runEmitted("invalid-ambient-enum-reverse", "globalThis.Grade = { Low: 0, High: 1 }; lowName()"), /reading .length./);
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
    // A closure's parameter slot narrowed until its next write; a write, or
    // an inner closure's write, between the test and the read gives
    // `undefined` where a string is returned.
    ["closure-parameter-slot", "const p = { kind: 'paren', inner: { kind: 'call', callee: { kind: 'name', text: 'f' }, args: [{ kind: 'paren', inner: { kind: 'name', text: 'a' } }] } }; JSON.stringify([unwrap(p).kind, names(p), area({ kind: 'square', side: 2 }), later(p)(), later({ kind: 'paren', inner: { kind: 'name', text: 'a' } })()])", '["call",["f","a"],4,"","a"]'],
    // `filter` at a guard keeps exactly the values the guard answers `true`
    // for, the one writing the receiver included; a guard answering `true`
    // of `null` leaves `null` in a result read at `string[]`.
    ["filter-guard-callback", "JSON.stringify([defined([{ kind: 'declaration', name: 'f', body: true, modifiers: [{ kind: 'declare' }] }], 'f'), defined([{ kind: 'declaration', name: 'f', body: true }], 'f'), declarations([{ kind: 'other', name: 'x' }, { kind: 'declaration', name: 'y', body: false }]).length, evenStrings(['a', 1, 'b', 'c']), none(['a']), overwriting(['a', 1, 'b'])])", '[false,true,1,["a","b"],[],["a","b"]]'],
    ["invalid-filter-guard-promise", "JSON.stringify(strings([null, 'a']))", '[null,"a"]'],
    // A guard passed by name keeps, and finds, exactly the values it
    // answers `true` for; one answering `true` of `null` leaves `null` in a
    // result read at `string[]`.
    ["filter-guard-value", "const ds = [{ kind: 'other' }, { kind: 'declaration', body: true }]; JSON.stringify([defined(ds), first(ds), first([{ kind: 'other' }]), others(ds).length])", '[true,true,false,1]'],
    ["invalid-filter-guard-value-promise", "JSON.stringify(strings([null, 'a']))", '[null,"a"]'],
    // A guard passed by name to `find` popping the array `find` searches is
    // called at `undefined` once the array is shorter than the length `find`
    // read, and reading its `kind` throws.
    ["invalid-find-guard-shrink", "(() => { try { return String(first()); } catch (e) { return e instanceof TypeError; } })()", true],
    ["invalid-closure-parameter-write", "String(textOf({ kind: 'name', text: 'a' }, { kind: 'paren', inner: { kind: 'name', text: 'b' } }))", "undefined"],
    ["invalid-closure-parameter-cell", "String(textOf({ kind: 'name', text: 'a' }, { kind: 'paren', inner: { kind: 'name', text: 'b' } }))", "undefined"],
    // A path rooted at a `let` slot holds what its test saw until the root's
    // next write; a write, a back edge, a `finally`, a closure's write, an
    // alias's write or a call through a member that is not stable between
    // the test and the read gives `undefined` where a string is returned.
    ["slot-path", "const n = { kind: 'index', object: { kind: 'name', text: 'o' }, key: { kind: 'name', text: 'k' } }; const p = { kind: 'paren', inner: n }; JSON.stringify([namesKey(p, 'k'), namesKey(p, 'j'), keyText(p), retested(n, { kind: 'name', text: 'x' }), retested(n, n)])", '[true,false,"k","","k"]'],
    // A guard writing the field it tests, or a call between the guard and
    // the reread, leaves a number where the list's length is returned.
    ["invalid-guard-field-write", "String(wrong({ args: [1, 2] }))", "undefined"],
    ["invalid-guard-field-saved", "String(wrong({ f: 'a' }))", "undefined"],
    ["invalid-guard-field-saved-callback", "String(wrong({ f: 'a' }, (x) => { x.f = 0; return 'a'; }))", "undefined"],
    ["invalid-guard-field-call", "(() => { const b = { args: [1, 2] }; return String(wrong(b, () => { b.args = 0; })); })()", "undefined"],
    ["invalid-guard-field-native-callback", "String(wrong({ args: [1, 2] }, [3]))", "undefined"],
    ["invalid-slot-path-write", "String(keyText({ kind: 'index', key: { kind: 'name', text: 'a' } }, { kind: 'index', key: { kind: 'paren', inner: { kind: 'name', text: 'b' } } }))", "undefined"],
    ["invalid-slot-path-loop", "String(lastKey({ kind: 'index', key: { kind: 'name', text: 'a' } }, { kind: 'index', key: { kind: 'paren', inner: { kind: 'name', text: 'b' } } }, 2))", "undefined"],
    ["invalid-slot-path-finally", "String(keyText({ kind: 'index', key: { kind: 'name', text: 'a' } }, { kind: 'index', key: { kind: 'paren', inner: { kind: 'name', text: 'b' } } }, () => {}))", "undefined"],
    ["invalid-slot-path-pattern", "String(keyText({ kind: 'index', key: { kind: 'name', text: 'a' } }, { kind: 'index', key: { kind: 'paren', inner: { kind: 'name', text: 'b' } } }))", "undefined"],
    ["invalid-slot-path-closure", "String(keyText({ kind: 'index', key: { kind: 'name', text: 'a' } }, { kind: 'index', key: { kind: 'paren', inner: { kind: 'name', text: 'b' } } }))", "undefined"],
    ["invalid-slot-path-alias", "String(keyText({ key: { kind: 'name', text: 'a' } }, { kind: 'paren', inner: { kind: 'name', text: 'b' } }, 1))", "undefined"],
    ["invalid-slot-path-call", "(() => { const b = { key: { kind: 'name', text: 'a' } }; return String(keyText(b, 1, () => { b.key = { kind: 'paren', inner: b.key }; })); })()", "undefined"],
    // A member of an intersection's operand holds what its test saw until
    // a write: one through an alias, or a call's, between the test and the
    // read gives `null` where a string is returned.
    ["path-test-intersection-application", "JSON.stringify([count({ k: 'scheme', binders: [{ name: 'T', bound: { k: 'leaf', n: 1 }, default: { k: 'leaf', n: 2 } }, { name: 'U', bound: null, default: null }] }), defaultOf({ name: 'T', bound: null, default: null }).n, boundOr({ name: 'T', bound: 0, default: null })])", "[3,0,0]"],
    ["invalid-path-test-intersection-alias", "String(wrong({ name: 'T', bound: null, default: 'a' }))", "null"],
    ["invalid-path-test-intersection-call", "(() => { const b = { name: 'T', bound: null, default: 'a' }; return String(wrong(b, () => { b.default = null; })); })()", "null"],
    ["invalid-path-test-intersection-application", "String(wrong({ name: 'T', bound: 'a', default: null }))", "null"],
    // A program's object with its own `has`, or its own iterator, is a
    // `ReadonlySet`: its `has` or its iterator's `next` shrinks the list,
    // and `findIndex` hands the callback `undefined`.
    ["invalid-readonly-set-has-effect", "(() => { const list = [1, 2], seen = []; const drain = { next: () => ({ done: true, value: undefined }), [Symbol.iterator]() { return this; } }; first({ size: 0, has: (n) => { seen.push(n); list.pop(); return false; }, forEach: () => {}, keys: () => drain, values: () => drain, entries: () => drain, [Symbol.iterator]: () => drain }, list); return String(seen[1]); })()", "undefined"],
    ["invalid-readonly-set-iterator-native", "(() => { const list = [1, 2]; const drain = { next: () => { list.pop(); return { done: true, value: undefined }; }, [Symbol.iterator]() { return this; } }; return String(first({ size: 0, has: () => false, forEach: () => {}, keys: () => drain, values: () => drain, entries: () => drain, [Symbol.iterator]: () => drain }, list)); })()", "undefined"],
    ["readonly-collection-views", "JSON.stringify([size(), merged(['a', 'b']), scoped(['a', 'a', 'b']), counted(['x', 'y', 'x'])])", "[0,2,4,[\"x\",\"y\"]]"],
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
    ["read-narrows-path", "JSON.stringify([initializerWidth([{ initializer: 'ab' }]), measured(new Measure(), [{ initializer: 'abc' }]), guarded([{}]), returned([{ kind: 'k', initializer: 'a' }])])", "[2,3,0,2]"],
    // The false edge of a truthiness test keeps `""`.
    ["invalid-read-narrows-path-falsy", "JSON.stringify(wrong([{ initializer: '' }]))", '""'],
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
  // A pattern binding the loop is destructured in the closing region: a
  // `break` after it closes once, a throwing default closes the iterator and
  // its error leaves, the end closes nothing; each iteration's bindings are
  // its own.
  const items = "new Items(new Link({ name: 'ab' }, ['a', 1], new Link({ name: 'c', size: 5 }, ['b', 2], null)), { closed: 0 })";
  const itemCloses = (call: string) =>
    runExample("for-of-pattern-program-iterable", `const l = ${items}; const r = ${call}; JSON.stringify([r, l.log.closed])`);
  assert.equal(itemCloses("sizes(l)"), "[7,0]");
  assert.equal(itemCloses("firstSized(l)"), '["c",1]');
  assert.equal(itemCloses("strict(l).message"), '["no size for ab",1]');
  assert.equal(itemCloses("namers(l).map((f) => f()).join()"), '["ab,c",0]');
  assert.equal(runExample("for-of-pattern-program-iterable",
    "const p = new Pairs(new Link({ name: '' }, ['a', 1], new Link({ name: '' }, ['b', 2], null))); [indexed(['x', 'y']), spelled(['x', 'y']), total(p), keyed(p)].join('|')"),
    "0:x 1:y |01xy|3|a=1;b=2;");
  // A short yielded array leaves the position `undefined`; a default
  // refilling the array the iterator holds leaves `b` `undefined` too, the
  // array's iterator having found its end.
  assert.equal(runExample("invalid-for-of-pattern-program-iterable", "String(second(new Rows(new Row([1], null))))"),
    "undefined");
  assert.equal(runExample("for-of-pattern-program-iterable-default-refused", "JSON.stringify(grown(new Shared([])))"),
    "[0,null]");
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
  // A replacement callback is handed an unmatched capture as `undefined`,
  // and no `groups` where no group is named; one shrinking the array `map`
  // steps leaves a hole.
  assert.equal(runExample("invalid-regexp-replace-capture", `last("b")`), undefined);
  assert.equal(runExample("invalid-regexp-replace-groups", `groups("a")`), undefined);
  assert.equal(runExample("invalid-regexp-replace-callback-effect", `1 in wrong(["a", "a"])`), false);
  // A regex shared before the call: a `lastIndex` whose `valueOf` compiles
  // another pattern hands the callback the offset where the capture was.
  assert.equal(runExample("invalid-regexp-replace-shared",
    `typeof first("b", (r) => { r.lastIndex = { valueOf() { r.compile("b"); return 0; } }; })`), "number");
  // `lastIndex` is a regex's own property, not enumerable: `in` finds it, a
  // copy lacks it.
  assert.equal(runExample("invalid-regexp-lastindex-in", "hasState(/a/)"), true);
  assert.equal(runExample("invalid-regexp-lastindex-view", "viewed()"), undefined);
  // A function inherits `apply` and `call`, which `in` finds; an open record
  // arm may own `call` at another type. An error inherits `name` and
  // `message` from `Error.prototype`: at `{ name?: number }` or
  // `{ message?: number }` it is outside the caller contract.
  assert.equal(runExample("invalid-in-function-key", "report(() => 0)"), true);
  assert.equal(runExample("invalid-in-function-key-call", "report(() => 0)"), true);
  assert.equal(runExample("invalid-in-function-key-member", `wrong({ size: 1, call: () => "s" })`), "s");
  // `in` throws on a primitive and on null, which tests on `unknown` may
  // leave; a function owns `name`.
  assert.throws(() => runExample("invalid-in-unknown-primitive", "probe(5)"), /Cannot use 'in' operator/);
  assert.throws(() => runExample("invalid-in-unknown-null", "probe(null)"), /Cannot use 'in' operator/);
  assert.equal(runExample("invalid-in-unknown-function-key", "probe(() => 0)"), true);
  // An open read runs a getter at its key, giving a new value at each read,
  // which the open-read restriction excludes; it finds a numeric `kind` on
  // a record that is no compiler node.
  assert.equal(JSON.stringify(runExample("invalid-open-read-getter",
    `(() => { let n = 0; const o = { get name() { n = n + 1; return n; } }; return [nameOf(o), nameOf(o)]; })()`)), "[1,2]");
  assert.equal(runExample("invalid-compiler-api-open-read-kind", "isNode({ kind: 1 })"), true);
  assert.equal(JSON.stringify(runExample("in-unknown-object", `[anything({ a: 1 }), anything(5), closable({ close() {} }),
    closable(""), named(() => { throw new Error("m"); }), named(() => { throw 5; }), kind(null), kind(() => 0),
    kind(1), kind({ code: 1 }), kind({})]`)), JSON.stringify([true, false, true, false, true, false, "nullish",
    "function", "primitive", "coded", "object"]));
  assert.equal(runExample("in-outside-caller-contract", `withIn(Object.assign(new Error("m"), { size: 1 }))`), "Error");
  assert.equal(runExample("in-outside-caller-contract", `withMessage(Object.assign(new Error(), { size: 1 }))`), "1");
  assert.equal(runExample("in-outside-caller-contract", `withoutIn(Object.assign(new Error(), { size: 1 }))`), "1");
  assert.equal(runExample("invalid-error-optional-name", "wrong()"), "Error");
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
{
  // A computed key is evaluated before the value: read before its
  // declaration, the key throws, and the value has not run.
  assert.equal(runExample("object-computed-key-order", "(() => { const log = []; const k = order(log); return JSON.stringify([log, k]); })()"),
    '[["thrown","value"],1]', "object-computed-key-order: the key throws before the value runs");
}
{
  // A program iterable spread first in its statement: its steps run before
  // the later element's code, as in place.
  assert.equal(runExample("spread-program-iterable-first",
    "(() => { const log = []; before(new Counter(log, 2)); return JSON.stringify(log); })()"),
  '["step","step","step","later"]', "spread-program-iterable-first: the iterator steps before the later element");
}
{
  // A read that throws before a spread's iterator runs: the first call logs
  // the throw alone, the iterator runs at the second.
  assert.equal(runExample("spread-program-iterable-uninitialized-refused",
    "(() => { const log = []; const n = early(log); return JSON.stringify([log, n]); })()"),
  '[["thrown","iterator"],1]', "spread-program-iterable-uninitialized-refused: the read throws before the iterator runs");
}
{
  // A global getter read as a callee runs before the iterator; a global
  // lexical binding read before its initialization throws before it.
  assert.equal(runExample("spread-program-iterable-global-getter-refused",
    "(() => { const log = []; Object.defineProperty(globalThis, \"counted\", { get() { log.push(\"getter\"); " +
    "return (...xs) => xs.length; } }); call(log); return JSON.stringify(log); })()"),
  '["getter","iterator"]', "spread-program-iterable-global-getter-refused: the getter runs before the iterator");
  assert.equal(runExample("spread-program-iterable-ambient-function-refused",
    "(() => { const log = []; Object.defineProperty(globalThis, \"counted\", { get() { log.push(\"getter\"); " +
    "return (...xs) => xs.length; } }); call(log); return JSON.stringify(log); })()"),
  '["getter","iterator"]', "spread-program-iterable-ambient-function-refused: the getter runs before the iterator");
  assert.equal(runExample("spread-program-iterable-global-tdz-refused",
    "(() => { const log = []; try { read(log); } catch { log.push(\"thrown\"); } return JSON.stringify(log); })();\nlet late = 1;"),
  '["thrown"]', "spread-program-iterable-global-tdz-refused: the read throws before the iterator runs");
}
{
  // Behaviour the host assumption on standard-library global bindings
  // excludes, and the parser cannot detect: a getter on `globalThis.Set`
  // returning the genuine `Set`. The source reads `Set` before the spread's
  // iterator; the collection hoisted before the statement runs the iterator
  // first. With a throwing iterator the source logs the getter and the
  // iterator, the hoisted order the iterator alone.
  const getter = "const real = Set; Object.defineProperty(globalThis, \"Set\", { get() { log.push(\"getter\"); return real; } });";
  const throwing = "{ [Symbol.iterator]() { return { next() { log.push(\"iterator\"); throw 0; } }; } }";
  const run = (body: string): unknown => runExample("spread-program-iterable-first",
    `(() => { const log = []; ${getter} try { ${body} } catch {} return JSON.stringify(log); })()`);
  assert.equal(run("distinct(new Counter(log, 1), []);"), '["getter","step","step"]',
    "the source reads Set before the iterator steps");
  assert.equal(run("const items = [...new Counter(log, 1)]; new Set([...items]);"), '["step","step","getter"]',
    "the hoisted collection steps the iterator before reading Set");
  assert.equal(run(`distinct(${throwing}, []);`), '["getter","iterator"]',
    "the source reads Set before a throwing iterator");
  assert.equal(run(`const items = [...${throwing}]; new Set([...items]);`), '["iterator"]',
    "the hoisted collection throws before reading Set");
}
{
  // `o.m?.(a)`: called with `o` as its receiver, the argument evaluated;
  // absent, `undefined` and the argument not evaluated.
  assert.equal(runExample("optional-method-call",
    "(() => { const log = []; const r = apply({ base: 2, equation(x) { return this.base + x; } }, 1, log); " +
    "const s = apply({ base: 0 }, 1, log); return JSON.stringify([r, s === undefined, log]); })()"),
  '[3,true,["argument"]]', "optional-method-call: the receiver bound, the arguments skipped where the method is absent");
  // `e.m?.(a)` on any object: the object's call runs once per call, the
  // method sees it as `this`, and an earlier `?.` skips the call and the
  // links after it.
  const scope = "{ base: 10, equation(x) { return this.base + x; } }";
  for (const [call, expected] of [
    [`(() => { const log = []; return JSON.stringify([apply(${scope}, 1, log), apply({ base: 0 }, 1, log), log]); })()`,
      '[11,null,["object","object"]]'],
    [`assigned({ base: 0 }, ${scope}, 2)`, 12],
    [`JSON.stringify([linked(undefined, 1), linked({}, 1), linked({ scope: ${scope} }, 1)])`, "[null,null,11]"],
    [`after({}, 1)`, undefined],
    [`after({ make(k) { return { n: k + (this.make ? 100 : 0) }; } }, 1)`, 101],
  ] as const)
    assert.equal(runExample("optional-method-call-object", call), expected, `optional-method-call-object: ${call}`);
  // Nested in an argument, each call has its own object as `this`, the
  // outer one evaluated first; in an arrow, the object's call runs at each
  // call of the arrow, and `this` in the arrow is the method's.
  const outer = "{ base: 100, equation(x) { return this.base + x; } }";
  const inner = "{ base: 10, equation(x) { return this.base + x; } }";
  for (const [call, expected] of [
    [`(() => { const log = []; return JSON.stringify([nested(${outer}, ${inner}, 1, log), log]); })()`,
      '[111,["outer","inner"]]'],
    [`(() => { const log = []; return JSON.stringify([nested(${outer}, { base: 0 }, 1, log), log]); })()`,
      '[101,["outer","inner"]]'],
    [`(() => { const log = []; return JSON.stringify([nested({ base: 0 }, ${inner}, 1, log), log]); })()`,
      '[null,["outer"]]'],
    [`(() => { const log = []; const f = later(${inner}, log); return JSON.stringify([f(1), f(2), log]); })()`,
      '[11,12,["arrow","arrow"]]'],
    [`new Box(${inner}).bound(5)()`, 15],
    [`new Box({ base: 0 }).bound(5)()`, undefined],
  ] as const)
    assert.equal(runExample("optional-method-call-nested", call), expected, `optional-method-call-nested: ${call}`);
  // The receiver is the saved object, which meets no `this: Keyed`; an
  // absent method gives `undefined`.
  assert.equal(runExample("invalid-optional-method-call-receiver", "wrong({ read() { return this.k; } })"), undefined,
    "invalid-optional-method-call-receiver: the method reads a `k` its receiver lacks");
  assert.equal(runExample("invalid-optional-method-call-absent", "wrong({}, 1)"), undefined,
    "invalid-optional-method-call-absent: an absent method gives undefined");
}

// Each invalidation changes the value observed by the second member read.
for (const [file, call] of [
  ["invalid-path-witness-getter", `wrong()`],
  ["invalid-path-witness-call", `(() => { const h = { value: { kind: "text", text: "ok" } }; return wrong(h, () => { h.value = { kind: "empty" }; }); })()`],
  ["invalid-path-witness-alias", `(() => { const h = { value: { kind: "text", text: "ok" } }; return wrong(h, h); })()`],
  ["invalid-path-witness-root", `wrong({ value: { kind: "text", text: "ok" } }, { value: { kind: "empty" } })`],
  ["invalid-path-witness-closure", `wrong({ value: { kind: "text", text: "ok" } }, { value: { kind: "empty" } })`],
]) assert.equal(runExample(file, call), undefined, file);
// Accessors lie outside the plain-data caller contract of structural records.
assert.equal(runExample("path-witness-record", `(() => { let reads = 0; return read({ get value() { return ++reads === 1 ? { kind: "text", text: "ok" } : { kind: "empty" }; } }); })()`), undefined);

// Repeated undefined reads leave the field absent, despite the required
// `kind` field in each function's result contract.
for (const [file, argument] of [
  ["invalid-guard-after-kind-optional", "{}"],
  ["invalid-guard-after-kind-index", "{}"],
  ["invalid-guard-after-kind-missing", "{ other: 1 }"],
]) {
  assert.equal(runExample(file, `"kind" in wrong(${argument})`), false,
    `${file}: the returned object lacks its required kind field`);
}
// A call that never returns normally (`no-return`): the positive's three
// callees throw where the callback reaches them, and return nothing to it.
for (const call of [`members(new Gate(), ["a", ""])`, "instances([1, -1])", `rests(["a", ""])`])
  assert.throws(() => runExample("no-return-callee-map", call), /empty|negative/, `no-return-callee-map: ${call}`);
// A promise, a Boolean and a caught throw are returns: the callee popped the
// mapped array, and `map` skipped the index it removed.
// A statement (`Within<F, T>`) a body does not meet: each popping method,
// declaration, override, look-alike, written field, static method or
// substituted dependency leaves a hole in the mapped array; a popping default
// shortens the array it reads.
for (const [file, call] of [
  ["invalid-method-effect-method", "1 in wrong(new Bump(), [1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-effect-declaration", "1 in wrong([1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-effect-override", "1 in wrong(new Drain(), [1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-effect-lookalike", "1 in wrong([1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-field-effect-write", "1 in wrong(new Holder(), [1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-effect-static", "1 in wrong([1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-effect-onthrow", "1 in wrong(new Bump(), [1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-effect-stated-throw-caught", "1 in wrong(new Bump(), [1, 2]) ? \"dense\" : undefined"],
  ["invalid-method-effect-unstated-dependency",
    "(() => { const r = new Runner(); r.helper = (ys, x) => { ys.pop(); return x; }; return 1 in wrong(r, [1, 2]) ? \"dense\" : undefined; })()"],
  ["invalid-method-effect-default", "(() => { const xs = [1]; bad(xs); return xs.length ? \"kept\" : undefined; })()"],
  ["invalid-method-effect-rest-default", "(() => { const xs = [1]; bad(xs); return xs.length ? \"kept\" : undefined; })()"],
  ["invalid-method-effect-callback-argument", "1 in wrong([1, 2]) ? \"dense\" : undefined"],
  ["invalid-compiler-api-visitor-effect",
    "1 in wrong([{ forEachChild: (v) => v() }, { forEachChild: (v) => v() }]) ? \"dense\" : undefined"],
]) assert.equal(runExample(file, call), undefined, `${file}: the statement is not met`);
for (const [file, call] of [
  ["invalid-method-effect-throw-caught", "1 in wrong(new Bump(), [1, 2]) ? \"dense\" : undefined"],
  ["invalid-no-return-guard", "1 in wrong([1, 2]) ? \"dense\" : undefined"],
]) assert.equal(runExample(file, call), undefined, `${file}: a hole in the result`);
// An async call returns its promise where its body throws: each rejection is
// handled by the process, and the pop before it leaves a hole.
for (const [file, call] of [
  ["invalid-no-return-promise", "wrong([1, 2])"],
  ["invalid-async-rejection-effect", "wrong([1, 2])"],
  ["invalid-async-rejection-default", "wrong([1, 2])"],
  ["invalid-async-rejection-module", "wrong([1, 2])"],
  ["invalid-async-throw-only", "wrong([1, 2])"],
  ["invalid-async-throw-only-arrow", "wrong([1, 2])"],
  ["invalid-async-throw-only-method", "wrong(new Runner(), [1, 2])"],
  ["invalid-async-throw-only-expression", "wrong([1, 2])"],
  ["invalid-async-throw-only-object-method", "wrong([1, 2])"],
  ["invalid-async-throw-only-static", "wrong([1, 2])"],
  ["invalid-async-throw-only-default", "wrong([1, 2])"],
]) {
  const ran = runNode(file, `process.on("unhandledRejection", () => {}); console.log(1 in ${call} ? "dense" : "hole");`);
  assert.deepEqual([ran.stdout, ran.status], ["hole", 0], `${file}: the async call returned, and the result has a hole`);
}
// A retained `fs` callback of the sync API popping an array the program
// holds: the request after the construction calls it, and the array
// shrinks, beyond the requests' `{value: any, store: grow}`; a verified
// program makes no instance (`invalid-compiler-api-retained-fs` is refused
// at the constructor's declaration).
{
  const project = new URL("../pipeline/compiler-api-project/tsconfig.json", import.meta.url).pathname;
  const sync = new URL("../tools/node_modules/typescript/dist/api/sync/api.js", import.meta.url).pathname;
  const ran = runNode("invalid-compiler-api-retained-fs",
    `const xs = [1, 2, 3]; try { wrong(xs, ${JSON.stringify(project)}); } catch {} console.log(xs.length < 3 ? "shrunk" : "kept");`,
    { "typescript/unstable/sync": sync });
  assert.deepEqual([ran.stdout, ran.status], ["shrunk", 0], "invalid-compiler-api-retained-fs: a request runs the popping callback");
  // The client serializes a callback's result: a `toJSON` it holds runs
  // during the request, though the callback itself changes nothing.
  const returned = runNode("invalid-compiler-api-callback-tojson",
    `const xs = [1, 2, 3]; try { wrong(xs, ${JSON.stringify(project)}); } catch {} console.log(xs.length < 3 ? "shrunk" : "kept");`,
    { "typescript/unstable/sync": sync });
  assert.deepEqual([returned.stdout, returned.status], ["shrunk", 0],
    "invalid-compiler-api-callback-tojson: serializing the callback's result runs its toJSON");
  // A request serializing an object of the program with `JSON.stringify`
  // runs its `toJSON`: popping the mapped array leaves a hole.
  const serialized = runNode("invalid-compiler-api-request-tojson", [
    `import { API } from ${JSON.stringify(pathToFileURL(sync).href)};`,
    `const api = new API({});`,
    `const snapshot = api.updateSnapshot({ openProject: ${JSON.stringify(project)} });`,
    `const program = snapshot.getProject(${JSON.stringify(project)}).program;`,
    `const r = wrong(program, [1, 2, 3]);`,
    `api.close();`,
    `console.log(r.length === 3 && !(2 in r) ? "hole" : "dense");`,
  ].join("\n"));
  assert.deepEqual([serialized.stdout, serialized.status], ["hole", 0],
    "invalid-compiler-api-request-tojson: the request runs the argument's toJSON");
  // The installed `forEachChild` runs a visitor popping the mapped array on
  // each child of a real source file: the result holds a hole.
  const file = new URL("../pipeline/compiler-api-project/node-names.ts", import.meta.url).pathname;
  const visited = runNode("invalid-compiler-api-visitor-effect", [
    `import { API } from ${JSON.stringify(pathToFileURL(sync).href)};`,
    `const api = new API({});`,
    `const snapshot = api.updateSnapshot({ openProject: ${JSON.stringify(project)} });`,
    `const sf = snapshot.getProject(${JSON.stringify(project)}).program.getSourceFile(${JSON.stringify(file)});`,
    `const r = wrong([sf, sf, sf]);`,
    `api.close();`,
    `console.log(r.length === 3 && !(2 in r) ? "hole" : "dense");`,
  ].join("\n"));
  assert.deepEqual([visited.stdout, visited.status], ["hole", 0],
    "invalid-compiler-api-visitor-effect: the installed forEachChild runs the popping visitor");
  // The checker's answers at nodes of a real source file: the array form
  // of `getSymbolAtLocation` gives `undefined` for a statement, and the
  // signature resolved at a binary expression has no declaration.
  const opened = [
    `import { API } from ${JSON.stringify(pathToFileURL(sync).href)};`,
    `const api = new API({});`,
    `const snapshot = api.updateSnapshot({ openProject: ${JSON.stringify(project)} });`,
    `const p = snapshot.getProject(${JSON.stringify(project)});`,
    `const sf = p.program.getSourceFile(${JSON.stringify(file)});`,
    `const statement = sf.statements[1].body.statements[0];`,
    `let binary; const find = (n) => { if (n.kind === 227) binary ??= n; n.forEachChild(find); }; find(sf);`,
  ];
  const entry = runNode("invalid-compiler-api-array-query-entry",
    [...opened, `const r = wrong(p.checker, [statement]);`, `api.close();`,
      `console.log(r === undefined ? "undefined" : "symbol");`].join("\n"));
  assert.deepEqual([entry.stdout, entry.status], ["undefined", 0],
    "invalid-compiler-api-array-query-entry: the array form gives undefined for a statement");
  const declared = runNode("invalid-compiler-api-signature-declaration",
    [...opened, `const r = wrong(p.checker, binary, null);`, `api.close();`,
      `console.log(r === undefined ? "undefined" : "handle");`].join("\n"));
  assert.deepEqual([declared.stdout, declared.status], ["undefined", 0],
    "invalid-compiler-api-signature-declaration: the binary expression's signature has no declaration");
  // The client shares one `Signature` per id, and its `declaration` is a
  // writable data field: the callback fetches the same signature again and
  // reassigns it, so the test made before the call no longer holds.
  const reassigned = runNode("invalid-compiler-api-signature-declaration-call", [...opened,
    `const signatureOf = () => p.checker.getSignaturesOfType(p.checker.getTypeAtLocation(sf.statements[1].name), 0)[0];`,
    `const s = signatureOf();`,
    `const r = wrong(s, null, () => { signatureOf().declaration = undefined; });`, `api.close();`,
    `console.log(s.declaration === undefined && r === undefined ? "undefined" : "handle");`].join("\n"));
  assert.deepEqual([reassigned.stdout, reassigned.status], ["undefined", 0],
    "invalid-compiler-api-signature-declaration-call: another alias reassigns the shared signature's declaration during the call");
}
// A type predicate's kind and a symbol's tables under Node, on a project of
// their own: `asserts x` states no type, so its predicate's `type` is
// `undefined`; a predicate about `this` has the index 0 and no name; a class
// member named `__x` is keyed `___x` in its owner's member table, so `get`
// at the display name finds nothing.
{
  const sync = new URL("../tools/node_modules/typescript/dist/api/sync/api.js", import.meta.url).pathname;
  const directory = realpathSync(mkdtempSync(join(tmpdir(), "tscert-symbol-tables-")));
  try {
    writeFileSync(join(directory, "tsconfig.json"), JSON.stringify({ compilerOptions: { strict: true }, files: ["subjects.ts"] }));
    writeFileSync(join(directory, "subjects.ts"),
      "export function asserted(x: unknown): asserts x {}\nexport class C { __x = 1; isC(): this is C { return true; } }\n");
    const config = join(directory, "tsconfig.json");
    const opened = [
      `import { API } from ${JSON.stringify(pathToFileURL(sync).href)};`,
      `const api = new API({});`,
      `const snapshot = api.updateSnapshot({ openProject: ${JSON.stringify(config)} });`,
      `const p = snapshot.getProject(${JSON.stringify(config)});`,
      `const sf = p.program.getSourceFile(${JSON.stringify(join(directory, "subjects.ts"))});`,
      `const [fn, cls] = sf.statements;`,
    ];
    const predicate = runNode("invalid-compiler-api-type-predicate-type", [...opened,
      `const signature = p.checker.getSignaturesOfType(p.checker.getTypeAtLocation(fn.name), 0)[0];`,
      `const r = wrong(p.checker, signature);`, `api.close();`,
      `console.log(r === undefined ? "undefined" : "type");`].join("\n"), { "typescript/unstable/sync": sync });
    assert.deepEqual([predicate.stdout, predicate.status], ["undefined", 0],
      "invalid-compiler-api-type-predicate-type: `asserts x` states no type");
    // The client copies the server's index of a predicate about `this`, 0,
    // so the test of the index passes it and its name is `undefined`.
    const self = runNode("invalid-compiler-api-type-predicate-this-index", [...opened,
      `const signature = p.checker.getSignaturesOfType(p.checker.getTypeAtLocation(cls.members[1].name), 0)[0];`,
      `const r = wrong(p.checker, signature);`, `api.close();`,
      `console.log(r === undefined ? "undefined" : JSON.stringify(r));`].join("\n"));
    assert.deepEqual([self.stdout, self.status], ["undefined", 0],
      "invalid-compiler-api-type-predicate-this-index: a predicate about this has index 0 and no name");
    const table = runNode("invalid-compiler-api-symbol-table-get", [...opened,
      `const owner = p.checker.getSymbolAtLocation(cls.name);`,
      `const member = p.checker.getSymbolAtLocation(cls.members[0].name);`,
      `const r = wrong(owner, member);`, `api.close();`,
      `console.log(member.name === "__x" && r === undefined ? "undefined" : "symbol");`].join("\n"));
    assert.deepEqual([table.stdout, table.status], ["undefined", 0],
      "invalid-compiler-api-symbol-table-get: the table is keyed by escaped names");
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}
