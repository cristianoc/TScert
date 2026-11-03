/** Node's module functions, such as `node:fs`'s `writeFileSync`, as a client
 * may import and call them: through a reviewed overlay (SOURCE-CONTRACTS.md,
 * "Library modules"), as `library-globals.mts` reads the standard library's
 * globals. An entry names one overload of the function's declaration in
 * `@types/node`, with exactly the text it was reviewed against, so a changed
 * declaration is refused and reviewed again, and states the signature the
 * host meets at the arguments it admits: what the host does there, stated as
 * a type. The value is the statements' intersection; the declaration's types
 * are not read, so the types they name (`Buffer`, `URL`, streams) are not
 * collected. A value of a built-in module the overlay lists none of is
 * refused where it is imported (`declaration-graph.mts`). */
import type { Stated } from "./library-globals.mts";
import type { CallEffect, DeclarationIdentity, TypeDefinition, TypeTerm } from "./declaration-types.mts";
import { emptyEffect, ordinaryEffect } from "./type-graph.mts";
import { pathToFileHrefName } from "./intrinsics.mts";
import { bigIntStats, buffer, bytes, definitions as stated, dirent, url } from "./library-types.mts";

export type ModuleEntry = {
  /** The module, as `node:` names it without the prefix: `child_process`. */
  module: string;
  /** The exported function. */
  name: string;
  /** The overload, exactly as reviewed: its text in the declaration file. */
  signature: string;
  /** The same overload's text in another pinned `@types/node` installation,
   * where it differs, also exactly as reviewed. */
  alternatives?: string[];
  stated: Stated;
  /** The effect the stated signature states, where reviewed: a call at it
   * changes at most what its footprint says; absent, it may change anything. */
  effect?: CallEffect;
  /** For a module that exports a function merged with a namespace
   * (`export = strict`), read by its default import: the member the entry
   * reviews, absent for the call of the function itself. */
  member?: string;
  /** A promise on normal return about the actual at `param`: it holds a
   * value of `type` (`asserts actual is T`), which the host's comparison
   * establishes before it returns. */
  promise?: { param: number; type: TypeTerm };
  /** The export is a constant, not a function: its value has the type
   * `stated.result`, and `stated` has no parameters. */
  constant?: true;
  /** The call is the calculus's own test: written as a statement with no
   * message or a literal one, `assert(v, m)` is `if (!v) throw
   * %AssertionFailure%(m)`, narrowing `v` as an `if` does. */
  lowering?: "test";
  /** A read of `href` written directly on a call at this entry,
   * `f(…).href`, is a call of this intrinsic with the call's arguments. No
   * other code reaches the object the call returns before the read. */
  serialized?: string;
  /** Declarations the stated signature names that no library declares, such
   * as the `Hash` `createHash` returns: they join the document when the
   * entry is read. */
  definitions?: TypeDefinition[];
};

type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];
const at: [number, number] = [0, 0];
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span: at });
const text = (value: string): TypeTerm => ({ k: "literal", name: "string", text: value, span: at });
const union = (...parts: TypeTerm[]): TypeTerm => ({ k: "union", parts, span: at });
const no = (): TypeTerm => ({ k: "literal", name: "false", text: "false", span: at });
const yes = (): TypeTerm => ({ k: "literal", name: "true", text: "true", span: at });
/** A field of an object type term. */
type Field = Extract<TypeTerm, { k: "object" }>["fields"][number];
const field = (name: string, type: TypeTerm, optional: boolean): Field =>
  ({ name, optional, readonly: true, type, span: at });

/** A function that computes a string and allocates only it, also when it
 * throws. */
const pathEffect: CallEffect = { ...emptyEffect, onThrow: true };

/** What `createHash("sha256")` returns, a `Hash` at the members the
 * overlay states (SOURCE-CONTRACTS.md, "Library modules"),
 *
 *     type Hash = { update(data: string | Uint8Array): this; digest(encoding: "hex"): string };
 *
 * each a method of `Hash.prototype`, its receiver a `Hash`. A `Buffer` is a
 * `Uint8Array` (`library-types.mts`). */
const hashIdentity: DeclarationIdentity = { module: "tscert/crypto", name: "Hash", span: at };
const hash: TypeTerm = { k: "reference", args: [], span: at,
  reference: { name: hashIdentity.name, span: at, arguments: [], target: hashIdentity } };
const method = (params: TypeTerm[], result: TypeTerm): TypeTerm =>
  ({ k: "function", effect: ordinaryEffect, receiver: { k: "self", span: at }, params, rest: null, result, span: at });
const hashDefinition: TypeDefinition = { declaration: hashIdentity, parameters: [], bases: [],
  expression: { k: "object", stringIndex: null, calls: [], span: at, fields: [
    field("update", method([union(atom("string"), bytes)], { k: "self", span: at }), false),
    field("digest", method([text("hex")], atom("string")), false)] } };

/** `readFileSync`'s overload without an encoding, as each pinned
 * installation declares its result. */
const readBytesText = (declared: string): string =>
  `export function readFileSync(\n        path: PathOrFileDescriptor,\n        options?: {\n            encoding?: null | undefined;\n            flag?: string | undefined;\n        } | null,\n    ): ${declared};`;

/** The standard streams of a child: standard output piped, the others piped,
 * ignored or inherited. */
const stdio: TypeTerm = { k: "tuple", presence: "dense", readonly: true, optional: [], rest: null, span: at,
  required: [union(text("pipe"), text("ignore"), text("inherit")), text("pipe"),
    union(text("pipe"), text("ignore"), text("inherit"))] };

/** A record of strings: every string key it owns holds a string. */
const strings: TypeTerm = { k: "object", fields: [], calls: [], span: at,
  stringIndex: { readonly: true, value: union(atom("string"), atom("undefined")), span: at } };

/** `node:assert/strict`'s message: a string, or absent. A message that is
 * an `Error` would be thrown in place of the `AssertionError`. */
const message: TypeTerm = union(atom("string"), atom("undefined"));
/** A callback `() => unknown`, whatever it runs. */
const block: TypeTerm = { k: "function", effect: ordinaryEffect, receiver: null, params: [], rest: null,
  result: atom("unknown"), span: at };
/** `node:assert/strict`'s entries (SOURCE-CONTRACTS.md, "node:assert/strict").
 * A passing `ok`, `equal`, `notEqual` and `ifError` run no code (ToBoolean,
 * `Object.is`, a comparison with `null` and `undefined`): their footprint is
 * empty on normal return. A failure builds an `AssertionError`, which reads
 * the compared values' accessors, runs a program's `Error.prepareStackTrace`
 * and sets and restores `Error.stackTraceLimit` (Node 25.2.1): no entry
 * preserves anything across the throw (`onThrow` false). A deep comparison
 * traverses enumerable own string and symbol properties, an array's extra
 * ones included, accessors among them; `match` runs the regex's `exec`,
 * reading `lastIndex` by ToLength; `throws` calls its block and converts a
 * thrown value by `String` to test a regex: these state no effect. */
type AssertFields = Pick<ModuleEntry, "stated" | "effect" | "promise" | "lowering">;
const assertMember = (member: string | undefined, signature: string, entry: AssertFields): ModuleEntry =>
  ({ module: "assert/strict", name: "default", signature,
    ...(member === undefined ? {} : { member }), stated: entry.stated,
    ...(entry.effect === undefined ? {} : { effect: entry.effect }),
    ...(entry.promise === undefined ? {} : { promise: entry.promise }),
    ...(entry.lowering === undefined ? {} : { lowering: entry.lowering }) });
const assertEntry = (members: (string | undefined)[], signature: string, entry: AssertFields): ModuleEntry[] => {
  const entries: ModuleEntry[] = [];
  for (const member of members) entries.push(assertMember(member, signature, entry));
  return entries;
};
const asserted: AssertFields = { lowering: "test", effect: emptyEffect,
  stated: { binders: [], params: [atom("unknown"), message], result: atom("void") } };
const assertEntries: ModuleEntry[] = [
  // The call of the module's function itself, as each pinned installation
  // declares it: a function merged with a namespace, or a call signature of
  // the exported constant's type.
  ...assertEntry([undefined], "function strict(value: unknown, message?: string | Error): asserts value;", asserted),
  ...assertEntry([undefined], "(value: unknown, message?: string | Error): asserts value;", asserted),
  ...assertEntry(["ok"], "function ok(value: unknown, message?: string | Error): asserts value;", asserted),
  // `equal` is `strictEqual`: `Object.is(actual, expected)`, after which
  // `actual` is the value `expected` is, of its type. That promise, a generic
  // one, is not stated: the producer encodes no generic promise signature
  // (WORK.md), so `equal` narrows nothing.
  ...assertEntry(["equal", "strictEqual"],
    "function strictEqual<T>(actual: unknown, expected: T, message?: string | Error): asserts actual is T;",
    { effect: emptyEffect,
      stated: { binders: ["T"], params: [atom("unknown"), { k: "binder", name: "T", span: at }, message], result: atom("void") } }),
  ...assertEntry(["notEqual", "notStrictEqual"],
    "function notStrictEqual(actual: unknown, expected: unknown, message?: string | Error): void;",
    { effect: emptyEffect, stated: { binders: [], params: [atom("unknown"), atom("unknown"), message], result: atom("void") } }),
  // A deep comparison narrows nothing: the declaration's `asserts actual is
  // T` is not read.
  ...assertEntry(["deepEqual", "deepStrictEqual"],
    "function deepStrictEqual<T>(actual: unknown, expected: T, message?: string | Error): asserts actual is T;",
    { stated: { binders: [], params: [atom("unknown"), atom("unknown"), message], result: atom("void") } }),
  ...assertEntry(["notDeepEqual", "notDeepStrictEqual"],
    "function notDeepStrictEqual(actual: unknown, expected: unknown, message?: string | Error): void;",
    { stated: { binders: [], params: [atom("unknown"), atom("unknown"), message], result: atom("void") } }),
  // A non-regex `regExp` throws a TypeError, an outcome.
  ...["match", "doesNotMatch"].flatMap(member => assertEntry([member],
    `function ${member}(value: string, regExp: RegExp, message?: string | Error): void;`,
    { stated: { binders: [], params: [atom("string"), atom("unknown"), message], result: atom("void") } })),
  ...["throws", "doesNotThrow"].flatMap(member => [
    ...assertEntry([member], `function ${member}(block: () => unknown, message?: string | Error): void;`,
      { stated: { binders: [], params: [block, message], result: atom("void") } }),
    ...assertEntry([member], `function ${member}(block: () => unknown, error: AssertPredicate, message?: string | Error): void;`,
      { stated: { binders: [], params: [block, atom("unknown"), message], result: atom("void") } })]),
  // `ifError(v)` returns where `v` is `null` or `undefined`, and throws
  // otherwise.
  ...assertEntry(["ifError"], "function ifError(value: unknown): asserts value is null | undefined;",
    { effect: emptyEffect, promise: { param: 0, type: union(atom("null"), atom("undefined")) },
      stated: { binders: [], params: [atom("unknown")], result: atom("void") } }),
  ...assertEntry(["fail"], "function fail(message?: string | Error): never;",
    { stated: { binders: [], params: [message], result: atom("never") } }),
];

export const modulesOverlay: readonly ModuleEntry[] = [
  ...assertEntries,
  // Node validates the string, strips annotations and returns source text.
  // The warning and error paths may run user code: the effect is unrestricted.
  { module: "module", name: "stripTypeScriptTypes",
    signature: "function stripTypeScriptTypes(code: string, options?: StripTypeScriptTypesOptions): string;",
    stated: { binders: [], params: [atom("string")], result: atom("string") } },
  // `execFileSync`'s restricted form, read first: options naming every key the synchronous path
  // reads, each at a type the host validates without code of the client's
  // (SOURCE-CONTRACTS.md, "Library modules"). `env` is absent or undefined,
  // as the host would write `NODE_V8_COVERAGE` and `NODE_OPTIONS` into an
  // `env` it is given and convert its values; `shell` is absent or `false`,
  // as a shell with arguments runs `process.emitWarning`'s listeners; `stdio`
  // is given, three streams long, so the host pads no array and writes no
  // standard error of its own. Under Node 25.2.1 the host writes nothing it
  // did not allocate before it returns or throws: the empty footprint, on a
  // throw too.
  { module: "child_process", name: "execFileSync",
    signature: "function execFileSync(\n        file: string,\n        args: readonly string[],\n        options: ExecFileSyncOptionsWithStringEncoding,\n    ): string;",
    stated: { binders: [], params: [atom("string"),
      { k: "array", presence: "readable", readonly: true, element: atom("string"), span: at },
      { k: "object", stringIndex: null, calls: [], span: at, fields: [
        field("encoding", text("utf8"), false), field("stdio", stdio, false),
        field("input", union(atom("string"), atom("undefined")), true),
        field("maxBuffer", union(atom("number"), atom("undefined")), true),
        field("env", atom("undefined"), true), field("shell", union(no(), atom("undefined")), true),
        field("cwd", union(atom("string"), atom("undefined")), true),
        field("argv0", union(atom("string"), atom("undefined")), true),
        field("detached", union(atom("boolean"), atom("undefined")), true),
        field("uid", union(atom("number"), atom("undefined")), true),
        field("gid", union(atom("number"), atom("undefined")), true),
        field("windowsHide", union(atom("boolean"), atom("undefined")), true),
        field("windowsVerbatimArguments", union(atom("boolean"), atom("undefined")), true),
        field("timeout", union(atom("number"), atom("undefined")), true),
        field("killSignal", union(atom("string"), atom("number"), atom("undefined")), true)] }],
      result: atom("string") },
    effect: { ...emptyEffect, onThrow: true } },
  // `execFileSync(file, args, options)` runs `file` with the arguments and,
  // when the child exits with status 0, returns its standard output: decoded
  // to a string where `options.encoding` is a text encoding, `null` where
  // standard output is not piped to the parent (`stdio[1]` is "ignore" or
  // "inherit"), whatever the declaration says. A failure to run, a nonzero
  // status, a signal, a timeout and output past `maxBuffer` throw. Stated at
  // `encoding: "utf8"`, at standard output piped (or `stdio` absent, which
  // pipes every stream), at a string `input` written to standard input, a
  // number `maxBuffer`, and an `env` absent or a record of strings. The host
  // copies the options' own properties, then converts each value `env` owns
  // to a string before it reads the `stdio` array the copy shares: an
  // object value's `toString` would run code of the client's that may
  // change `stdio` to ignore standard output, and the result is then `null`
  // (`invalid-node-exec-env-object`). Every other option the host reads it
  // validates without converting, throwing on a type it does not accept: an
  // object at each key it reads, the declared options and `argv0`,
  // `detached` and `windowsVerbatimArguments`, ran no code of the client's
  // under Node 25.2.1, and `env` alone did. A record type states nothing of
  // the keys it does not name, so `env` is stated.
  { module: "child_process", name: "execFileSync",
    signature: "function execFileSync(\n        file: string,\n        args: readonly string[],\n        options: ExecFileSyncOptionsWithStringEncoding,\n    ): string;",
    stated: { binders: [], params: [atom("string"),
      { k: "array", presence: "readable", readonly: true, element: atom("string"), span: at },
      { k: "object", stringIndex: null, calls: [], span: at, fields: [
        field("encoding", text("utf8"), false), field("input", union(atom("string"), atom("undefined")), true),
        field("maxBuffer", union(atom("number"), atom("undefined")), true),
        field("stdio", union(stdio, atom("undefined")), true),
        field("env", union(strings, atom("undefined")), true)] }],
      result: atom("string") } },
  // `spawnSync(command, args, options)` runs the command and waits for it.
  // Stated at options naming `encoding: "utf8"` and `stdio` and `env` absent
  // (Node 25.2.1): both streams are piped, so `stdout` and `stderr` are its
  // decoded output, a string, where the child ran, and absent where it could
  // not be spawned (`error` then set, `status` null); a timeout kills it
  // (`signal` set, `status` null). The host reads the options' other
  // properties, which an object of another type may hold as accessors, and
  // runs no other code of the client's: no effect is stated. The result is a
  // fresh record of what it ran, `error` an `Error` or absent.
  { module: "child_process", name: "spawnSync",
    signature: "function spawnSync(\n        command: string,\n        args: readonly string[],\n        options: SpawnSyncOptionsWithStringEncoding,\n    ): SpawnSyncReturns<string>;",
    stated: { binders: [], params: [atom("string"),
      { k: "array", presence: "readable", readonly: true, element: atom("string"), span: at },
      { k: "object", stringIndex: null, calls: [], span: at, fields: [
        field("encoding", text("utf8"), false), field("stdio", atom("undefined"), true),
        field("env", atom("undefined"), true),
        field("timeout", union(atom("number"), atom("undefined")), true),
        field("cwd", union(atom("string"), atom("undefined")), true),
        field("maxBuffer", union(atom("number"), atom("undefined")), true),
        field("input", union(atom("string"), atom("undefined")), true)] }],
      result: { k: "object", stringIndex: null, calls: [], span: at, fields: [
        field("pid", atom("number"), false),
        field("status", union(atom("number"), atom("null")), false),
        field("signal", union(atom("string"), atom("null")), false),
        field("stdout", union(atom("string"), atom("undefined")), false),
        field("stderr", union(atom("string"), atom("undefined")), false),
        field("error", atom("unknown"), true)] } } },
  // `readdirSync(path, options)` with a string path reads, of the options,
  // `encoding` and `signal` (`getOptions`), then `recursive`, `encoding` and
  // `withFileTypes` again (Node 25.2.1's `lib/fs.js`). The four are stated:
  // `withFileTypes: true`, `encoding` "utf8" or absent (`"buffer"` names the
  // entries by Buffers), `recursive` false or absent and `signal` absent, so
  // under the caller contract each is a data property every read of which
  // agrees. `recursive: true` walks the subdirectories (`readdirSyncRecursive`,
  // `handleDirents`): it calls each entry's `isDirectory` through its
  // prototype and `path.join`, both other code may replace, and the
  // `internalModuleStat` of the joined path to choose what to read next,
  // and collects entries of every depth; that walk is not audited. The
  // result is a fresh array of entries: a `Dirent`, or, where the directory
  // reports an unknown type, a `DirentFromStats` built from `fs.lstatSync`
  // of the joined path, both writable properties other code may replace.
  // Each constructor assigns `name` and `parentPath`, which become own
  // writable strings under the host assumption that entries keep their
  // audited prototype chains, `DirentFromStats.prototype` →
  // `Dirent.prototype` → `Object.prototype`, whose two Node prototypes hold
  // data properties only, the seven `is…` tests among them callable
  // throughout execution, also in external code (SOURCE-CONTRACTS.md,
  // "Library modules"). An entry's `is…` tests
  // dispatch through prototypes other code may change (`Stats`'s call
  // `this._checkModeProperty`): each is stated at `() => unknown`, its
  // effect unrestricted. The declared `path` is absent (`"path" in entry` is
  // false), so the element states none and a value read at the declared
  // `Dirent` is refused. A path it cannot read throws. The call states no
  // effect.
  { module: "fs", name: "readdirSync",
    signature: "export function readdirSync(\n        path: PathLike,\n        options: ObjectEncodingOptions & {\n            withFileTypes: true;\n            recursive?: boolean | undefined;\n        },\n    ): Dirent[];",
    stated: { binders: [], params: [atom("string"),
      { k: "object", stringIndex: null, calls: [], span: at, fields: [field("withFileTypes", yes(), false),
        field("encoding", union(text("utf8"), atom("undefined")), true),
        field("recursive", union(no(), atom("undefined")), true),
        field("signal", atom("undefined"), true)] }],
      result: { k: "array", presence: "readable", readonly: false, span: at, element: dirent } },
    definitions: [stated.dirent] },
  // `readdirSync(path)` with a string path and no options reads the
  // default options' `recursive`, `encoding` and `withFileTypes`, a frozen
  // object of no property (Node 25.2.1's `lib/fs.js`), and returns a fresh
  // array of the entries' names, strings decoded as UTF-8; a path it cannot
  // read throws. It runs no code of the client's on a string path. The call
  // states no effect.
  { module: "fs", name: "readdirSync",
    signature: "export function readdirSync(\n        path: PathLike,\n        options?:\n            | {\n                encoding: BufferEncoding | null;\n                withFileTypes?: false | undefined;\n                recursive?: boolean | undefined;\n            }\n            | BufferEncoding\n            | null,\n    ): string[];",
    stated: { binders: [], params: [atom("string")],
      result: { k: "array", presence: "readable", readonly: false, element: atom("string"), span: at } } },
  // `statSync(path)` with a string path and no options stats what the path
  // names, its symbolic links followed, and returns a fresh `Stats`; a path
  // that names nothing, or one it cannot stat, throws (`throwIfNoEntry`
  // defaults to true). It validates the string and runs no code of the
  // client's (Node 25.2.1's `lib/fs.js`). The declaration is a constant of
  // the interface `StatSyncFn`, whose first call signature the entry names.
  // `StatsBase` and `Stats` assign the fourteen numbers, which become own
  // writable data properties under the host assumption that a `Stats`
  // keeps its audited prototype chain, `Stats.prototype` →
  // `StatsBase.prototype` → `Object.prototype`, whose two Node prototypes
  // hold the seven `is…` tests, `_checkModeProperty` and the date getters
  // (`atime`, `mtime`, `ctime`, `birthtime`), none named by the stated
  // fields, the tests data properties holding callable values throughout
  // execution, also in external code
  // (SOURCE-CONTRACTS.md, "Library modules"). A test calls
  // `this._checkModeProperty`, a writable property of `Stats.prototype`
  // other code may replace: each is stated at `() => unknown`, its effect
  // unrestricted, as a `Dirent`'s. The date getters are not stated. The
  // call states no effect.
  { module: "fs", name: "statSync", signature: "(path: PathLike, options?: undefined): Stats;",
    stated: { binders: [], params: [atom("string")], result: { k: "object", stringIndex: null, calls: [], span: at,
      fields: [...["dev", "mode", "nlink", "uid", "gid", "rdev", "blksize", "ino", "size", "blocks", "atimeMs",
        "mtimeMs", "ctimeMs", "birthtimeMs"].map(name => ({ ...field(name, atom("number"), false), readonly: false })),
      ...["isFile", "isDirectory", "isBlockDevice", "isCharacterDevice", "isSymbolicLink", "isFIFO", "isSocket"]
        .map(name => field(name, { k: "function", effect: ordinaryEffect, receiver: { k: "self", span: at },
          params: [], rest: null, result: atom("unknown"), span: at }, false))] } } },
  // `statSync(path, options)` with a string path and options naming
  // `bigint: true` reads, of the options, `bigint` and `throwIfNoEntry`
  // (Node 25.2.1's `lib/fs.js`), both stated: at `throwIfNoEntry` absent,
  // `undefined` or `true` a path that names nothing throws, as without
  // options. It returns a fresh `BigIntStats` (`library-types.mts`), whose
  // numbers are bigints. It runs no code of the client's at the stated
  // options. The call states no effect.
  { module: "fs", name: "statSync",
    signature: "(\n            path: PathLike,\n            options: StatSyncOptions & {\n                bigint: true;\n            },\n        ): BigIntStats;",
    stated: { binders: [], params: [atom("string"), { k: "object", stringIndex: null, calls: [], span: at,
      fields: [field("bigint", yes(), false), field("throwIfNoEntry", union(yes(), atom("undefined")), true)] }],
      result: bigIntStats }, definitions: [stated.bigIntStats] },
  // `writeFileSync(file, data)` with a path and a string writes the string,
  // encoded as UTF-8, to the file, replacing it, and returns `undefined`. A
  // path it cannot open or write, or one holding a NUL character, throws.
  // It runs no code of the client's on a string.
  { module: "fs", name: "writeFileSync",
    signature: "export function writeFileSync(\n        file: PathOrFileDescriptor,\n        data: string | NodeJS.ArrayBufferView,\n        options?: WriteFileOptions,\n    ): void;",
    stated: { binders: [], params: [atom("string"), atom("string")], result: atom("undefined") } },
  // `writeFileSync(file, data, options)` with a path, a string and options
  // naming `mode` reads, of the options, `encoding` and `signal`
  // (`getOptions`), then `flush`, `flag`, `encoding` and `mode` (Node
  // 25.2.1's `lib/fs.js`); the six are stated, so under the caller contract
  // each is a data property whose reads agree. It writes the string,
  // encoded as UTF-8, to the file opened with `flag` "w" and the mode, and
  // returns `undefined`; a mode that is no 32-bit unsigned integer, a path
  // it cannot open or write, or one holding a NUL character, throws. Without
  // `encoding: "utf8"` the host takes its general path, which calls
  // `fs.openSync`, `fs.writeSync` and `fs.closeSync` through the module's
  // object, writable properties other code may replace: the call states no
  // effect.
  { module: "fs", name: "writeFileSync",
    signature: "export function writeFileSync(\n        file: PathOrFileDescriptor,\n        data: string | NodeJS.ArrayBufferView,\n        options?: WriteFileOptions,\n    ): void;",
    stated: { binders: [], params: [atom("string"), atom("string"), { k: "object", stringIndex: null, calls: [], span: at,
      fields: [field("mode", atom("number"), false), field("encoding", union(text("utf8"), atom("undefined")), true),
        field("signal", atom("undefined"), true), field("flush", union(atom("boolean"), atom("undefined")), true),
        field("flag", union(text("w"), atom("undefined")), true)] }], result: atom("undefined") } },
  // `mkdirSync(path, options)` with a string path and options naming
  // `recursive: true` reads `recursive` and `mode` (Node 25.2.1's
  // `lib/fs.js`), both stated: it creates the directory and those above it
  // that are missing, and returns the first it created, a string, or
  // `undefined` where the directory exists; a mode that is no 32-bit
  // unsigned integer, or a path it cannot create, throws. It runs no code of
  // the client's at the stated options. The call states no effect.
  { module: "fs", name: "mkdirSync",
    signature: "export function mkdirSync(\n        path: PathLike,\n        options: MakeDirectoryOptions & {\n            recursive: true;\n        },\n    ): string | undefined;",
    stated: { binders: [], params: [atom("string"), { k: "object", stringIndex: null, calls: [], span: at,
      fields: [field("recursive", yes(), false), field("mode", union(atom("number"), atom("undefined")), true)] }],
      result: union(atom("string"), atom("undefined")) } },
  // `chmodSync(path, mode)` with a string path and a number sets the mode
  // of what the path names, its symbolic links followed, and returns
  // `undefined`; a mode that is no 32-bit unsigned integer, or a path it
  // cannot change, throws. It runs no code of the client's (Node 25.2.1's
  // `lib/fs.js`). The call states no effect.
  { module: "fs", name: "chmodSync", signature: "export function chmodSync(path: PathLike, mode: Mode): void;",
    stated: { binders: [], params: [atom("string"), atom("number")], result: atom("undefined") } },
  // `readFileSync(path, "utf8")` with a string path reads the whole file and
  // returns its contents decoded as UTF-8, a string; a path it cannot open
  // or read, or one holding a NUL character, throws. It runs no code of the
  // client's on a string path and a string encoding. Stated at the encoding
  // "utf8", where the declaration's other forms return a `Buffer`.
  { module: "fs", name: "readFileSync",
    signature: "export function readFileSync(\n        path: PathOrFileDescriptor,\n        options:\n            | {\n                encoding: BufferEncoding;\n                flag?: string | undefined;\n            }\n            | BufferEncoding,\n    ): string;",
    stated: { binders: [], params: [atom("string"), text("utf8")], result: atom("string") } },
  // `readFileSync(path)` with a string path and no options opens the file,
  // reads it whole into a fresh `Buffer` (`library-types.mts`) and closes
  // it; a path it cannot open or read throws. It opens, reads and closes
  // through `fs.openSync`, `fs.readSync` and `fs.closeSync`, writable
  // properties of the module's object other code may replace, and allocates
  // through `Buffer.allocUnsafe`, `Buffer.concat` and `Buffer.prototype.slice`
  // (Node 25.2.1's `lib/fs.js`): the call states no effect, and its result
  // is a `Buffer` under the host assumption that `Buffer`'s and
  // `Buffer.prototype`'s functions are Node's own (SOURCE-CONTRACTS.md,
  // "Stated library types"). The two texts are the two pinned `@types/node`
  // installations'.
  { module: "fs", name: "readFileSync", signature: readBytesText("NonSharedBuffer"), alternatives: [readBytesText("Buffer")],
    stated: { binders: [], params: [atom("string")], result: buffer }, definitions: [stated.buffer] },
  // `existsSync(path)` with a string tests whether the path exists on the
  // file system and returns a Boolean; it does not throw. It runs no code of
  // the client's on a string.
  { module: "fs", name: "existsSync", signature: "export function existsSync(path: PathLike): boolean;",
    stated: { binders: [], params: [atom("string")], result: atom("boolean") } },
  // `mkdtempSync(prefix)` with a string creates a directory named by the
  // prefix and six random characters and returns its path, a string; a
  // prefix it cannot create a directory at throws. Stated at one argument,
  // where an encoding option may select a `Buffer`.
  { module: "fs", name: "mkdtempSync",
    signature: "export function mkdtempSync(prefix: string, options?: EncodingOption): string;",
    stated: { binders: [], params: [atom("string")], result: atom("string") } },
  // `rmSync(path, { recursive: true, force: true })` with a string path
  // removes the path and everything under it, a path that does not exist
  // included, and returns `undefined`; one it cannot remove throws. The host
  // reads and validates the options' properties, which an object of another
  // type may hold as accessors: the call is unrestricted in its effect.
  { module: "fs", name: "rmSync", signature: "export function rmSync(path: PathLike, options?: RmOptions): void;",
    stated: { binders: [], params: [atom("string"), { k: "object", stringIndex: null, calls: [], span: at, fields: [
      field("recursive", yes(), false), field("force", yes(), false)] }], result: atom("undefined") } },
  // `realpathSync(path)` with a string resolves it on the file system, its
  // symbolic links followed, and returns the canonical path as a string; a
  // path that does not exist throws. A relative path is resolved against
  // `process.cwd()`, a writable property of the global `process`, which
  // other code may replace: the call is unrestricted in its effect.
  { module: "fs", name: "realpathSync",
    signature: "export function realpathSync(path: PathLike, options?: EncodingOption): string;",
    stated: { binders: [], params: [atom("string")], result: atom("string") } },
  // `createHash("sha256")` constructs a `Hash` (Node 25.2.1's
  // lib/internal/crypto/hash.js): it validates the algorithm, a string,
  // builds the native handle and the state record, both fresh, and, at a
  // SHAKE algorithm without an output length alone, emits a deprecation
  // warning, which reads `process.noDeprecation` during the call, a property
  // other code may replace by a getter; an unsupported algorithm throws.
  // Stated at "sha256". `LazyTransform` assigns the hash's `_options`, which
  // a setter `Hash.prototype` inherits from other code would intercept: the
  // call states no effect. The result's `update` and `digest` are own data
  // properties of `Hash.prototype`, a host assumption as `Dirent`'s tests
  // are (SOURCE-CONTRACTS.md, "Library modules"). `update(data)` with a
  // string validates it and hashes it as UTF-8, with a view of bytes (a
  // `Uint8Array`, a `Buffer`) hashes its bytes, and returns the receiver; a
  // value meeting the view's type that is no view throws;
  // `digest("hex")` converts the encoding by a template, a string's own
  // value, marks the hash finalized and returns the digest as hexadecimal
  // digits, a string. Either throws on a hash already digested. Each reads
  // the hash's state through a symbol-keyed property, on which other code
  // may install a getter, and writes host state: both state no effect.
  { module: "crypto", name: "createHash",
    signature: "function createHash(algorithm: string, options?: HashOptions): Hash;",
    stated: { binders: [], params: [text("sha256")], result: hash }, definitions: [hashDefinition, stated.bytes] },
  // String-only `join` invokes the standard platform normalize function,
  // allocates private arrays and strings, and runs no client callback under
  // the untampered-standard-object contract (SOURCE-CONTRACTS.md, Library modules).
  // `resolve` and `relative` keep their unrestricted contracts.
  { module: "path", name: "join", signature: "join(...paths: string[]): string;",
    stated: { binders: [], params: [], rest: atom("string"), result: atom("string") }, effect: emptyEffect },
  { module: "path", name: "resolve", signature: "resolve(...paths: string[]): string;",
    stated: { binders: [], params: [], rest: atom("string"), result: atom("string") } },
  { module: "path", name: "dirname", signature: "dirname(path: string): string;",
    stated: { binders: [], params: [atom("string")], result: atom("string") }, effect: pathEffect },
  { module: "path", name: "basename", signature: "basename(path: string, suffix?: string): string;",
    stated: { binders: [], params: [atom("string"), union(atom("string"), atom("undefined"))], result: atom("string") },
    effect: pathEffect },
  { module: "path", name: "relative", signature: "relative(from: string, to: string): string;",
    stated: { binders: [], params: [atom("string"), atom("string")], result: atom("string") } },
  // `node:os`'s `tmpdir()` returns the directory for temporary files: on
  // POSIX the native `getTempDir`, the first of `TMPDIR`, `TMP` and `TEMP`
  // set, stripped of a trailing separator, or `"/tmp"`; on Windows
  // `process.env`'s `TEMP` or `TMP`, or `SystemRoot` or `windir` joined to
  // `\temp` (Node 25.2.1's lib/os.js). The result is a string under the
  // approved assumption that standard objects are not tampered with:
  // `process.env` is Node's, whose values are strings; a replaced
  // `process.env` holding `TEMP: 7` makes Windows return 7. It states no
  // effect, since the call reads `process.env`.
  { module: "os", name: "tmpdir", signature: "function tmpdir(): string;",
    stated: { binders: [], params: [], result: atom("string") } },
  // `availableParallelism()` is the native `getAvailableParallelism`
  // (Node 25.2.1's lib/os.js and src/node_os.cc): libuv's
  // `uv_available_parallelism`, an unsigned integer, returned as a number.
  // It reads no property, runs no code of the client's, allocates nothing
  // and does not throw: the empty footprint.
  { module: "os", name: "availableParallelism", signature: "function availableParallelism(): number;",
    stated: { binders: [], params: [], result: atom("number") }, effect: emptyEffect },
  // `userInfo()` with no options (Node 25.2.1's lib/os.js and
  // src/node_os.cc) calls the native `getUserInfo` with `null` options, so
  // no property is read, and encodes libuv's password entry as UTF-8: a
  // fresh object of null prototype whose own data properties, writable, are
  // `uid` and `gid`, numbers, `username` and `homedir`, strings, and `shell`,
  // a string or `null`. A failure of `uv_os_get_passwd` throws a
  // `SystemError`, whose construction runs Node's error code: the call
  // states no effect. Stated at no argument, where an encoding option may
  // select `Buffer`s.
  { module: "os", name: "userInfo",
    signature: "function userInfo(options?: UserInfoOptionsWithStringEncoding): UserInfo<string>;",
    alternatives: ["function userInfo(options?: { encoding: BufferEncoding }): UserInfo<string>;"],
    stated: { binders: [], params: [], result: { k: "object", stringIndex: null, calls: [], span: at, fields: [
      { ...field("username", atom("string"), false), readonly: false },
      { ...field("uid", atom("number"), false), readonly: false },
      { ...field("gid", atom("number"), false), readonly: false },
      { ...field("shell", union(atom("string"), atom("null")), false), readonly: false },
      { ...field("homedir", atom("string"), false), readonly: false }] } } },
  // `isBuiltin(id)` with a string (Node 25.2.1's lib/internal/bootstrap/realm.js)
  // tests the id in the set of built-ins requirable without a scheme, and,
  // for an id starting `node:`, the rest in the set of those requirable by
  // users: `SafeSet`s and primordial string functions, which run no code of
  // the client's, write and allocate nothing and do not throw. The sets are
  // filled while Node starts (`--expose-internals` adds to them): the
  // answer is the running Node's, a Boolean.
  { module: "module", name: "isBuiltin", signature: "function isBuiltin(moduleName: string): boolean;",
    stated: { binders: [], params: [atom("string")], result: atom("boolean") }, effect: emptyEffect },
  // Only strings enter fileURLToPath. The URL it parses reaches no other code: it has no own
  // auth/path/hostname/pathname hooks or externally aliased search params.
  // POSIX rejects hosts and encoded slashes; Windows accepts UNC hosts and
  // also rejects encoded backslashes. The default selects the platform.
  { module: "url", name: "fileURLToPath",
    signature: "function fileURLToPath(url: string | URL, options?: FileUrlToPathOptions): string;",
    stated: { binders: [], params: [atom("string")], result: atom("string") }, effect: emptyEffect },
  // `pathToFileURL(path)` (Node 25.2.1's `lib/internal/url.js`) validates
  // the string, resolves it by platform-specific posix/win32.resolve, which reads
  // `process.cwd()` for a relative path, a writable property other code may
  // replace, keeps a trailing `/`, and returns a fresh URL of the `file:`
  // protocol whose path is the resolved one, its URL control characters
  // encoded. Stated at one argument: `options.windows` selects Windows
  // paths. The call states no effect. `pathToFileURL(path).href` reads the
  // fresh URL's serialization: the URL reaches no other code before the
  // read, so `URL.prototype`'s `href` getter serializes its parsed record.
  { module: "url", name: "pathToFileURL", serialized: pathToFileHrefName,
    signature: "function pathToFileURL(path: string, options?: PathToFileUrlOptions): URL;",
    stated: { binders: [], params: [atom("string")], result: url }, definitions: [stated.url] },
  // `node:path`'s `sep`, the separator of the platform's paths: a data
  // property of the object the module exports, set when Node loads it (`"/"`
  // on POSIX, `"\\"` on Windows; Node 25.2.1's lib/path.js). It is writable:
  // no code writes it, an assumption, as of `process.argv`.
  { module: "path", name: "sep", signature: 'readonly sep: "\\\\" | "/";', constant: true,
    stated: { binders: [], params: [], result: union(text("\\"), text("/")) } },
];

/** The texts an entry reviews its overload as: its signature and its
 * alternatives. */
export function reviewedTexts(entry: ModuleEntry): readonly string[] {
  return [entry.signature, ...entry.alternatives ?? []];
}

/** A declaration's text as messages print it: white space collapsed. */
export function reviewedText(declaration: string): string {
  return declaration.replace(/\s+/g, " ").trim();
}

/** The module `specifier` names: `node:fs` and `fs` name one module. */
const moduleOf = (specifier: string): string =>
  specifier.startsWith("node:") ? specifier.slice("node:".length) : specifier;

/** The entries of an import from `specifier` of `name`: `node:fs` and `fs` name one module. */
export function moduleEntries(specifier: string, name: string): readonly ModuleEntry[] {
  const module = moduleOf(specifier);
  return modulesOverlay.filter(e => e.module === module && e.name === name);
}

/** Whether the default import of `specifier` is the module's object, read
 * through its members as a namespace import is (`namespace-members.mts`):
 * a Node module the overlay lists, whose `default` it reviews no entry of.
 * Node's default export of a built-in module is its `module.exports`, the
 * object whose own properties the named exports are bound from when Node
 * loads the module (Node 25.2.1, `lib/internal/bootstrap/realm.js`,
 * `BuiltinModule.prototype.syncExports`); with that object's members not
 * replaced (the approved assumption that standard objects are not tampered
 * with), its member `x` holds the named export `x`. */
export function moduleObjectDefault(specifier: string): boolean {
  const module = moduleOf(specifier);
  return modulesOverlay.some(e => e.module === module) &&
    !modulesOverlay.some(e => e.module === module && e.name === "default");
}
