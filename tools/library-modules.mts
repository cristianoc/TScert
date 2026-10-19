/** Node's module functions, such as `node:fs`'s `writeFileSync`, as a client
 * may import and call them: through a reviewed overlay (SOURCE-CONTRACTS.md,
 * "Library modules"), as `library-globals.mts` reads the standard library's
 * globals. An entry names one overload of the function's declaration in
 * `@types/node`, with exactly the text it was reviewed against, so a changed
 * declaration is refused and reviewed again, and states the signature the
 * host meets at the arguments it admits: what the host does there, stated as
 * a type. The value is the statements' intersection; the declaration's types
 * are not read, so the types they name (`Buffer`, `URL`, streams) are not
 * collected. A function the overlay lists none of is read as its declaration
 * states (an imported value). */
import type { Stated } from "./library-globals.mts";
import type { CallEffect, TypeTerm } from "./declaration-types.mts";
import { emptyEffect } from "./type-graph.mts";

export type ModuleEntry = {
  /** The module, as `node:` names it without the prefix: `child_process`. */
  module: string;
  /** The exported function. */
  name: string;
  /** The overload, exactly as reviewed, its white space collapsed. */
  signature: string;
  stated: Stated;
  /** The effect the stated signature states, where reviewed: a call at it
   * changes at most what its footprint says; absent, it may change anything. */
  effect?: CallEffect;
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

/** The standard streams of a child: standard output piped, the others piped,
 * ignored or inherited. */
const stdio: TypeTerm = { k: "tuple", presence: "dense", readonly: true, optional: [], rest: null, span: at,
  required: [union(text("pipe"), text("ignore"), text("inherit")), text("pipe"),
    union(text("pipe"), text("ignore"), text("inherit"))] };

/** A record of strings: every string key it owns holds a string. */
const strings: TypeTerm = { k: "object", fields: [], calls: [], span: at,
  stringIndex: { readonly: true, value: union(atom("string"), atom("undefined")), span: at } };

export const modulesOverlay: readonly ModuleEntry[] = [
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
    signature: "function execFileSync(file: string, args: readonly string[], options: ExecFileSyncOptionsWithStringEncoding): string;",
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
    signature: "function execFileSync(file: string, args: readonly string[], options: ExecFileSyncOptionsWithStringEncoding): string;",
    stated: { binders: [], params: [atom("string"),
      { k: "array", presence: "readable", readonly: true, element: atom("string"), span: at },
      { k: "object", stringIndex: null, calls: [], span: at, fields: [
        field("encoding", text("utf8"), false), field("input", union(atom("string"), atom("undefined")), true),
        field("maxBuffer", union(atom("number"), atom("undefined")), true),
        field("stdio", union(stdio, atom("undefined")), true),
        field("env", union(strings, atom("undefined")), true)] }],
      result: atom("string") } },
  // `writeFileSync(file, data)` with a path and a string writes the string,
  // encoded as UTF-8, to the file, replacing it, and returns `undefined`. A
  // path it cannot open or write, or one holding a NUL character, throws.
  // It runs no code of the client's on a string.
  { module: "fs", name: "writeFileSync",
    signature: "export function writeFileSync(file: PathOrFileDescriptor, data: string | NodeJS.ArrayBufferView, options?: WriteFileOptions): void;",
    stated: { binders: [], params: [atom("string"), atom("string")], result: atom("undefined") } },
  // `readFileSync(path, "utf8")` with a string path reads the whole file and
  // returns its contents decoded as UTF-8, a string; a path it cannot open
  // or read, or one holding a NUL character, throws. It runs no code of the
  // client's on a string path and a string encoding. Stated at the encoding
  // "utf8", where the declaration's other forms return a `Buffer`.
  { module: "fs", name: "readFileSync",
    signature: "export function readFileSync(path: PathOrFileDescriptor, options: | { encoding: BufferEncoding; flag?: string | undefined; } | BufferEncoding): string;",
    stated: { binders: [], params: [atom("string"), text("utf8")], result: atom("string") } },
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
  // `node:path`'s string functions compute a path from strings. `dirname`
  // and `basename` with an optional suffix validate their strings and
  // compute from them alone (Node 25.2.1's lib/path.js): they run no code of
  // the client's, write nothing and allocate the string they return. `join`
  // calls `posix.normalize`, and `resolve`, and `relative` through it, read
  // `process.cwd()` for a relative path: writable properties other code may
  // replace, so the three are unrestricted in their effect.
  { module: "path", name: "join", signature: "join(...paths: string[]): string;",
    stated: { binders: [], params: [], rest: atom("string"), result: atom("string") } },
  { module: "path", name: "resolve", signature: "resolve(...paths: string[]): string;",
    stated: { binders: [], params: [], rest: atom("string"), result: atom("string") } },
  { module: "path", name: "dirname", signature: "dirname(path: string): string;",
    stated: { binders: [], params: [atom("string")], result: atom("string") }, effect: pathEffect },
  { module: "path", name: "basename", signature: "basename(path: string, suffix?: string): string;",
    stated: { binders: [], params: [atom("string"), union(atom("string"), atom("undefined"))], result: atom("string") },
    effect: pathEffect },
  { module: "path", name: "relative", signature: "relative(from: string, to: string): string;",
    stated: { binders: [], params: [atom("string"), atom("string")], result: atom("string") } },
];

/** A declaration's text as an entry spells it: white space collapsed, none
 * after `(` or before `)`, and no comma before `)`. */
export function reviewedText(declaration: string): string {
  return declaration.replace(/\s+/g, " ").replace(/,\s*\)/g, ")").replace(/\(\s+/g, "(").replace(/\s+\)/g, ")").trim();
}

/** The entries of an import from `specifier` of `name`: `node:fs` and `fs` name one module. */
export function moduleEntries(specifier: string, name: string): readonly ModuleEntry[] {
  const module = specifier.startsWith("node:") ? specifier.slice("node:".length) : specifier;
  return modulesOverlay.filter(e => e.module === module && e.name === name);
}
