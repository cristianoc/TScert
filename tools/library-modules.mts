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
import type { TypeTerm } from "./declaration-types.mts";

export type ModuleEntry = {
  /** The module, as `node:` names it without the prefix: `child_process`. */
  module: string;
  /** The exported function. */
  name: string;
  /** The overload, exactly as reviewed, its white space collapsed. */
  signature: string;
  stated: Stated;
};

type AtomName = Extract<TypeTerm, { k: "atom" }>["name"];
const at: [number, number] = [0, 0];
const atom = (name: AtomName): TypeTerm => ({ k: "atom", name, span: at });
const text = (value: string): TypeTerm => ({ k: "literal", name: "string", text: value, span: at });
const union = (...parts: TypeTerm[]): TypeTerm => ({ k: "union", parts, span: at });
const field = (name: string, type: TypeTerm, optional: boolean) =>
  ({ name, optional, readonly: true, type, span: at });

/** The standard streams of a child: standard output piped, the others piped,
 * ignored or inherited. */
const stdio: TypeTerm = { k: "tuple", presence: "dense", readonly: true, optional: [], rest: null, span: at,
  required: [union(text("pipe"), text("ignore"), text("inherit")), text("pipe"),
    union(text("pipe"), text("ignore"), text("inherit"))] };

export const modulesOverlay: readonly ModuleEntry[] = [
  // `execFileSync(file, args, options)` runs `file` with the arguments and,
  // when the child exits with status 0, returns its standard output: decoded
  // to a string where `options.encoding` is a text encoding, `null` where
  // standard output is not piped to the parent (`stdio[1]` is "ignore" or
  // "inherit"), whatever the declaration says. A failure to run, a nonzero
  // status, a signal, a timeout and output past `maxBuffer` throw. Stated at
  // `encoding: "utf8"`, at standard output piped (or `stdio` absent, which
  // pipes every stream), at a string `input` written to standard input and a
  // number `maxBuffer`. The host validates the other options it reads and
  // throws on a type it does not accept; it reads `options.encoding` and
  // `options.stdio` before it converts the values of `options.env` to
  // strings, the one place it runs code of the client's (an object value's
  // `toString`).
  { module: "child_process", name: "execFileSync",
    signature: "function execFileSync(file: string, args: readonly string[], options: ExecFileSyncOptionsWithStringEncoding): string;",
    stated: { binders: [], params: [atom("string"),
      { k: "array", presence: "readable", readonly: true, element: atom("string"), span: at },
      { k: "object", stringIndex: null, calls: [], span: at, fields: [
        field("encoding", text("utf8"), false), field("input", union(atom("string"), atom("undefined")), true),
        field("maxBuffer", union(atom("number"), atom("undefined")), true),
        field("stdio", union(stdio, atom("undefined")), true)] }],
      result: atom("string") } },
  // `writeFileSync(file, data)` with a path and a string writes the string,
  // encoded as UTF-8, to the file, replacing it, and returns `undefined`. A
  // path it cannot open or write, or one holding a NUL character, throws.
  // It runs no code of the client's on a string.
  { module: "fs", name: "writeFileSync",
    signature: "export function writeFileSync(file: PathOrFileDescriptor, data: string | NodeJS.ArrayBufferView, options?: WriteFileOptions): void;",
    stated: { binders: [], params: [atom("string"), atom("string")], result: atom("undefined") } },
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
