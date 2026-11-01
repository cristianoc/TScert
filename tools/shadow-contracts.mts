/**
 * The external declarations a program is checked against in place of their
 * `any`: each declaration file outside the program's own sources (the
 * standard library, Node's types, the compiler API's) read with every `any`
 * replaced. TypeScript then checks the program over these declarations
 * itself — inference, contextual typing, overloads, variance and
 * assignability — and each error it reports is a place the program relies
 * on an `any` of a declaration.
 *
 * - Every `any` a value may have is `TScertAny`, one opaque type: no value of
 *   the program is assignable to it, and it is assignable only to `unknown`,
 *   `{}` and `object`, which permit no use. TypeScript's own variance decides
 *   what that means at each position: a result or a property read is a value
 *   the program cannot use without narrowing; a parameter, a writable
 *   property, an index signature or a generic argument fed back as an input
 *   accepts no value of the program. Aliases, heritage, defaults and
 *   conditional types carry it as written.
 * - A type parameter's default `any`: a signature's is deleted, its
 *   constraint kept, so the call infers the parameter; a type's is `unknown`,
 *   the value with no guarantee a reference leaving the argument out stands
 *   for (`Iterator<T>`'s `TReturn` and `TNext`).
 * - An `any` in a type-level wildcard — a type parameter's constraint or a
 *   conditional type's `extends` clause — is replaced by the top type there:
 *   `unknown` at a positive position, `never` at a parameter of it; and
 *   `keyof any` is `string | number | symbol`. These constrain types; no
 *   value has them.
 * - A member the reviewed overlay of library globals states
 *   (library-globals.mts), of a standard library file, is read at the
 *   overlay's own contract: its `stated` signature where it has one, and
 *   otherwise its declaration with `any` read as `unknown`, as the front end
 *   reads a declaration's `any` (type-term.mts). The overlays of array and
 *   interface members state no `any` but a dropped `thisArg`, which stays
 *   `TScertAny`: calls omit it.
 * - A member a review below states is read at that contract.
 * - A property of the compiler API's declarations declared `any` reads as
 *   an optional `unknown` (reading rule 2 of COMPILER-API.md), as the front
 *   end reads it.
 *
 * A stated contract the printer below cannot write as TypeScript leaves the
 * member at `TScertAny`: refused at a use.
 */
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";
import { globalsOverlay, type GlobalEntry, type Stated } from "./library-globals.mts";
import type { TypeDefinition, TypeTerm } from "./declaration-types.mts";
import { readsAsOptionalUnknown } from "./compiler-api.mts";
import { childOf, childrenOf } from "./syntax.mts";
import { nativeCollectionView } from "./array-prototype.mts";

/** The opaque type every value-level `any` of a declaration is read as. */
export const OPAQUE = "TScertAny";

/** A contract reviewed for the any check: the declaration file's name, the
 * member as written (whitespace collapsed), the member read instead or,
 * without one, the member with its `any` read as `unknown`, and why that
 * holds of the host. */
interface Reviewed {
  file: string;
  text: string;
  contract?: string;
  why: string;
}

const coercion = "converts any value: ToString or ToNumber of an object runs its own conversion, an effect " +
  "outside this check (TScert admits primitives only), and may throw";
const sending = "process.send serializes any value, throwing or failing on one it cannot";

export const reviewed: readonly Reviewed[] = [
  { file: "lib.es2015.collection.d.ts", text: "new (): Map<any, any>;", contract: "new <K, V>(): Map<K, V>;",
    why: "an empty map holds no entry: it is a map at every key and value type, inferred from where it flows" },
  { file: "lib.es2015.iterable.d.ts", text: "new (): Map<any, any>;", contract: "new <K, V>(): Map<K, V>;",
    why: "an empty map holds no entry: it is a map at every key and value type, inferred from where it flows" },
  { file: "lib.es5.d.ts", text: "stringify(value: any, replacer?: (this: any, key: string, value: any) => any, space?: string | number): string;",
    contract: "stringify(value: object, replacer?: null, space?: string | number): string; " +
      "stringify(value: null | boolean | number | string, replacer?: null, space?: string | number): string; " +
      "stringify(value: unknown, replacer?: ((this: unknown, key: string, value: unknown) => unknown) | null, space?: string | number): string | undefined;",
    why: "JSON.stringify returns undefined for undefined, a symbol or a function, and where a replacer or a toJSON " +
      "returns undefined: a string only of a value that is none of these at the top and without a replacer; " +
      "a function or an object whose toJSON returns undefined is an object here, and still gives undefined" },
  { file: "lib.es5.d.ts", text: "stringify(value: any, replacer?: (number | string)[] | null, space?: string | number): string;",
    contract: "stringify(value: object, replacer?: (number | string)[] | null, space?: string | number): string; " +
      "stringify(value: null | boolean | number | string, replacer?: (number | string)[] | null, space?: string | number): string;",
    why: "as above: a list of keys selects members and returns no undefined of a value that is not undefined, a symbol or a function" },
  { file: "lib.es5.d.ts", text: "(value?: any): string;", why: `String(v) ${coercion}` },
  { file: "lib.es2020.promise.d.ts", text: "reason: any;",
    why: "a promise is rejected with any value: the reason of a settled result is any value, read and written" },
  ...[["lib.es5.d.ts", "forEach(callbackfn: (value: T, index: number, array: readonly T[]) => void, thisArg?: any): void;"],
    ["lib.es5.d.ts", "map<U>(callbackfn: (value: T, index: number, array: readonly T[]) => U, thisArg?: any): U[];"],
    ["lib.es5.d.ts", "every(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;"],
    ["lib.es5.d.ts", "some(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): boolean;"],
    ["lib.es5.d.ts", "filter(predicate: (value: T, index: number, array: readonly T[]) => unknown, thisArg?: any): T[];"],
    ["lib.es2015.core.d.ts", "find(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): T | undefined;"],
    ["lib.es2015.core.d.ts", "findIndex(predicate: (value: T, index: number, obj: readonly T[]) => unknown, thisArg?: any): number;"]]
    .map(([file, text]): Reviewed => ({ file: file ?? "", text: text ?? "",
      why: "the callback's receiver is any value: the member calls it with thisArg as this (TScert's overlay drops it)" })),
  { file: "lib.es5.d.ts", text: "(value?: any): number;", why: `Number(v) ${coercion}` },
  { file: "lib.es2015.symbol.wellknown.d.ts", text: "[Symbol.hasInstance](value: any): boolean;",
    why: "`instanceof` takes any left operand: OrdinaryHasInstance returns false for a non-object" },
  { file: "lib.es5.d.ts", text: "getPrototypeOf(o: any): any;",
    why: "Object.getPrototypeOf takes any value: ToObject throws on null and undefined, a primitive's wrapper otherwise" },
  { file: "lib.es2015.reflect.d.ts", text: "function set(target: object, propertyKey: PropertyKey, value: any, receiver?: any): boolean;",
    why: "Reflect.set stores any value (what it then breaks is a mutation, not an any)" },
  { file: "console.d.ts", text: "log(message?: any, ...optionalParams: any[]): void;",
    why: "Node's console.log formats any value (util.format)" },
  { file: "process.d.ts", text: "send?( message: any, sendHandle?: SendHandle, options?: MessageOptions, callback?: (error: Error | null) => void, ): boolean;", why: sending },
  { file: "process.d.ts", text: "send?( message: any, sendHandle: SendHandle, callback?: (error: Error | null) => void, ): boolean;", why: sending },
  { file: "process.d.ts", text: "send?( message: any, callback: (error: Error | null) => void, ): boolean;", why: sending },
];

/* ------------------------------------------------- the overlay's contracts -- */

/** The definitions the overlay's contracts name, as global type aliases. */
const definitions: ReadonlyMap<string, TypeDefinition> = new Map(globalsOverlay
  .flatMap((entry) => entry.definitions ?? []).map((definition) => [definition.declaration.name, definition]));

/** The TypeScript a type term writes, or `null` for a term TypeScript has no
 * spelling of here. */
function print(term: TypeTerm): string | null {
  const all = (terms: readonly TypeTerm[], separator: string): string | null => {
    const parts = terms.map(print);
    return parts.every((part): part is string => part !== null) ? parts.map((p) => `(${p})`).join(separator) : null;
  };
  switch (term.k) {
    case "atom": return term.name === "nonHost" ? "unknown" : term.name === "nonHostObject" ? "object" : term.name === "function" ? "((...args: never) => unknown)"
      : term.name === "class" ? "(abstract new (...args: never) => unknown)" : term.name;
    case "literal": return term.text;
    case "union": return term.parts.length ? all(term.parts, " | ") : "never";
    case "intersection": return term.parts.length ? all(term.parts, " & ") : "unknown";
    case "array": {
      const element = print(term.element);
      return element === null ? null : `${term.readonly ? "readonly " : ""}(${element})[]`;
    }
    case "tuple": {
      const required = term.required.map(print), optional = term.optional.map(print);
      const rest = term.rest === null ? null : print(term.rest);
      if (![...required, ...optional].every((p): p is string => p !== null) || (term.rest !== null && rest === null)) return null;
      const positions = [...required, ...optional.map((p) => `(${p})?`), ...(rest === null ? [] : [`...(${rest})[]`])];
      return `${term.readonly ? "readonly " : ""}[${positions.join(", ")}]`;
    }
    case "object": {
      if (term.calls.length || term.numberIndex || term.symbolIndex || term.prototype) return null;
      const fields: string[] = [];
      for (const field of term.fields) {
        const type = print(field.type);
        if (type === null || typeof field.name !== "string") return null;
        fields.push(`${field.readonly ? "readonly " : ""}${JSON.stringify(field.name)}${field.optional ? "?" : ""}: ${type};`);
      }
      if (term.stringIndex) {
        const value = print(term.stringIndex.value);
        if (value === null) return null;
        fields.push(`${term.stringIndex.readonly ? "readonly " : ""}[key: string]: ${value};`);
      }
      return `{ ${fields.join(" ")} }`;
    }
    case "constructor": {
      const signature = printSignature({ binders: [], params: term.params, result: term.result,
        ...(term.rest === null ? {} : { rest: term.rest }) });
      if (signature === null) return null;
      const fields: string[] = [];
      for (const field of term.statics ?? []) {
        const type = print(field.type);
        if (type === null || typeof field.name !== "string") return null;
        fields.push(`${field.readonly ? "readonly " : ""}${JSON.stringify(field.name)}: ${type};`);
      }
      return `{ new ${signature}; ${fields.join(" ")} }`;
    }
    case "function": {
      const signature = printSignature({ binders: [], params: term.params, result: term.result,
        ...(term.rest === null ? {} : { rest: term.rest }) });
      if (signature === null) return null;
      const receiver = term.receiver && print(term.receiver);
      if (term.receiver && receiver === null) return null;
      const arrow = signature.replace(/\): /, ") => ");
      return receiver ? arrow.replace("(", `(this: ${receiver}${term.params.length || term.rest ? ", " : ""}`) : arrow;
    }
    case "binder": return term.name;
    case "reference": {
      const args = term.args.map(print);
      if (!args.every((a): a is string => a !== null)) return null;
      const target = term.reference.target;
      const name = target.module.startsWith("tscert/") ? `TScert${term.reference.name}` : term.reference.name;
      return args.length ? `${name}<${args.join(", ")}>` : name;
    }
    default: return null;
  }
}

/** A stated signature as TypeScript writes one: `<B>(p0: A, p1?: B, ...rest: C[]): R`,
 * a trailing parameter whose type admits `undefined` optional. */
function printSignature(stated: Stated): string | null {
  const params = stated.params.map(print);
  const result = print(stated.result);
  const rest = stated.rest === undefined ? undefined : print(stated.rest);
  if (!params.every((p): p is string => p !== null) || result === null || rest === null) return null;
  const admitsUndefined = (term: TypeTerm): boolean =>
    (term.k === "atom" && term.name === "undefined") || (term.k === "union" && term.parts.some(admitsUndefined));
  let required = stated.params.length;
  while (required > 0 && stated.params[required - 1] && admitsUndefined(stated.params[required - 1] ?? stated.result)) required--;
  const written = params.map((p: string | null, i) => `p${i}${i >= required ? "?" : ""}: ${p}`);
  if (rest !== undefined) written.push(`...rest: (${rest})[]`);
  const binders = stated.binders.length ? `<${stated.binders.join(", ")}>` : "";
  return `${binders}(${written.join(", ")}): ${result}`;
}

/** The signatures an overlay entry states, as TypeScript writes them, or
 * `null` where one has no spelling here; `undefined` where it states none. */
function statedSignatures(entry: GlobalEntry): string[] | null | undefined {
  if (entry.stated === undefined && entry.forms === undefined) return undefined;
  const library = (name: string, args: TypeTerm[]): TypeTerm => ({ k: "reference", args, span: [0, 0],
    reference: { name, span: [0, 0], arguments: args.map(() => [0, 0]), target: { module: "typescript/lib", name, span: [0, 0] } } });
  const stated = typeof entry.stated === "function" ? entry.stated(library, nativeCollectionView) : entry.stated;
  const forms = typeof entry.forms === "function" ? entry.forms(library, nativeCollectionView) : entry.forms;
  const printed = [...(stated === undefined ? [] : [stated]), ...(forms ?? [])].map(printSignature);
  return printed.every((p): p is string => p !== null) ? printed : null;
}

/** The overlay's entries by their declarations' text. */
const overlaid: ReadonlyMap<string, GlobalEntry[]> = globalsOverlay.reduce((map, entry) =>
  map.set(entry.signature, [...(map.get(entry.signature) ?? []), entry]), new Map<string, GlobalEntry[]>());

/** Declarations the shadowed standard library adds, as a global script:
 * the opaque type, and the definitions the overlay's contracts name. */
export function prelude(): string {
  const aliases = [...definitions.values()].flatMap((definition) => {
    const expression = definition.expression === null ? null : print(definition.expression);
    const parameters = definition.parameters.map((p) => p.name);
    return expression === null ? [] : [`type TScert${definition.declaration.name}${parameters.length ? `<${parameters.join(", ")}>` : ""} = ${expression};`];
  });
  return `
declare const tscertAny: unique symbol;
/** What a declaration types \`any\`: no value is assignable to it, and it is
 * assignable only to \`unknown\`, \`{}\` and \`object\`. */
interface ${OPAQUE} { readonly [tscertAny]: never }
${aliases.join("\n")}
`;
}

/* ---------------------------------------------------------- the rewrite -- */

/** An input of a declaration read at a contract, for the review list. */
export interface ReplacedInput {
  file: string;
  member: string;
  contract: string;
}

/** A position under a type-level wildcard: its polarity there. */
type Wildcard = 1 | -1 | null;

/** The declaration file's text with each `any` replaced, and the members
 * read at a contract; `host` for the compiler API's files. */
export function shadowText(source: SourceFile, text: string, host: boolean): { text: string; inputs: ReplacedInput[] } {
  const edits: { start: number; end: number; text: string }[] = [];
  const inputs: ReplacedInput[] = [];
  const file = path.basename(source.fileName);
  const library = file.startsWith("lib.") && file.endsWith(".d.ts");
  const memberText = (member: Node): string => member.getText(source).trim().replace(/\s+/g, " ");
  const replace = (node: Node, replacement: string): void => {
    edits.push({ start: node.getStart(source), end: node.end, text: replacement });
  };
  // Every `any` below `node` read as `unknown`, as the front end reads a
  // reviewed declaration's.
  const asUnknown = (node: Node): void => {
    if (node.kind === ts.SyntaxKind.AnyKeyword) replace(node, "unknown");
    else node.forEachChild(asUnknown);
  };
  const visit = (node: Node, wildcard: Wildcard): void => {
    if (node.kind === ts.SyntaxKind.AnyKeyword)
      return replace(node, wildcard === null ? OPAQUE : wildcard === 1 ? "unknown" : "never");
    if (wildcard === null && isMember(node)) {
      const written = memberText(node);
      const review = reviewed.find((entry) => entry.file === file && entry.text === written);
      if (review) {
        if (review.contract !== undefined) replace(node, review.contract);
        else asUnknown(node);
        inputs.push({ file: source.fileName, member: written, contract: review.contract ?? "unknown, by a review here" });
        return;
      }
      const entries = library && holdsAny(node) ? overlaid.get(written) : undefined;
      if (entries) {
        const signatures = entries.flatMap((entry) => statedSignatures(entry) ?? []);
        const stated = entries.map(statedSignatures);
        if (stated.every((s) => s === undefined)) {
          asUnknown(node);
          inputs.push({ file: source.fileName, member: written, contract: "unknown, by the overlay" });
          return;
        }
        if (stated.every((s) => s !== null) && signatures.length && rewriteSignature(node, signatures, source, edits)) {
          inputs.push({ file: source.fileName, member: written, contract: `the overlay's ${signatures.join("; ")}` });
          return;
        }
      }
    }
    if (ts.isTypeOperatorNode(node) && node.operator === ts.SyntaxKind.KeyOfKeyword && node.type.kind === ts.SyntaxKind.AnyKeyword)
      return replace(node, "(string | number | symbol)");
    if (ts.isTypeParameterDeclaration(node)) {
      if (node.constraint) visit(node.constraint, 1);
      const fallback = node.defaultType;
      if (fallback?.kind === ts.SyntaxKind.AnyKeyword) {
        // A signature's parameter is inferred at each call: its default
        // `any` is deleted, the constraint kept, unless an earlier parameter
        // has a default, after which a required one may not follow: then the
        // default is the opaque type, a value-level `any`. A type's stands
        // where a reference leaves it out, as a value with no guarantee.
        const owner = node.parent;
        const signature = owner !== undefined && (ts.isFunctionLikeDeclaration(owner) || ts.isMethodSignatureDeclaration(owner) ||
          ts.isCallSignatureDeclaration(owner) || ts.isConstructSignatureDeclaration(owner) ||
          ts.isFunctionTypeNode(owner) || ts.isConstructorTypeNode(owner));
        const siblings: readonly Node[] = owner === undefined ? [] : childrenOf(owner, "typeParameters");
        const earlier = siblings.slice(0, siblings.indexOf(node))
          .some((sibling) => ts.isTypeParameterDeclaration(sibling) && sibling.defaultType !== undefined);
        edits.push(signature && !earlier ? { start: (node.constraint ?? node.name).end, end: fallback.end, text: "" }
          : { start: fallback.getStart(source), end: fallback.end, text: signature ? OPAQUE : "unknown" });
      } else if (fallback) visit(fallback, wildcard);
      return;
    }
    if (ts.isConditionalTypeNode(node)) {
      visit(node.checkType, wildcard);
      visit(node.extendsType, wildcard ?? 1);
      visit(node.trueType, wildcard);
      visit(node.falseType, wildcard);
      return;
    }
    if (wildcard !== null && ts.isParameterDeclaration(node)) {
      if (node.type) visit(node.type, wildcard === 1 ? -1 : 1);
      return;
    }
    if (host && (ts.isPropertySignatureDeclaration(node) || ts.isPropertyDeclaration(node)) && readsAsOptionalUnknown(node)) {
      const type = node.type;
      if (type) replace(type, "unknown");
      if (!childOf(node, "postfixToken")) edits.push({ start: node.name.end, end: node.name.end, text: "?" });
      return;
    }
    node.forEachChild((child) => visit(child, wildcard));
  };
  source.forEachChild((child) => visit(child, null));
  let out = text;
  for (const edit of edits.sort((a, b) => b.start - a.start)) out = out.slice(0, edit.start) + edit.text + out.slice(edit.end);
  return { text: out, inputs };
}

/** Whether a declaration writes `any`: only such a member is read at the
 * overlay's contract. */
function holdsAny(node: Node): boolean {
  let found = false;
  const look = (child: Node): void => {
    if (child.kind === ts.SyntaxKind.AnyKeyword) found = true;
    else if (!found) child.forEachChild(look);
  };
  look(node);
  return found;
}

/** A declaration a contract states: a function, method, call or construct
 * signature, or a property. */
function isMember(node: Node): boolean {
  return ts.isFunctionDeclaration(node) || ts.isMethodSignatureDeclaration(node) || ts.isMethodDeclaration(node) ||
    ts.isCallSignatureDeclaration(node) || ts.isConstructSignatureDeclaration(node) ||
    ts.isConstructorDeclaration(node) || ts.isPropertySignatureDeclaration(node);
}

/** Replace a signature's binders, parameters and result by each printed
 * signature in turn, as overloads; `false` for a member with no signature. */
function rewriteSignature(node: Node, signatures: string[], source: SourceFile,
    edits: { start: number; end: number; text: string }[]): boolean {
  if (!(ts.isFunctionDeclaration(node) || ts.isMethodSignatureDeclaration(node) || ts.isMethodDeclaration(node) ||
    ts.isCallSignatureDeclaration(node) || ts.isConstructSignatureDeclaration(node)) || !node.type) return false;
  const head = source.text.slice(node.getStart(source), (node.typeParameters ?? node.parameters).pos - 1);
  const end = node.type.end;
  edits.push({ start: node.getStart(source), end, text: signatures.map((signature, i) => `${i ? "; " : ""}${head}${signature}`).join("") });
  return true;
}
