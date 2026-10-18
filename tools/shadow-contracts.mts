/**
 * The external declarations a program is checked against with no `any`:
 * each declaration file outside the program's own sources (the standard
 * library, Node's types, the compiler API's), with every `any` replaced by
 * the contract it stands for. TypeScript then checks the program over these
 * declarations itself — inference, contextual typing, overloads and
 * assignability — and each error it reports is a place the program relied
 * on an `any` of a declaration.
 *
 * Each `any` of a declaration is read by its position:
 *
 * - a type-level wildcard, in a type parameter's constraint, a conditional
 *   type's check or extends clause, `infer`, `keyof` or `typeof`, is kept:
 *   it constrains types, and no value has it;
 * - a signature's type parameter's default `any` is removed: the parameter
 *   is inferred at each call, or is `unknown`; a type's is `unknown`, the
 *   value with no guarantee a reference leaving it out stands for;
 * - at a positive position (a result, a property, an index signature's
 *   value, a variable, a type argument there, a parameter of a function at a
 *   parameter) it is a value with no guarantee: `unknown`;
 * - at a negative position (a parameter, a callback's result) it is an input
 *   the declaration accepts. Where the reviewed overlay of library globals,
 *   of array and interface members or of library modules states the member
 *   (`library-globals.mts`, `array-prototype.mts`, `library-modules.mts`),
 *   the overlay's review holds of every value there: `unknown`. Where a
 *   reviewed contract below states it, that contract. Anywhere else it is
 *   `TScertUnreviewedAny`, which no value has: a use of the input is an
 *   error, refused until a contract is reviewed;
 * - a property of the compiler API's declarations declared `any` reads as
 *   an optional `unknown` (reading rule 2 of COMPILER-API.md), as the front
 *   end reads it;
 * - `JSON.parse` of a text returns `ParsedJson`, as the overlay states it.
 */
import path from "node:path";
import * as ts from "typescript/unstable/ast";
import type { Node, SourceFile } from "typescript/unstable/ast";
import { globalsOverlay } from "./library-globals.mts";
import { interfaceOverlay, overlay as arrayOverlay } from "./array-prototype.mts";
import { modulesOverlay } from "./library-modules.mts";
import { readsAsOptionalUnknown } from "./compiler-api.mts";
import { childOf } from "./syntax.mts";

/** The type of an unreviewed input: nothing is assignable to it. */
export const UNREVIEWED = "TScertUnreviewedAny";

/** Declarations the shadowed standard library adds, as a global script. */
export const PRELUDE: string = `
declare const tscertUnreviewed: unique symbol;
/** An input a declaration types \`any\` that no review states a contract of. */
interface ${UNREVIEWED} { readonly [tscertUnreviewed]: true }
/** What \`JSON.parse\` returns without a reviver (library-globals.mts). */
type TScertParsedJson = null | boolean | number | string | TScertParsedJson[] | { [key: string]: TScertParsedJson };
`;

/** A contract reviewed for the any check where no overlay states the member:
 * the declaration as written (whitespace collapsed), the declaration read
 * instead or, without one, every `any` input of it read as `unknown`, and
 * why that holds of the host. */
interface Reviewed {
  /** The declaration file's name. */
  file: string;
  text: string;
  contract?: string;
  why: string;
}

export const reviewed: readonly Reviewed[] = [
  { file: "lib.es2015.collection.d.ts", text: "new (): Map<any, any>;", contract: "new <K, V>(): Map<K, V>;",
    why: "an empty map holds no entry: it is a map at every key and value type, inferred from where it flows" },
  { file: "lib.es2015.iterable.d.ts", text: "new (): Map<any, any>;", contract: "new <K, V>(): Map<K, V>;",
    why: "an empty map holds no entry: it is a map at every key and value type, inferred from where it flows" },
  { file: "lib.es5.d.ts", text: "parse(text: string, reviver?: (this: any, key: string, value: any) => any): any;",
    contract: "parse(text: string): TScertParsedJson;",
    why: "the overlay's JSON.parse: the text only, a fresh ParsedJson (library-globals.mts)" },
  { file: "lib.es2015.symbol.wellknown.d.ts", text: "[Symbol.hasInstance](value: any): boolean;",
    why: "`instanceof` takes any left operand: OrdinaryHasInstance returns false for a non-object" },
  { file: "lib.es5.d.ts", text: "getPrototypeOf(o: any): any;",
    why: "Object.getPrototypeOf takes any value: ToObject throws on null and undefined, a primitive's wrapper otherwise" },
  { file: "lib.es2015.reflect.d.ts", text: "function set(target: object, propertyKey: PropertyKey, value: any, receiver?: any): boolean;",
    why: "Reflect.set stores any value (what it then breaks is a mutation, not an any)" },
  { file: "console.d.ts", text: "log(message?: any, ...optionalParams: any[]): void;",
    why: "Node's console.log formats any value (util.format), as the overlay's console.log states" },
  { file: "process.d.ts", text: "send?( message: any, sendHandle?: SendHandle, options?: MessageOptions, callback?: (error: Error | null) => void, ): boolean;",
    why: "process.send serializes any value, throwing or failing on one it cannot" },
  { file: "process.d.ts", text: "send?( message: any, sendHandle: SendHandle, callback?: (error: Error | null) => void, ): boolean;",
    why: "process.send serializes any value, throwing or failing on one it cannot" },
  { file: "process.d.ts", text: "send?( message: any, callback: (error: Error | null) => void, ): boolean;",
    why: "process.send serializes any value, throwing or failing on one it cannot" },
];

/** The member signatures the overlays of the standard library state, and
 * those the overlay of library modules states, exactly as reviewed. */
const libraryOverlaid: ReadonlySet<string> = new Set([
  ...globalsOverlay.map((entry) => entry.signature),
  ...arrayOverlay.map((entry) => entry.signature),
  ...Object.values(interfaceOverlay).flatMap((entries) => entries.map((entry) => entry.signature)),
]);
const moduleOverlaid: ReadonlySet<string> = new Set(modulesOverlay.map((entry) => entry.signature));

/** Who states that the `any` inputs of member `text` of the declaration file
 * `file` accept every value: an overlay, a review above, or none. */
function accepting(file: string, text: string): "the overlay's review" | "a review here" | undefined {
  const name = path.basename(file);
  if (name.startsWith("lib.") && libraryOverlaid.has(text)) return "the overlay's review";
  if (file.includes(`${path.sep}@types${path.sep}node${path.sep}`) && moduleOverlaid.has(text)) return "the overlay's review";
  return reviewed.some((entry) => entry.contract === undefined && entry.file === name && entry.text === text)
    ? "a review here" : undefined;
}

/** An input of a declaration replaced by a contract, for the review list. */
export interface ReplacedInput {
  file: string;
  member: string;
  contract: string;
}

/** A position's reading: a type-level wildcard, or a value's polarity. */
type Polarity = 1 | -1 | 0;

/** The declaration file's text with each `any` replaced by its contract,
 * and the inputs a review replaced; `host` for the compiler API's files. */
export function shadowText(source: SourceFile, text: string, host: boolean): { text: string; inputs: ReplacedInput[] } {
  const edits: { start: number; end: number; text: string }[] = [];
  const inputs: ReplacedInput[] = [];
  const memberText = (member: Node): string => member.getText(source).trim().replace(/\s+/g, " ");
  const visit = (node: Node, polarity: Polarity, member: Node | null): void => {
    if (node.kind === ts.SyntaxKind.AnyKeyword) {
      if (polarity === 1) edits.push({ start: node.getStart(source), end: node.end, text: "unknown" });
      if (polarity === -1) {
        const stated = member === null ? undefined : accepting(source.fileName, memberText(member));
        edits.push({ start: node.getStart(source), end: node.end, text: stated ? "unknown" : UNREVIEWED });
        if (stated && member) inputs.push({ file: source.fileName, member: memberText(member), contract: `unknown, by ${stated}` });
      }
      return;
    }
    // A member a reviewed contract states is read at that contract whole.
    const contract = reviewedContract(node, path.basename(source.fileName), memberText);
    if (contract) {
      edits.push({ start: node.getStart(source), end: node.end, text: contract.contract });
      inputs.push({ file: source.fileName, member: contract.text, contract: contract.contract });
      return;
    }
    const within: Node | null = member ?? (isMember(node) ? node : null);
    const each = (child: Node | undefined, p: Polarity): void => {
      if (child) visit(child, p, within);
    };
    if (ts.isTypeParameterDeclaration(node)) {
      // A signature's parameter is inferred at each call; a type's stands
      // where a reference leaves it out, as a value with no guarantee.
      const owner = node.parent;
      const inferred = owner !== undefined && (ts.isFunctionLikeDeclaration(owner) || ts.isMethodSignatureDeclaration(owner) ||
        ts.isCallSignatureDeclaration(owner) || ts.isConstructSignatureDeclaration(owner) ||
        ts.isFunctionTypeNode(owner) || ts.isConstructorTypeNode(owner));
      const fallback = node.defaultType;
      if (fallback?.kind === ts.SyntaxKind.AnyKeyword)
        edits.push(inferred ? { start: node.name.end, end: fallback.end, text: "" }
          : { start: fallback.getStart(source), end: fallback.end, text: "unknown" });
      return;
    }
    if (ts.isConditionalTypeNode(node)) {
      each(node.trueType, polarity);
      each(node.falseType, polarity);
      return;
    }
    if (ts.isInferTypeNode(node) || ts.isTypeQueryNode(node) ||
      (ts.isTypeOperatorNode(node) && node.operator === ts.SyntaxKind.KeyOfKeyword)) return;
    if (ts.isMappedTypeNode(node)) {
      each(node.type, polarity);
      return;
    }
    if (ts.isParameterDeclaration(node)) {
      each(node.type, polarity === 0 ? 0 : polarity === 1 ? -1 : 1);
      return;
    }
    if (ts.isIndexSignatureDeclaration(node)) {
      each(node.type, polarity);
      return;
    }
    if (host && (ts.isPropertySignatureDeclaration(node) || ts.isPropertyDeclaration(node)) && readsAsOptionalUnknown(node)) {
      const type = node.type;
      if (type) edits.push({ start: type.getStart(source), end: type.end, text: "unknown" });
      if (!childOf(node, "postfixToken")) edits.push({ start: node.name.end, end: node.name.end, text: "?" });
      return;
    }
    node.forEachChild((child) => {
      // A function's parameters run against its polarity; its type
      // parameters' constraints are type-level.
      if (ts.isTypeParameterDeclaration(child) && child.parent === node) visit(child, 0, within);
      else visit(child, polarity, within);
    });
  };
  source.forEachChild((child) => visit(child, 1, null));
  let out = text;
  for (const edit of edits.sort((a, b) => b.start - a.start)) out = out.slice(0, edit.start) + edit.text + out.slice(edit.end);
  return { text: out, inputs };
}

/** A declaration a review states inputs of: a function, method, call or
 * construct signature, or a property. */
function isMember(node: Node): boolean {
  return ts.isFunctionDeclaration(node) || ts.isMethodSignatureDeclaration(node) || ts.isMethodDeclaration(node) ||
    ts.isCallSignatureDeclaration(node) || ts.isConstructSignatureDeclaration(node) ||
    ts.isConstructorDeclaration(node) || ts.isPropertySignatureDeclaration(node);
}

function reviewedContract(node: Node, file: string, text: (member: Node) => string): (Reviewed & { contract: string }) | undefined {
  if (!isMember(node)) return undefined;
  const written = text(node);
  const entry = reviewed.find((candidate) => candidate.file === file && candidate.text === written);
  return entry?.contract === undefined ? undefined : { ...entry, contract: entry.contract };
}
