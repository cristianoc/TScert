/* TypeScript's evaluation of a declaration's computed type syntax at one
 * application (SOURCE-CONTRACTS.md, "Written applications").
 *
 * A form in a declaration's parameter list, `keyof U` in
 * `type G<T, U = T, K extends keyof U = keyof U>`, names the declaration's
 * parameters; what it denotes at an application `G<σ⃗>` is what TypeScript
 * computes for it with the parameters bound to the arguments, the omitted
 * ones to their defaults. The checker answers that for a type node in its
 * program, and has no operation instantiating a declaration's syntax. So the
 * question is asked in a probe program: the project's files, two of them
 * with a declaration added,
 *
 *   type P<the declaration's parameter list, verbatim> = <the form>;
 *   type U = P<the application's written arguments, verbatim>;
 *
 * `P` where the declaration stands (beside it, in a global augmentation of
 * its module) or, where that file cannot be read again (a standard library
 * file), beside `U`; `U` at the end of the statement list holding the
 * application. TypeScript completes the omitted arguments with the defaults,
 * substitutes and evaluates the form: `U`'s type is the answer.
 *
 * A copy means what the original means only where every name in it resolves
 * to what it resolves to where it is written. Each name in the copied
 * parameter list, form and arguments is checked: its symbol's declarations
 * in the probe program, mapped back to the original files, must be its
 * symbol's declarations in the original program. A name declared inside the
 * copied text (a parameter, a mapped type's key) maps to the original copy.
 * Any difference, a `this` type, or an application in a file that cannot be
 * read again refuses the evaluation. The answer is read from the checker's
 * type objects: literals, primitives and unique symbols, and references to
 * classes and interfaces mapped back to their original declarations with
 * every argument represented. Other results are refused.
 */
// files.mts makes every file-system failure a tool failure.
import { present } from "./files.mts";

import { TypeFlags, isTypeReference, isUnionType, type Checker, type Program, type Symbol, type Type } from "typescript/unstable/sync";
import * as ts from "typescript/unstable/ast";
import type { Identifier, Node, SourceFile, TypeNode } from "typescript/unstable/ast";
import { isInstanceReference, literalUnion } from "./computed-types.mts";
import type { TypeTerm } from "./declaration-types.mts";
import type { Span } from "./span.mts";
import { childrenOf, nameOf, isTypeAlias } from "./syntax.mts";


/** A symbol of the checker. */
type Symbolic = Symbol;

/** A program over the project's files with some of them replaced. */
export type ProbeProgram = <T>(files: ReadonlyMap<string, string>,
  read: (program: Program, checker: Checker) => T) => T;

/** One evaluation: `form`, written in `declaration` (whose `parameters` are
 * merged across its declarations), at the application `use` (a node whose
 * `typeArguments` are its written arguments). */
export type ProbeRequest = { declaration: Node; parameters: readonly MergedParameter[]; form: TypeNode; use: Node;
  span: Span; what: string };
/** A declaration's type parameter at one position, its merged declarations
 * together: its name, and the bound and default some declaration states;
 * `captured` for an enclosing type parameter a type declared in a block
 * closes over (SOURCE-CONTRACTS.md, "Block-scoped type declarations"). */
export type MergedParameter = { name: Identifier; constraint: TypeNode | undefined; default: TypeNode | undefined;
  captured?: true };

/** Original text copied into the probe: `[start, end)` of `file`. */
type Copy = { file: string; start: number; end: number };
/** A piece of inserted text: a copy, or text of its own; `mark` names the
 * generated declaration or reference it starts. */
type Mark = "probe" | "use" | "reference";
type Piece = { text: string; copy?: Copy; mark?: Mark };
/** Pieces inserted at offset `at` of a file. */
type Edit = { at: number; pieces: Piece[] };

/** The end offset of a statement list a declaration can be added to, in its
 * file's text; null for a node that is no such list. */
function listEnd(list: Node): number | null {
  if (ts.isSourceFile(list)) return list.end;
  if (ts.isBlock(list) || ts.isModuleBlock(list)) return list.end - 1;
  if (ts.isCaseClause(list) || ts.isDefaultClause(list)) return list.end;
  return null;
}

/** The type arguments written at an application. */
function argumentsOf(use: Node): readonly TypeNode[] {
  const value: unknown = Reflect.get(use, "typeArguments");
  return Array.isArray(value) ? value.filter((n: unknown): n is TypeNode => !!n && typeof n === "object" && "kind" in n) : [];
}

/** Every identifier under `node`, `node` included. */
function identifiers(node: Node): Identifier[] {
  const found: Identifier[] = [];
  const visit = (n: Node): void => {
    if (ts.isIdentifier(n)) found.push(n);
    n.forEachChild(visit);
  };
  visit(node);
  return found;
}

/** Whether `node` is or holds a `this` type. */
const holdsThis = (node: Node): boolean =>
  node.kind === ts.SyntaxKind.ThisType || (node.forEachChild(c => holdsThis(c) || undefined) ?? false);

/** The node passing `test` that spans exactly `[start, end)` of `file`. */
function nodeAt<N extends Node>(file: SourceFile, start: number, end: number, test: (n: Node) => n is N): N | undefined {
  let found: N | undefined;
  const visit = (n: Node): void => {
    if (found || n.end < start || n.pos > end) return;
    if (test(n) && n.getStart(file) === start && n.end === end) found = n;
    else n.forEachChild(visit);
  };
  visit(file);
  return found;
}

export function makeProbe(original: { program: Program; checker: Checker }, probeProgram: ProbeProgram,
    unique: (name: Identifier) => number,
    readReference?: (name: Identifier, args: TypeTerm[], span: Span) => TypeTerm): (request: ProbeRequest) => TypeTerm {
  let count = 0;
  return ({ declaration, parameters, form, use, span, what }) => {
    const refuse = (why: string): never => {
      throw Error(`${what}: ${form.getText(form.getSourceFile())} at the application: ${why}`);
    };
    const declarationFile = declaration.getSourceFile();
    const useFile = use.getSourceFile();
    const args = argumentsOf(use);
    const copied: Node[] = [...parameters.flatMap(p => [p.name, ...(p.constraint ? [p.constraint] : []),
      ...(p.default ? [p.default] : [])]), form, ...args];
    if (copied.some(holdsThis)) refuse("a `this` type means what it means where it is written");
    // The statement list holding the application.
    let list: Node | undefined = use.parent;
    while (list && listEnd(list) === null) list = list.parent;
    if (!list || !present(useFile.fileName)) return refuse("its file cannot be read again with the probe beside it");
    const useEnd = listEnd(list) ?? useFile.end;
    const copy = (n: Node): Piece => {
      const file = n.getSourceFile();
      const start = n.getStart(file);
      return { text: file.text.slice(start, n.end), copy: { file: file.fileName, start, end: n.end } };
    };
    const listed = (nodes: readonly Node[]): Piece[] =>
      nodes.flatMap((n, i) => i ? [{ text: ", " }, copy(n)] : [copy(n)]);
    // Each position's parameter: its name, and its bound and default copied
    // from the declarations stating them.
    const parameterList: Piece[] = parameters.flatMap((p, i) => [...(i ? [{ text: ", " }] : []), copy(p.name),
      ...(p.constraint ? [{ text: " extends " }, copy(p.constraint)] : []),
      ...(p.default ? [{ text: " = " }, copy(p.default)] : [])]);
    // Names neither file spells; what binds them is checked in the probe,
    // and another pair is tried where they bind elsewhere.
    for (let tries = 0; tries < 8; tries++) {
    let k = count++;
    while ([declarationFile, useFile].some(f => f.text.includes(`__TScertProbe${k}`) || f.text.includes(`__TScertUse${k}`)))
      k = count++;
    const probeName = `__TScertProbe${k}`, useName = `__TScertUse${k}`;
    // `type P<the parameters> = form;` and `type U = P<the arguments>;`
    const probe: Piece[] = [{ text: `type ${probeName}<`, mark: "probe" }, ...parameterList, { text: "> = " },
      copy(form), { text: ";" }];
    const application: Piece[] = [{ text: "\n" }, { text: `type ${useName} = `, mark: "use" },
      { text: probeName, mark: "reference" },
      ...(args.length ? [{ text: "<" }, ...listed(args), { text: ">" }] : []), { text: ";\n" }];
    // The probe stands beside the declaration, at its module's top level,
    // where its file can be read again; otherwise beside the application.
    const edits = new Map<SourceFile, Edit[]>();
    const insert = (file: SourceFile, at: number, pieces: Piece[]): void => {
      edits.set(file, [...(edits.get(file) ?? []), { at, pieces }]);
    };
    if (ts.isSourceFile(declaration.parent) && present(declarationFile.fileName)) {
      const module = declarationFile.externalModuleIndicator !== undefined;
      insert(declarationFile, declarationFile.end, [{ text: module ? "\ndeclare global {\n" : "\n" }, ...probe,
        { text: module ? "\n}\n" : "\n" }]);
      insert(useFile, useEnd, application);
    } else insert(useFile, useEnd, [{ text: "\n" }, ...probe, ...application]);
    // The edited texts, each copy's offset in them, and each insertion's.
    const files = new Map<string, string>();
    const placed: { copy: Copy; into: string; at: number }[] = [];
    const marks = new Map<Mark, { file: string; at: number }>();
    const inserted = new Map<string, { start: number; end: number }[]>();
    for (const [file, list] of edits) {
      const sorted = [...list].sort((a, b) => a.at - b.at);
      let out = "", last = 0;
      const ranges: { start: number; end: number }[] = [];
      for (const edit of sorted) {
        out += file.text.slice(last, edit.at);
        last = edit.at;
        const start = out.length;
        for (const piece of edit.pieces) {
          if (piece.copy) placed.push({ copy: piece.copy, into: file.fileName, at: out.length });
          if (piece.mark) marks.set(piece.mark, { file: file.fileName, at: out.length });
          out += piece.text;
        }
        ranges.push({ start, end: out.length });
      }
      files.set(file.fileName, out + file.text.slice(last));
      inserted.set(file.fileName, ranges);
    }
    // An offset of an edited text: the original offset it stands for, inside
    // a copy the offset it copies, inside other inserted text none.
    const back = (file: string, offset: number): { file: string; offset: number } | null => {
      for (const p of placed)
        if (p.into === file && offset >= p.at && offset <= p.at + p.copy.end - p.copy.start)
          return { file: p.copy.file, offset: p.copy.start + offset - p.at };
      let at = offset;
      for (const range of inserted.get(file) ?? []) {
        if (offset >= range.start && offset < range.end) return null;
        if (range.end <= offset) at -= range.end - range.start;
      }
      return { file, offset: at };
    };
    const answer = probeProgram(files, (program, checker): TypeTerm | null => {
      const where = (node: Node, map: boolean): unknown => {
        const file = node.getSourceFile();
        const start = node.getStart(file);
        if (!map) return [file.fileName, start, node.end];
        const from = back(file.fileName, start), to = back(file.fileName, node.end);
        return from && to && from.file === to.file ? [from.file, from.offset, to.offset] : "the probe";
      };
      const declarationsOf = (symbol: Symbolic | undefined, map: boolean): string =>
        JSON.stringify((symbol?.declarations ?? []).map(d => {
          const node = d.resolve();
          return node ? where(node, map) : null;
        }).map(d => JSON.stringify(d)).sort());
      // The generated declarations, where they were placed; the generated
      // reference binds to the inserted probe, and `U` is the one declaration
      // of its name.
      const marked = <N extends Node>(mark: Mark, test: (n: Node) => n is N): N | undefined => {
        const at = marks.get(mark);
        const file = at && program.getSourceFile(at.file);
        if (!at || !file) return undefined;
        let found: N | undefined;
        const visit = (n: Node): void => {
          if (found || n.end <= at.at || n.pos > at.at) return;
          if (test(n) && n.getStart(file) === at.at) found = n;
          else n.forEachChild(visit);
        };
        visit(file);
        return found;
      };
      const probeAlias = marked("probe", isTypeAlias);
      const alias = marked("use", isTypeAlias);
      const reference = marked("reference", ts.isIdentifier);
      if (!probeAlias || probeAlias.name.text !== probeName || !alias || alias.name.text !== useName ||
          !reference || reference.text !== probeName)
        return refuse("the probe program does not hold the generated declarations where they were placed");
      const only = (symbol: Symbolic | undefined, node: Node): boolean => {
        const nodes = (symbol?.declarations ?? []).map(d => d.resolve());
        return nodes.length === 1 && !!nodes[0] && nodes[0].getSourceFile().fileName === node.getSourceFile().fileName &&
          nodes[0].getStart(nodes[0].getSourceFile()) === node.getStart(node.getSourceFile()) && nodes[0].end === node.end;
      };
      if (!only(checker.getSymbolAtLocation(reference), probeAlias) || !only(checker.getSymbolAtLocation(alias.name), alias))
        return null;
      // A type parameter of the declaration, merged parts included, by its
      // position in their parameter lists.
      const declarationSymbol = (() => {
        const name = nameOf(declaration);
        return name ? declarationsOf(original.checker.getSymbolAtLocation(name), false) : null;
      })();
      const parameterIndex = (symbol: Symbolic | undefined): number | null => {
        // The first declaration's position, and whether every one states it.
        let index: number | undefined;
        let one = true;
        for (const d of symbol?.declarations ?? []) {
          const node = d.resolve();
          if (!node || !ts.isTypeParameterDeclaration(node)) return null;
          const owner = node.parent;
          const name = nameOf(owner);
          if (!name || declarationSymbol === null ||
              declarationsOf(original.checker.getSymbolAtLocation(name), false) !== declarationSymbol) return null;
          const at = childrenOf(owner, "typeParameters").indexOf(node);
          if (index === undefined) index = at;
          else if (at !== index) one = false;
        }
        return one && index !== undefined && index >= 0 ? index : null;
      };
      // Each copied name resolves to what it resolves to where it is written.
      for (const p of placed) {
        const into = program.getSourceFile(p.into);
        const source = copied.find(n => n.getSourceFile().fileName === p.copy.file &&
          n.getStart(n.getSourceFile()) === p.copy.start && n.end === p.copy.end);
        if (!into || !source) return refuse("the probe program lost a copied part");
        const file = source.getSourceFile();
        for (const name of identifiers(source)) {
          const start = p.at + name.getStart(file) - p.copy.start;
          const twin = nodeAt(into, start, start + name.end - name.getStart(file), ts.isIdentifier);
          if (!twin) return refuse(`the copy of ${name.text} is not where it was placed`);
          const symbol = original.checker.getSymbolAtLocation(name);
          const resolved = checker.getSymbolAtLocation(twin);
          const index = parameterIndex(symbol);
          const parameter = index === null ? undefined : probeAlias.typeParameters?.[index];
          if (index !== null ? !parameter || !only(resolved, parameter)
              : declarationsOf(symbol, false) !== declarationsOf(resolved, true))
            return refuse((symbol?.declarations ?? []).some(d => {
              const node = d.resolve();
              return !!node && ts.isTypeParameterDeclaration(node) && index === null;
            }) ? `${name.text} is a type parameter of the application's scope: the form is computed only at an instance`
              : `${name.text} does not resolve there to what it names where it is written`);
        }
      }
      const type: Type | undefined = checker.getTypeAtLocation(alias.name);
      if (!type || type.isErrorType()) return refuse("TypeScript computes no type for it");
      const read = (type: Type): TypeTerm => {
        const term = literalUnion(type, span, part => {
          const nodes = (part.getSymbol()?.declarations ?? []).map(d => d.resolve());
          const [node, ...more] = nodes;
          const name = node && (ts.isVariableDeclaration(node) || ts.isPropertySignatureDeclaration(node)) &&
            node.name && ts.isIdentifier(node.name) ? node.name : null;
          if (!name || more.length)
            return refuse(`the unique symbol ${checker.typeToString(part)} is declared by no one constant`);
          const file = name.getSourceFile();
          const from = back(file.fileName, name.getStart(file)), to = back(file.fileName, name.end);
          const source = from && to ? original.program.getSourceFile(from.file) : undefined;
          const mapped = from && to && source ? nodeAt(source, from.offset, to.offset, ts.isIdentifier) : undefined;
          if (!mapped) return refuse(`the unique symbol ${checker.typeToString(part)} is declared in the probe`);
          return unique(mapped);
        });
        if (!term && readReference) {
          if (isUnionType(type)) return { k: "union", parts: type.getTypes().map(read), span };
          const nodes = (type.getSymbol()?.declarations ?? []).map(d => d.resolve());
          const [node] = nodes;
          if (node && nodes.length === 1 && (ts.isInterfaceDeclaration(node) || ts.isClassDeclaration(node)) && node.name) {
            const file = node.getSourceFile();
            const from = back(file.fileName, node.name.getStart(file)), to = back(file.fileName, node.name.end);
            const source = from && to ? original.program.getSourceFile(from.file) : undefined;
            const name = from && to && source ? nodeAt(source, from.offset, to.offset, ts.isIdentifier) : undefined;
            if (!name) return refuse("the computed declaration exists only in the probe");
            if (!isInstanceReference(type))
              return refuse(`TypeScript computes ${checker.typeToString(type)}, which is not an object type reference`);
            const args = isTypeReference(type) ? checker.getTypeArguments(type).map(read) : [];
            return readReference(name, args, span);
          }
        }
        if (!term) {
          const parts = isUnionType(type) ? type.getTypes() : [type];
          return refuse(`TypeScript computes ${checker.typeToString(type)}, ` +
            (parts.some(t => t.flags & TypeFlags.EnumLiteral) ? "whose part is an enum member, outside the fragment"
              : "which is not a union of literals and primitives"));
        }
        return term;
      };
      return read(type);
    });
    if (answer) return answer;
    }
    return refuse("no fresh generated name binds to the inserted declarations");
  };
}
