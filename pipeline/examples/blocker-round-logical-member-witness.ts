// Census functions: type-term.mts#typeTerm,#constructorForms and their callers;
// declaration-graph.mts#closeDeclarations,#collectFrom,#collectInstances,#collect,
// #elaborateDeclaration; computed-types.mts#computedType,#aliasApplication,
// #distributed,#inferredResult.
// A nonempty type literal whose every member is a construct signature.
import * as ts from "typescript/unstable/ast";

export function constructorsOnly(node: ts.Node): boolean {
  if (
    ts.isTypeLiteralNode(node) &&
    node.members.length &&
    node.members.every(ts.isConstructSignatureDeclaration)
  )
    return true;
  return false;
}

type ObjectTerm =
  | {
      k: "object";
      fields: string[];
      calls: string[];
      stringIndex: string | null;
    }
  | { k: "other" };

export function objectOnly(term: ObjectTerm): boolean {
  if (
    term.k !== "object" ||
    term.fields.length !== 1 ||
    term.calls.length ||
    term.stringIndex
  )
    return false;
  return true;
}

export function noParameters(
  owner: { heritageClauses?: string[] },
  last: { params: string[]; rest: string | null },
): boolean {
  if (owner.heritageClauses?.length || last.params.length || last.rest)
    return false;
  return true;
}
