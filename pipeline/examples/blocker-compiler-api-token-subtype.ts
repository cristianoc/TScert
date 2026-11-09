// A binary operator token meets the Node contract at a call, though the run's
// selection names some of its kinds and leaves the others: the operator
// token's tag set, which a selected shape's member is read at, is selected whole.
// Census functions:
// fragment-expressions.mts#chainComparison.
import * as ts from "typescript/unstable/ast";

import type {
  BinaryExpression,
  Identifier,
  Node,
} from "typescript/unstable/ast";

import type { Expr } from "../../tools/fragment.mts";

import { CHAIN } from "../../tools/fragment.mts";

import {
  bindingScope,
  skipParentheses,
} from "../../tools/fragment-support.mts";

import type { Gate } from "../../tools/fragment-parse.mts";

function chainReceiver(
  at: Node,
): Modifies<{ values: "any"; stores: "grow" }, Node | null> {
  return null;
}

function inertRead(
  gate: Gate,
  receiver: Node,
): Modifies<{ values: "any"; stores: "grow" }, boolean> {
  if (!ts.isIdentifier(receiver)) return false;
  const declaration = gate.resolve(receiver);
  return (
    declaration !== undefined && !(declaration.flags & ts.NodeFlags.Ambient)
  );
}

export function chainComparison(
  gate: Gate,
  node: BinaryExpression,
  op: "===" | "!==" | "==" | "!=",
  l: Expr,
  r: Expr,
): Modifies<{ values: "any"; stores: "grow" }, Expr | null> {
  const chainLeft = l.k === "optional";
  const chain = chainLeft ? l : r;
  const other = chainLeft ? r : l;
  if (chain.k !== "optional" || other.k !== "lit") return null;
  const source = chainReceiver(
    skipParentheses(chainLeft ? node.left : node.right),
  );
  if (!source || !inertRead(gate, source)) return null;
  const receiver = chain.receiver;

  const reread: Expr =
    receiver.k === "id"
      ? { k: "id", pos: chain.at, name: receiver.name }
      : { k: "this", pos: chain.at };

  const reads = (e: Expr): Expr | null => {
    if (e.k === "id" && e.name === CHAIN) return reread;
    if (e.k !== "read") return null;
    const inner = reads(e.e);
    return inner ? { ...e, e: inner } : null;
  };
  const body = reads(chain.body);
  if (!body) return null;
  const lit = other.lit.a;
  const equal = op === "===" || op === "==";

  const undefinedEquals =
    op === "==" || op === "!="
      ? lit === "null" || lit === "undefined"
      : lit === "undefined";
  const absent = undefinedEquals === equal;
  const test: Expr = {
    k: "bin",
    pos: chain.pos,
    op: absent ? "==" : "!=",
    l: receiver,
    r: { k: "lit", pos: [chain.at[0], chain.at[0] + 1], lit: { a: "null" } },
  };
  const comparison: Expr = {
    k: "bin",
    pos: gate.span(node.operatorToken),
    op,
    l: chainLeft ? body : other,
    r: chainLeft ? other : body,
  };
  return {
    k: "bin",
    pos: gate.span(node),
    op: absent ? "||" : "&&",
    l: test,
    r: comparison,
  };
}
