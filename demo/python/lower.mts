// The demo's Python front end: a module of Python's syntax tree, as
// `py_ast.py` prints it, lowered onto the Fragment wire (`tools/fragment.mts`)
// that the OCaml producer and the Lean verifier read. The subset and the
// meaning each form is given are stated in this directory's README.

import type { Ast, Expr, FunctionAst, FunctionParamAst, Stmt } from "../../tools/fragment.mts";
import type { TypeTerm } from "../../tools/declaration-types.mts";
import type { Span } from "../../tools/span.mts";

/** A node of `py_ast.py`'s output: its class name, its span, and its fields. */
export type PyNode = { _type: string; span: Span | null; fields: Map<string, unknown> };

/** A construct outside the subset, with where it is written. */
export class Unsupported extends Error {}

const isSpan = (value: unknown): value is Span =>
  Array.isArray(value) && value.length === 2 && value.every((n: unknown) => typeof n === "number");

/** `value` as a node: an object with a string `_type`; anything else is refused. */
export function readNode(value: unknown): PyNode {
  if (typeof value !== "object" || value === null || Array.isArray(value)) throw Error("py_ast: not a node");
  const entries = new Map<string, unknown>(Object.entries(value));
  const type = entries.get("_type");
  if (typeof type !== "string") throw Error("py_ast: a node without its class");
  const span = entries.get("span");
  entries.delete("_type");
  entries.delete("span");
  return { _type: type, span: isSpan(span) ? span : null, fields: entries };
}

const nodeField = (n: PyNode, name: string): PyNode => readNode(n.fields.get(name));
const optionalNode = (n: PyNode, name: string): PyNode | null => {
  const value = n.fields.get(name);
  return value === null || value === undefined ? null : readNode(value);
};
const nodeList = (n: PyNode, name: string): PyNode[] => {
  const value = n.fields.get(name);
  if (!Array.isArray(value)) throw Error(`py_ast: ${n._type}.${name} is not a list`);
  return value.map(readNode);
};
const stringField = (n: PyNode, name: string): string => {
  const value = n.fields.get(name);
  if (typeof value !== "string") throw Error(`py_ast: ${n._type}.${name} is not a string`);
  return value;
};
const spanOf = (n: PyNode): Span => {
  if (n.span === null) throw Error(`py_ast: ${n._type} has no position`);
  return n.span;
};

/** The Python annotations of the subset, and the source types they lower to. */
const annotations: ReadonlyMap<string, "bigint" | "string" | "boolean"> = new Map([
  ["int", "bigint"],
  ["str", "string"],
  ["bool", "boolean"],
]);

/** Lowers one Python module; `source` is its text, whose UTF-16 offsets the spans count. */
export class Lowering {
  readonly source: string;
  constructor(source: string) {
    this.source = source;
  }

  refuse(n: PyNode, what: string): never {
    const [start] = n.span ?? [0, 0];
    const line = this.source.slice(0, start).split("\n").length;
    throw new Unsupported(`unsupported: ${what} at line ${line}`);
  }

  annotation(n: PyNode | null, owner: PyNode, role: string): TypeTerm {
    if (n === null) return this.refuse(owner, `an unannotated ${role}`);
    const name = n._type === "Name" ? annotations.get(stringField(n, "id")) : undefined;
    if (name === undefined) return this.refuse(n, `the annotation of a ${role} other than int, str or bool`);
    return { k: "atom", name, span: spanOf(n) };
  }

  /** The module's functions, in source order. */
  module(tree: PyNode, file: string, sourceSha256: string): Ast {
    const functions = nodeList(tree, "body").map((s) =>
      s._type === "FunctionDef" ? this.function(s) : this.refuse(s, `the module statement ${s._type}`));
    const declarations = { roots: [], definitions: [], values: [], symbols: [], applications: [] };
    return { file, sourceSha256, declarations, init: [], functions, modules: [] };
  }

  function(def: PyNode): FunctionAst {
    if (nodeList(def, "decorator_list").length > 0) this.refuse(def, "a decorator");
    const typeParams = def.fields.get("type_params");
    if (Array.isArray(typeParams) && typeParams.length > 0) this.refuse(def, "a type parameter");
    const args = nodeField(def, "args");
    for (const field of ["posonlyargs", "kwonlyargs", "defaults", "kw_defaults"])
      if (nodeList(args, field).length > 0) this.refuse(def, `a parameter list with ${field}`);
    if (optionalNode(args, "vararg") !== null || optionalNode(args, "kwarg") !== null)
      this.refuse(def, "a parameter list with *args or **kwargs");
    const name = stringField(def, "name");
    // The name follows `def` and its whitespace.
    const [start] = spanOf(def);
    const at = this.source.indexOf(name, start + "def".length);
    const params = nodeList(args, "args").map((a): FunctionParamAst => {
      const param = stringField(a, "arg");
      const [from] = spanOf(a);
      return { name: param, pos: [from, from + param.length], type: this.annotation(optionalNode(a, "annotation"), a, "parameter") };
    });
    return {
      name,
      namePos: [at, at + name.length],
      typeParams: [],
      params,
      retType: this.annotation(optionalNode(def, "returns"), def, "result"),
      guard: null,
      stated: null,
      completion: "sync",
      body: this.block(nodeList(def, "body")),
      strict: true,
    };
  }

  block(statements: PyNode[]): Stmt[] {
    return statements.map((s) => this.statement(s));
  }

  statement(s: PyNode): Stmt {
    switch (s._type) {
      case "Return": {
        const value = optionalNode(s, "value");
        if (value === null) return this.refuse(s, "a return without a value");
        return { k: "return", pos: spanOf(s), e: this.expression(value) };
      }
      case "If": {
        const orelse = nodeList(s, "orelse");
        return {
          k: "if",
          pos: spanOf(s),
          cond: this.expression(nodeField(s, "test")),
          then: this.block(nodeList(s, "body")),
          else_: orelse.length === 0 ? null : this.block(orelse),
        };
      }
      default:
        return this.refuse(s, `the statement ${s._type}`);
    }
  }

  expression(e: PyNode): Expr {
    const pos = spanOf(e);
    switch (e._type) {
      case "Name":
        return { k: "id", pos, name: stringField(e, "id") };
      case "Constant": {
        const value = e.fields.get("value");
        if (typeof value === "boolean") return { k: "lit", pos, lit: { a: "booleanlit", v: String(value) } };
        if (typeof value === "string") return { k: "lit", pos, lit: { a: "stringlit", v: value } };
        if (typeof value === "object" && value !== null && "int" in value && typeof value.int === "string")
          return { k: "lit", pos, lit: { a: "bigintlit", v: value.int } };
        return this.refuse(e, "a constant other than an int, a str or a bool");
      }
      case "BinOp": {
        const op = nodeField(e, "op")._type;
        const l = this.expression(nodeField(e, "left")), r = this.expression(nodeField(e, "right"));
        if (op === "Add") return { k: "arith", pos, op: "add", l, r };
        if (op === "Sub") return { k: "arith", pos, op: "sub", l, r };
        return this.refuse(e, `the operator ${op}`);
      }
      case "Compare": {
        const ops = nodeList(e, "ops"), comparators = nodeList(e, "comparators");
        const [only] = ops, [right] = comparators;
        if (ops.length !== 1 || only === undefined || right === undefined) return this.refuse(e, "a chained comparison");
        const l = this.expression(nodeField(e, "left")), r = this.expression(right);
        switch (only._type) {
          case "Lt": return { k: "arith", pos, op: "lt", l, r };
          case "LtE": return { k: "arith", pos, op: "le", l, r };
          case "Gt": return { k: "arith", pos, op: "gt", l, r };
          case "GtE": return { k: "arith", pos, op: "ge", l, r };
          case "Eq": return { k: "bin", pos, op: "===", l, r };
          case "NotEq": return { k: "bin", pos, op: "!==", l, r };
          default: return this.refuse(e, `the comparison ${only._type}`);
        }
      }
      case "BoolOp": {
        const op = nodeField(e, "op")._type === "And" ? "&&" : "||";
        const [first, ...rest] = nodeList(e, "values");
        if (first === undefined) return this.refuse(e, "an empty Boolean operation");
        // `a and b and c` is `(a && b) && c`, each span from the first operand's start.
        return rest.reduce<Expr>((l, v) => {
          const r = this.expression(v);
          return { k: "bin", pos: [pos[0], spanOf(v)[1]], op, l, r };
        }, this.expression(first));
      }
      case "UnaryOp": {
        const op = nodeField(e, "op")._type;
        const operand = this.expression(nodeField(e, "operand"));
        if (op === "Not") return { k: "not", pos, e: operand };
        if (op === "USub") return { k: "unary", pos, op: "neg", e: operand };
        return this.refuse(e, `the unary operator ${op}`);
      }
      case "IfExp":
        return {
          k: "conditional",
          pos,
          cond: this.expression(nodeField(e, "test")),
          then: this.expression(nodeField(e, "body")),
          else_: this.expression(nodeField(e, "orelse")),
        };
      default:
        return this.refuse(e, `the expression ${e._type}`);
    }
  }
}
