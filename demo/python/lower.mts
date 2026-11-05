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
  readonly records: Map<string, TypeTerm> = new Map();
  readonly bindings: Set<string> = new Set();
  depth: number = 0;

  bind(n: PyNode, name: string): void {
    if (["int", "str", "bool", "isinstance", "TypedDict"].includes(name))
      this.refuse(n, `rebinding the built-in ${name}`);
    if (this.bindings.has(name)) this.refuse(n, `rebinding ${name}`);
    this.bindings.add(name);
  }
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
    if (n._type === "BinOp" && nodeField(n, "op")._type === "BitOr")
      return { k: "union", span: spanOf(n), parts: [
        this.annotation(nodeField(n, "left"), n, role),
        this.annotation(nodeField(n, "right"), n, role),
      ] };
    if (n._type === "Name") {
      const record = this.records.get(stringField(n, "id"));
      if (record) return record;
    }
    const name = n._type === "Name" ? annotations.get(stringField(n, "id")) : undefined;
    if (name === undefined) return this.refuse(n, `the annotation of a ${role} other than int, str, bool, their unions or a preceding TypedDict`);
    return { k: "atom", name, span: spanOf(n) };
  }

  /** The module's functions, in source order. */
  module(tree: PyNode, file: string, sourceSha256: string): Ast {
    const functions: FunctionAst[] = [];
    const names = new Set<string>();
    let imported = false;
    for (const s of nodeList(tree, "body")) {
      if (s._type === "ImportFrom") {
        const imports = nodeList(s, "names");
        const [only] = imports;
        if (imported || functions.length || this.records.size ||
            s.fields.get("module") !== "typing" || s.fields.get("level") !== 0 ||
            imports.length !== 1 || !only || stringField(only, "name") !== "TypedDict" ||
            only.fields.get("asname") !== null)
          this.refuse(s, "an import other than an initial from typing import TypedDict");
        imported = true;
        continue;
      }
      if (s._type !== "FunctionDef" && s._type !== "ClassDef")
        this.refuse(s, `the module statement ${s._type}`);
      const name = stringField(s, "name");
      if (names.has(name) || ["int", "str", "bool", "isinstance", "TypedDict"].includes(name))
        this.refuse(s, `a duplicate or reserved module name ${name}`);
      names.add(name);
      if (s._type === "FunctionDef") functions.push(this.function(s));
      else {
        const bases = nodeList(s, "bases");
        const [base] = bases;
        const parameters = s.fields.get("type_params");
        if (!imported || bases.length !== 1 || !base || base._type !== "Name" ||
            stringField(base, "id") !== "TypedDict" || nodeList(s, "keywords").length ||
            nodeList(s, "decorator_list").length || (Array.isArray(parameters) && parameters.length))
          this.refuse(s, "a class other than a total, non-generic TypedDict");
        const fields: { name: string; optional: boolean; readonly: boolean; type: TypeTerm; span: Span }[] = [];
        for (const field of nodeList(s, "body")) {
          if (field._type !== "AnnAssign" || optionalNode(field, "value") !== null)
            this.refuse(field, "a TypedDict member other than an annotation");
          const target = nodeField(field, "target");
          if (target._type !== "Name") this.refuse(target, "a non-name TypedDict field");
          const key = stringField(target, "id");
          if (fields.some((f) => f.name === key)) this.refuse(target, "a duplicate TypedDict field");
          fields.push({ name: key, optional: false, readonly: false,
            type: this.annotation(nodeField(field, "annotation"), field, "field"), span: spanOf(field) });
        }
        this.records.set(name, { k: "object", fields, stringIndex: null, calls: [], span: spanOf(s) });
      }
    }
    if (!functions.length) this.refuse(tree, "a module without functions");
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
    this.bindings.clear();
    this.depth = 0;
    // The name follows `def` and its whitespace.
    const [start] = spanOf(def);
    const at = this.source.indexOf(name, start + "def".length);
    const params = nodeList(args, "args").map((a): FunctionParamAst => {
      const param = stringField(a, "arg");
      this.bind(a, param);
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
      case "Assign": {
        const targets = nodeList(s, "targets");
        const [target] = targets;
        if (targets.length !== 1 || !target) return this.refuse(s, "a chained assignment");
        const rhs = this.expression(nodeField(s, "value"));
        if (target._type === "Subscript") {
          const { receiver, field } = this.item(target);
          return { k: "effect", pos: spanOf(s), e: { k: "write", pos: spanOf(s), receiver, field, rhs } };
        }
        if (target._type !== "Name" || this.depth !== 0)
          return this.refuse(target, "a local binding outside the function's outer block");
        const name = stringField(target, "id");
        this.bind(target, name);
        return { k: "const", pos: spanOf(s), bindings: [{ name, namePos: spanOf(target),
          annot: null, init: rhs, early: false }] };
      }
      case "If": {
        const orelse = nodeList(s, "orelse");
        this.depth++;
        const then = this.block(nodeList(s, "body"));
        const else_ = orelse.length === 0 ? null : this.block(orelse);
        this.depth--;
        return {
          k: "if",
          pos: spanOf(s),
          cond: this.expression(nodeField(s, "test")),
          then,
          else_,
        };
      }
      default:
        return this.refuse(s, `the statement ${s._type}`);
    }
  }

  /** Literal string keys denote required record fields, read and written once. */
  item(e: PyNode): { receiver: Expr; field: string } {
    const key = nodeField(e, "slice");
    const field = key.fields.get("value");
    if (key._type !== "Constant" || typeof field !== "string")
      return this.refuse(key, "a subscript other than a literal string key");
    return { receiver: this.expression(nodeField(e, "value")), field };
  }

  expression(e: PyNode): Expr {
    const pos = spanOf(e);
    switch (e._type) {
      case "Name": {
        const name = stringField(e, "id");
        if (!this.bindings.has(name)) return this.refuse(e, `an unbound name ${name}`);
        return { k: "id", pos, name };
      }
      case "Subscript": {
        const { receiver, field } = this.item(e);
        return { k: "read", pos, field, e: receiver };
      }
      case "Call": {
        const fn = nodeField(e, "func");
        const args = nodeList(e, "args");
        const [value, kind] = args;
        if (fn._type !== "Name" || stringField(fn, "id") !== "isinstance" ||
            args.length !== 2 || !value || !kind || kind._type !== "Name" ||
            stringField(kind, "id") !== "str" || nodeList(e, "keywords").length)
          return this.refuse(e, "a call other than isinstance(value, str)");
        return { k: "typeofTest", pos, shape: "string", equal: true, e: this.expression(value) };
      }
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
