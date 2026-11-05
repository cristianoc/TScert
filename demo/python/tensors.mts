// Tensor rank demo (README, "Tensor rank contracts"). Existing mechanisms: required readonly record fields state tensor metadata;
// DeclarationDocument.values supplies external operator contracts. The existing
// producer selects overloads; the existing Lean checker checks all applications
// and results. This prototype adds no tensor inference to the proof kernel.
import type { Ast, Expr, Stmt } from "../../tools/fragment.mts";
import type { TypeTerm, ValueRoot } from "../../tools/declaration-types.mts";
import type { ObligationDiagnostic } from "../../tools/diagnostic.mts";
import { decodeGraph, type TypeGraph } from "../../tools/type-graph.mts";
import type { Span } from "../../tools/span.mts";
import { Lowering as PythonLowering, readNode, type PyNode } from "./lower.mts";

const span: Span = [0, 0];
const literal = (value: number): TypeTerm => ({ k: "literal", name: "number", text: String(value), span });
function tensor(rank: number, last?: number): TypeTerm {
  const fields = [{ name: "ndim", optional: false, readonly: true, type: literal(rank), span }];
  if (last !== undefined) fields.push({ name: "%lastDimension%", optional: false, readonly: true, type: literal(last), span });
  return { k: "object", fields, stringIndex: null, calls: [], span };
}
const scalar = tensor(0), vector = tensor(1), matrix = tensor(2), column = tensor(2, 1);
const types: ReadonlyMap<string, TypeTerm> = new Map([
  ["Scalar", scalar], ["Vector", vector], ["Matrix", matrix], ["Column", column],
]);
function arrow(params: TypeTerm[], result: TypeTerm): TypeTerm {
  return { k: "function", effect: { footprint: { value: "keep", store: "keep" }, promise: null,
    fresh: false, receiverStore: false, onThrow: false, receiverOwn: false, freshObject: false,
    requires: null, elements: null }, receiver: null, params, rest: null, result, span };
}
const operators: ReadonlyMap<string, TypeTerm> = new Map([
  ["subtract", { k: "intersection", parts: [arrow([column, vector], matrix), arrow([vector, vector], vector)], span }],
  ["square", { k: "intersection", parts: [arrow([matrix], matrix), arrow([vector], vector)], span }],
  ["squeezeLast", arrow([column], vector)],
  ["squeezeAll", arrow([column], { k: "union", parts: [scalar, vector], span })],
  ["mean", arrow([{ k: "union", parts: [matrix, vector], span }], scalar)],
]);
function field(n: PyNode, key: string): PyNode { return readNode(n.fields.get(key)); }
function list(n: PyNode, key: string): PyNode[] {
  const raw = n.fields.get(key);
  if (!Array.isArray(raw)) throw Error(`missing list ${key}`);
  return raw.map(readNode);
}
function text(n: PyNode, key: string): string {
  const raw = n.fields.get(key);
  if (typeof raw !== "string") throw Error(`missing text ${key}`);
  return raw;
}
function position(n: PyNode): Span { if (!n.span) throw Error("missing span"); return n.span; }

export class TensorLowering extends PythonLowering {
  readonly used: Map<string, Span> = new Map();
  readonly imported: Set<string> = new Set();
  override bind(n: PyNode, name: string): void {
    if (types.has(name)) this.refuse(n, `rebinding the tensor contract ${name}`);
    super.bind(n, name);
  }
  override annotation(n: PyNode | null, owner: PyNode, role: string): TypeTerm {
    if (n?._type === "Name") {
      const type = types.get(text(n, "id"));
      if (type && this.imported.has(text(n, "id"))) return type;
    }
    return this.refuse(n ?? owner, `unsupported tensor ${role} contract`);
  }
  override module(tree: PyNode, file: string, sourceSha256: string): Ast {
    const body = list(tree, "body");
    const first = body[0];
    if (!first || first._type !== "ImportFrom" || text(first, "module") !== "rank_contracts" ||
        first.fields.get("level") !== 0 || list(first, "names").some((n) =>
          !types.has(text(n, "name")) || n.fields.get("asname") !== null))
      return this.refuse(first ?? tree, "expected rank_contracts import");
    for (const name of list(first, "names")) this.imported.add(text(name, "name"));
    const rest = body.slice(1);
    for (const statement of rest)
      if (statement._type === "FunctionDef" && types.has(text(statement, "name")))
        this.refuse(statement, "rebinding an imported tensor contract");
    if (rest.some((n) => n._type !== "FunctionDef")) return this.refuse(tree, "non-function module body");
    const raw = rest.map((n): Record<string, unknown> => {
      const value: Record<string, unknown> = { _type: n._type, span: n.span };
      for (const [name, field] of n.fields) value[name] = field;
      return value;
    });
    const ast = super.module({ ...tree, fields: new Map([["body", raw]]) }, file, sourceSha256);
    const values: ValueRoot[] = [...this.used].map(([name, at]) => {
      const type = operators.get(name);
      if (!type) throw Error("missing operator contract");
      return { binding: { local: `%tensor:${name}%`, imported: name, specifier: "torch-rank-contracts", span: at },
        declaration: { module: "torch-rank-contracts", name, span }, construct: false, typeParams: [], type };
    });
    return { ...ast, declarations: { ...ast.declarations, values } };
  }
  call(name: string, at: Span, token: Span, args: Expr[]): Expr {
    this.used.set(name, token);
    return { k: "apply", pos: at, callee: { k: "id", name: `%tensor:${name}%`, pos: token }, args };
  }
  override statement(s: PyNode): Stmt {
    // Tensor truthiness is data-dependent and may throw; a model record's
    // truthiness would erase that execution. This subset has return bodies.
    if (s._type !== "Return") return this.refuse(s, "tensor bodies contain only return statements");
    return super.statement(s);
  }
  override expression(e: PyNode): Expr {
    if (e._type === "BinOp") {
      if (field(e, "op")._type !== "Sub") return this.refuse(e, "unsupported tensor operator");
      const left = field(e, "left"), right = field(e, "right");
      const start = position(left)[1], end = position(right)[0];
      let offset = start;
      let token: Span | null = null;
      for (const line of this.source.slice(start, end).split("\n")) {
        const beforeComment = line.split("#")[0] ?? "";
        const op = beforeComment.indexOf("-");
        if (op >= 0) { token = [offset + op, offset + op + 1]; break; }
        offset += line.length + 1;
      }
      if (!token) return this.refuse(e, "the subtraction token is missing");
      return this.call("subtract", position(e), token, [this.expression(left), this.expression(right)]);
    }
    if (e._type === "Call") {
      const fn = field(e, "func");
      if (fn._type !== "Attribute" || list(e, "keywords").length) return this.refuse(e, "unsupported call");
      const name = text(fn, "attr"), args = list(e, "args");
      const end = position(fn)[1];
      const token: Span = [end - name.length, end];
      if (name === "squeeze") {
        if (!args.length) return this.call("squeezeAll", position(e), token, [this.expression(field(fn, "value"))]);
        const [arg] = args;
        if (args.length !== 1 || !arg || arg._type !== "UnaryOp" || field(arg, "op")._type !== "USub")
          return this.refuse(e, "only squeeze(-1) is supported");
        const value = field(arg, "operand").fields.get("value");
        if (typeof value !== "object" || value === null || !("int" in value) || value.int !== "1")
          return this.refuse(e, "only squeeze(-1) is supported");
        return this.call("squeezeLast", position(e), token, [this.expression(field(fn, "value"))]);
      }
      if ((name !== "square" && name !== "mean") || args.length) return this.refuse(e, "unsupported method");
      return this.call(name, position(e), token, [this.expression(field(fn, "value"))]);
    }
    if (e._type !== "Name") return this.refuse(e, "expression outside the tensor experiment");
    return super.expression(e);
  }
}

/** Rank-only explanation, derived from the checker's decoded return obligation. */
export function tensorObligation(record: ObligationDiagnostic, source: string): string | null {
  if (record.kind !== "node-typing" || record.source.sourceMap?.role !== "return-contract" ||
      record.sequent.term.kind !== "var") return null;
  const rows = decodeGraph(record.types);
  const actual = ranks(rows, record.sequent.context[record.sequent.term.i] ?? []);
  const expected = ranks(rows, record.sequent.type);
  if (!actual || !expected) return null;
  const at = record.source.sourceMap.pos;
  const expression = source.slice(at[0], at[1]);
  const show = (ns: number[]): string => ns.map((n) =>
    `rank ${n}${n === 0 ? " (scalar)" : n === 1 ? " (vector)" : n === 2 ? " (matrix)" : ""}`).join(" or ");
  return `${expression} may return ${show(actual)}. This return requires ${show(expected)}.`;
}
function ranks(rows: TypeGraph, labels: number[]): number[] | null {
  const result = new Set<number>();
  for (const label of labels) {
    const row = rows[label];
    if (!Array.isArray(row) || row.length !== 1) return null;
    const clause = row[0];
    if (typeof clause !== "object" || clause === null || !("refs" in clause)) return null;
    const fields = [...clause.refs.first, ...clause.refs.rest.flat(), ...clause.refs.views];
    const ndim = fields.find(([key]) => key === "ndim");
    if (!ndim) return null;
    for (const rankLabel of ndim[1]) {
      const row = rows[rankLabel];
      if (!Array.isArray(row)) return null;
      for (const atom of row) {
        if (typeof atom !== "object" || atom === null) return null;
        const bits = "numLit" in atom ? [atom.numLit.bits] : "numIn" in atom ? atom.numIn.bits : null;
        if (!bits) return null;
        for (const b of bits) {
          const view = new DataView(new ArrayBuffer(8));
          view.setBigUint64(0, BigInt(b));
          const n = view.getFloat64(0);
          if (!Number.isSafeInteger(n) || n < 0) return null;
          result.add(n);
        }
      }
    }
  }
  return result.size ? [...result].sort((a, b) => a - b) : null;
}
