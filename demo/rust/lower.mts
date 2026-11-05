// The demo's Rust front end: a crate of the subset, as `parse.mts` reads it,
// lowered onto the Fragment wire (`tools/fragment.mts`) that the OCaml
// producer and the Lean verifier read. The subset and the meaning each form
// is given are stated in this directory's README.

import type { Ast, Expr, FunctionAst, Stmt } from "../../tools/fragment.mts";
import type { TypeTerm } from "../../tools/declaration-types.mts";
import type { Span } from "../../tools/span.mts";
import { lineOf, Unsupported, type Prim, type RBlock, type RCrate, type RExpr, type RFn, type RStmt, type RStruct, type RType } from "./parse.mts";

const integers: readonly Prim[] = ["i32", "u32", "i64"];
const strings: readonly Prim[] = ["String", "&str"];
const isPrim = (t: RType, names: readonly Prim[]): boolean => t.k === "prim" && names.includes(t.name);
const show = (t: RType): string => (t.k === "prim" ? t.name : t.name);

/** Lowers one crate; `source` is its text, whose UTF-16 offsets the spans count. */
export class Lowering {
  readonly source: string;
  readonly structs: Map<string, RStruct>;
  readonly fns: Map<string, RFn>;
  /** The names in scope in the function being lowered, and their Rust types. */
  private env = new Map<string, RType>();
  private ret: RType | null = null;

  constructor(source: string, crate: RCrate) {
    this.source = source;
    this.structs = new Map(crate.structs.map((s) => [s.name, s]));
    this.fns = new Map(crate.fns.map((f) => [f.name, f]));
  }

  refuse(at: Span, what: string): never {
    throw new Unsupported(`unsupported: ${what} at line ${lineOf(this.source, at[0])}`);
  }

  /** The source type term a Rust type stands for. */
  term(t: RType): TypeTerm {
    if (t.k === "prim") {
      const name = t.name === "i64" ? "bigint" : t.name === "bool" ? "boolean" : strings.includes(t.name) ? "string" : "number";
      return { k: "atom", name, span: t.span };
    }
    const def = this.structs.get(t.name);
    if (def === undefined) return this.refuse(t.span, `the type ${t.name}, which no struct of the file declares`);
    return {
      k: "object",
      fields: def.fields.map((f) => ({ name: f.name, optional: false, readonly: true, type: this.term(f.type), span: f.span })),
      stringIndex: null, calls: [], span: t.span,
    };
  }

  /** The crate's functions, in source order. */
  crate(crate: RCrate, file: string, sourceSha256: string): Ast {
    for (const s of crate.structs)
      for (const f of s.fields) this.term(f.type);
    const functions = crate.fns.map((f) => this.function(f));
    const declarations = { roots: [], definitions: [], values: [], symbols: [], applications: [] };
    return { file, sourceSha256, declarations, init: [], functions, modules: [] };
  }

  function(f: RFn): FunctionAst {
    if (f.ret === null) this.refuse(f.span, "a function returning ()");
    this.ret = f.ret;
    this.env = new Map();
    const params = f.params.map((p) => {
      this.bind(p.name, p.span, p.type);
      return { name: p.name, pos: p.span, type: this.term(p.type) };
    });
    return {
      name: f.name, namePos: f.nameSpan, typeParams: [], params, retType: this.term(f.ret),
      guard: null, stated: null, completion: "sync", body: this.block(f.body, true), strict: true,
    };
  }

  private bind(name: string, at: Span, type: RType): void {
    if (this.env.has(name)) this.refuse(at, `the name ${name} bound twice in one function (shadowing)`);
    this.env.set(name, type);
  }

  /** A block's statements; where `tail` is set, the block ends the function
   * body and its tail is returned. */
  block(b: RBlock, tail: boolean): Stmt[] {
    const out = b.stmts.map((s) => this.statement(s));
    const t = b.tail;
    if (t === null) return out;
    // An `if` ending a block is a statement: its arms' tails are returned
    // where the block ends the function body, and are refused otherwise.
    if (t.k === "if") out.push(this.ifStatement(t, tail));
    else if (tail) out.push({ k: "return", pos: t.span, e: this.expr(t, this.ret).e });
    else return this.refuse(t.span, "a value at the end of a block whose value is unused");
    return out;
  }

  private ifStatement(e: Extract<RExpr, { k: "if" }>, tail: boolean): Stmt {
    const cond = this.check(e.cond, { k: "prim", name: "bool", span: e.cond.span });
    return { k: "if", pos: e.span, cond, then: this.block(e.then, tail), else_: e.else_ === null ? null : this.block(e.else_, tail) };
  }

  statement(s: RStmt): Stmt {
    switch (s.k) {
      case "let": {
        const { e, type } = this.expr(s.init, s.type);
        const bound = s.type ?? type;
        if (bound === null) return this.refuse(s.init.span, "an integer literal whose type no context fixes");
        if (s.type !== null) this.term(s.type);
        this.bind(s.name, s.nameSpan, bound);
        return { k: "const", pos: s.span, bindings: [{ name: s.name, namePos: s.nameSpan, annot: s.type && this.term(s.type), init: e, early: false }] };
      }
      case "return":
        return { k: "return", pos: s.span, e: this.expr(s.e, this.ret).e };
      case "expr":
        if (s.e.k === "if") return this.ifStatement(s.e, false);
        return this.refuse(s.span, "an expression statement");
    }
  }

  /** `e` lowered where a `bool` is required. */
  private check(e: RExpr, want: RType): Expr {
    return this.expr(e, want).e;
  }

  /** The type `e` has without context; null for an unsuffixed integer
   * literal and for an expression whose type only such literals fix. */
  natural(e: RExpr): RType | null {
    switch (e.k) {
      case "int": return e.suffix === null ? null : { k: "prim", name: e.suffix, span: e.span };
      case "float": return { k: "prim", name: "f64", span: e.span };
      case "str": return { k: "prim", name: "&str", span: e.span };
      case "bool": return { k: "prim", name: "bool", span: e.span };
      case "path": return this.env.get(e.name) ?? this.refuse(e.span, `the name ${e.name}, not a local of the function`);
      case "unary": return e.op === "!" ? { k: "prim", name: "bool", span: e.span } : this.natural(e.e);
      case "binary":
        if (["<", "<=", ">", ">=", "==", "!=", "&&", "||"].includes(e.op)) return { k: "prim", name: "bool", span: e.span };
        return this.natural(e.l) ?? this.natural(e.r);
      case "call": return this.fns.get(e.callee)?.ret ?? this.refuse(e.span, `a call of ${e.callee}, not a function of the file`);
      case "field": {
        const t = this.natural(e.e);
        const def = t?.k === "struct" ? this.structs.get(t.name) : undefined;
        const field = def?.fields.find((f) => f.name === e.name);
        return field?.type ?? this.refuse(e.span, `the field ${e.name}, not a field of a struct of the file`);
      }
      case "toString": return { k: "prim", name: "String", span: e.span };
      case "structLit": return { k: "struct", name: e.name, span: e.span };
      case "if": {
        const arm = (b: RBlock | null): RType | null => (b !== null && b.tail !== null ? this.natural(b.tail) : null);
        return arm(e.then) ?? arm(e.else_);
      }
    }
  }

  /** `e` lowered at the type `want` its context fixes (null: none), and its type. */
  expr(e: RExpr, want: RType | null): { e: Expr; type: RType | null } {
    const pos = e.span;
    switch (e.k) {
      case "int": {
        const type = e.suffix !== null ? { k: "prim" as const, name: e.suffix, span: pos } : want;
        if (type === null) return this.refuse(pos, "an integer literal whose type no context fixes");
        if (!isPrim(type, integers)) return this.refuse(pos, `an integer literal where ${show(type)} is required`);
        const digits = BigInt(e.digits).toString();
        if (type.k === "prim" && type.name === "i64") return { e: { k: "lit", pos, lit: { a: "bigintlit", v: digits } }, type };
        return { e: { k: "lit", pos, lit: { a: "numberlit", v: digits } }, type };
      }
      case "float": {
        if (want !== null && !isPrim(want, ["f64"])) return this.refuse(pos, `a float literal where ${show(want)} is required`);
        return { e: { k: "lit", pos, lit: { a: "numberlit", v: String(Number(e.text)) } }, type: this.natural(e) };
      }
      case "str": return { e: { k: "lit", pos, lit: { a: "stringlit", v: e.value } }, type: this.natural(e) };
      case "bool": return { e: { k: "lit", pos, lit: { a: "booleanlit", v: String(e.value) } }, type: this.natural(e) };
      case "path": return { e: { k: "id", pos, name: e.name }, type: this.natural(e) };
      case "unary": {
        if (e.op === "&") return this.expr(e.e, want);
        if (e.op === "!") {
          const inner = this.expr(e.e, { k: "prim", name: "bool", span: pos });
          if (inner.type === null || !isPrim(inner.type, ["bool"])) return this.refuse(pos, "`!` on another type than bool");
          return { e: { k: "not", pos, e: inner.e }, type: inner.type };
        }
        const type = this.natural(e.e) ?? want;
        if (type === null) return this.refuse(pos, "an integer literal whose type no context fixes");
        if (!isPrim(type, ["i32", "u32", "i64", "f64"])) return this.refuse(pos, `unary - on ${show(type)}`);
        return { e: { k: "unary", pos, op: "neg", e: this.expr(e.e, type).e }, type };
      }
      case "binary": {
        if (e.op === "&&" || e.op === "||") {
          const bool: RType = { k: "prim", name: "bool", span: pos };
          const l = this.expr(e.l, bool), r = this.expr(e.r, bool);
          for (const side of [l, r])
            if (side.type === null || !isPrim(side.type, ["bool"])) return this.refuse(pos, `${e.op} on another type than bool`);
          return { e: { k: "bin", pos, op: e.op, l: l.e, r: r.e }, type: bool };
        }
        const comparison = ["<", "<=", ">", ">=", "==", "!="].includes(e.op);
        const operand = this.natural(e.l) ?? this.natural(e.r) ?? (comparison ? null : want);
        if (operand === null) return this.refuse(pos, "an integer literal whose type no context fixes");
        const l = this.expr(e.l, operand).e, r = this.expr(e.r, operand).e;
        const bool: RType = { k: "prim", name: "bool", span: pos };
        switch (e.op) {
          case "==": case "!=":
            if (operand.k !== "prim") return this.refuse(pos, `${e.op} on a struct`);
            return { e: { k: "bin", pos, op: e.op === "==" ? "===" : "!==", l, r }, type: bool };
          case "<": case "<=": case ">": case ">=": {
            if (!isPrim(operand, ["i32", "u32", "i64", "f64", "String", "&str"])) return this.refuse(pos, `${e.op} on ${show(operand)}`);
            const op = ({ "<": "lt", "<=": "le", ">": "gt", ">=": "ge" } as const)[e.op];
            return { e: { k: "arith", pos, op, l, r }, type: bool };
          }
          case "+":
            if (isPrim(operand, strings)) return { e: { k: "arith", pos, op: "add", l, r }, type: { k: "prim", name: "String", span: pos } };
          // falls through
          case "-": case "*":
            if (!isPrim(operand, ["i32", "u32", "i64", "f64"])) return this.refuse(pos, `${e.op} on ${show(operand)}`);
            return { e: { k: "arith", pos, op: e.op === "+" ? "add" : e.op === "-" ? "sub" : "mul", l, r }, type: operand };
          case "/": case "%":
            if (!isPrim(operand, ["i64", "f64"])) return this.refuse(pos, `${e.op} on ${show(operand)} (admitted on i64 and f64)`);
            return { e: { k: "arith", pos, op: e.op === "/" ? "div" : "rem", l, r }, type: operand };
        }
        return this.refuse(pos, `the operator ${e.op}`);
      }
      case "call": {
        const f = this.fns.get(e.callee);
        if (f === undefined) return this.refuse(pos, `a call of ${e.callee}, not a function of the file`);
        if (f.params.length !== e.args.length) return this.refuse(pos, `a call of ${e.callee} with ${e.args.length} arguments`);
        const args = e.args.map((a, i) => this.expr(a, f.params[i]?.type ?? null).e);
        return { e: { k: "apply", pos, callee: { k: "id", pos: [pos[0], pos[0] + e.callee.length], name: e.callee }, args }, type: f.ret };
      }
      case "field": {
        const type = this.natural(e);
        return { e: { k: "read", pos, field: e.name, e: this.expr(e.e, null).e }, type };
      }
      case "toString": {
        const inner = this.expr(e.e, null);
        if (inner.type === null || !isPrim(inner.type, strings)) return this.refuse(pos, "to_string of another type than a string");
        return { e: inner.e, type: this.natural(e) };
      }
      case "structLit": {
        const def = this.structs.get(e.name);
        if (def === undefined) return this.refuse(pos, `the struct ${e.name}, which the file does not declare`);
        const names = e.fields.map((f) => f.name);
        if (names.length !== def.fields.length || new Set(names).size !== names.length || !def.fields.every((f) => names.includes(f.name)))
          return this.refuse(pos, `a literal of ${e.name} not naming each of its fields once`);
        const fields = e.fields.map((f) => {
          const type = def.fields.find((d) => d.name === f.name)?.type ?? null;
          return { name: f.name, e: this.expr(f.e, type).e };
        });
        return { e: { k: "alloc", pos, fields }, type: this.natural(e) };
      }
      case "if": {
        const only = (b: RBlock | null): RExpr | null => (b !== null && b.stmts.length === 0 ? b.tail : null);
        const a = only(e.then), b = only(e.else_);
        if (a === null || b === null) return this.refuse(pos, "an `if` with statements, or without `else`, used as a value");
        const type = this.natural(e) ?? want;
        if (type === null) return this.refuse(pos, "an integer literal whose type no context fixes");
        const cond = this.check(e.cond, { k: "prim", name: "bool", span: e.cond.span });
        return { e: { k: "conditional", pos, cond, then: this.expr(a, type).e, else_: this.expr(b, type).e }, type };
      }
    }
  }
}
