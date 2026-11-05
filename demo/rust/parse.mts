// The demo's Rust parser: a tokenizer and a recursive-descent parser for
// exactly the subset this directory's README states, writing a small Rust
// syntax tree. Spans are UTF-16 offsets of the file, the Fragment's unit.
// Anything outside the subset is refused with its line.

import type { Span } from "../../tools/span.mts";

export type Prim = "i32" | "u32" | "i64" | "f64" | "bool" | "String" | "&str";
export type RType = { k: "prim"; name: Prim; span: Span } | { k: "struct"; name: string; span: Span };

export type IntSuffix = "i32" | "u32" | "i64";
export type BinOp = "+" | "-" | "*" | "/" | "%" | "<" | "<=" | ">" | ">=" | "==" | "!=" | "&&" | "||";
export type RExpr =
  | { k: "int"; digits: string; suffix: IntSuffix | null; span: Span }
  | { k: "float"; text: string; span: Span }
  | { k: "str"; value: string; span: Span }
  | { k: "bool"; value: boolean; span: Span }
  | { k: "path"; name: string; span: Span }
  | { k: "unary"; op: "-" | "!" | "&"; e: RExpr; span: Span }
  | { k: "binary"; op: BinOp; l: RExpr; r: RExpr; span: Span }
  | { k: "call"; callee: string; args: RExpr[]; span: Span }
  | { k: "field"; e: RExpr; name: string; span: Span }
  | { k: "toString"; e: RExpr; span: Span }
  | { k: "structLit"; name: string; fields: { name: string; e: RExpr; span: Span }[]; span: Span }
  | { k: "if"; cond: RExpr; then: RBlock; else_: RBlock | null; span: Span };
export type RStmt =
  | { k: "let"; name: string; nameSpan: Span; type: RType | null; init: RExpr; span: Span }
  | { k: "return"; e: RExpr; span: Span }
  /** An expression statement: `e;`, or a block-like `if` not ending its block. */
  | { k: "expr"; e: RExpr; span: Span };
/** `{ stmts tail? }`: `tail` is a final expression written without `;`. An
 * `else if` is an else block holding only that `if` as its tail. */
export type RBlock = { stmts: RStmt[]; tail: RExpr | null; span: Span };
export type RFn = {
  name: string; nameSpan: Span; params: { name: string; span: Span; type: RType }[];
  ret: RType | null; body: RBlock; exported: boolean; span: Span;
};
export type RStruct = { name: string; fields: { name: string; type: RType; span: Span }[]; span: Span };
export type RCrate = { fns: RFn[]; structs: RStruct[] };

/** A construct outside the subset, with its line. */
export class Unsupported extends Error {}

type Tok = { t: "ident" | "int" | "float" | "str" | "punct" | "eof"; v: string; span: Span; suffix?: string };

const puncts = ["->", "::", "==", "!=", "<=", ">=", "&&", "||", "+", "-", "*", "/", "%", "<", ">", "=", "!", "&",
  "(", ")", "{", "}", "[", "]", ",", ";", ":", ".", "#"];
const escapes: ReadonlyMap<string, string> = new Map([["n", "\n"], ["t", "\t"], ["\\", "\\"], ['"', '"'], ["'", "'"]]);

export function lineOf(source: string, offset: number): number {
  return source.slice(0, offset).split("\n").length;
}

function tokenize(src: string): Tok[] {
  const out: Tok[] = [];
  const fail = (at: number, what: string): never => {
    throw new Unsupported(`unsupported: ${what} at line ${lineOf(src, at)}`);
  };
  let i = 0;
  while (i < src.length) {
    const c = src[i] ?? "";
    if (/\s/.test(c)) { i++; continue; }
    if (src.startsWith("//", i)) { const end = src.indexOf("\n", i); i = end < 0 ? src.length : end; continue; }
    if (src.startsWith("/*", i)) { const end = src.indexOf("*/", i + 2); if (end < 0) fail(i, "an unclosed comment"); i = end + 2; continue; }
    const start = i;
    if (/[A-Za-z_]/.test(c)) {
      while (i < src.length && /[A-Za-z0-9_]/.test(src[i] ?? "")) i++;
      out.push({ t: "ident", v: src.slice(start, i), span: [start, i] });
      continue;
    }
    if (/[0-9]/.test(c)) {
      if (/^0[xob]/.test(src.slice(i, i + 2))) fail(i, "an integer literal in another radix than 10");
      while (i < src.length && /[0-9_]/.test(src[i] ?? "")) i++;
      let float = false;
      if (src[i] === "." && /[0-9]/.test(src[i + 1] ?? "")) { float = true; i++; while (/[0-9_]/.test(src[i] ?? "")) i++; }
      if (/[eE]/.test(src[i] ?? "") && /[-+0-9]/.test(src[i + 1] ?? "")) {
        float = true; i++; if (/[-+]/.test(src[i] ?? "")) i++; while (/[0-9_]/.test(src[i] ?? "")) i++;
      }
      const body = src.slice(start, i).replaceAll("_", "");
      let suffix = "";
      const s0 = i;
      while (i < src.length && /[A-Za-z0-9_]/.test(src[i] ?? "")) i++;
      suffix = src.slice(s0, i);
      if (suffix === "f64") float = true;
      else if (suffix !== "" && (float || !["i32", "u32", "i64"].includes(suffix))) fail(start, `the literal suffix ${suffix}`);
      out.push({ t: float ? "float" : "int", v: body, span: [start, i], suffix });
      continue;
    }
    if (c === '"') {
      i++;
      let value = "";
      while (src[i] !== '"') {
        if (i >= src.length) fail(start, "an unclosed string");
        if (src[i] === "\\") {
          const e = escapes.get(src[i + 1] ?? "");
          if (e === undefined) fail(i, "a string escape other than \\n \\t \\\\ \\\" \\'");
          value += e; i += 2;
        } else { value += src[i]; i++; }
      }
      i++;
      out.push({ t: "str", v: value, span: [start, i] });
      continue;
    }
    const p = puncts.find((q) => src.startsWith(q, i));
    if (p === undefined) fail(i, `the character ${JSON.stringify(c)}`);
    else { i += p.length; out.push({ t: "punct", v: p, span: [start, i] }); }
  }
  out.push({ t: "eof", v: "", span: [src.length, src.length] });
  return out;
}

const prims: ReadonlyMap<string, Prim> = new Map([
  ["i32", "i32"], ["u32", "u32"], ["i64", "i64"], ["f64", "f64"], ["bool", "bool"], ["String", "String"]]);
const keywords = new Set(["fn", "let", "return", "if", "else", "true", "false", "pub", "struct", "mut", "match",
  "while", "for", "loop", "impl", "use", "as", "const", "static", "trait", "enum", "unsafe", "mod"]);

const binaryLevels: BinOp[][] = [["||"], ["&&"], ["==", "!=", "<", "<=", ">", ">="], ["+", "-"], ["*", "/", "%"]];

export class Parser {
  readonly src: string;
  private toks: Tok[];
  private i = 0;
  constructor(src: string) {
    this.src = src;
    this.toks = tokenize(src);
  }

  private peek(k: number = 0): Tok {
    const tok = this.toks[this.i + k] ?? this.toks[this.toks.length - 1];
    if (tok === undefined) throw Error("no tokens");
    return tok;
  }
  private next(): Tok { const tok = this.peek(); this.i++; return tok; }
  private is(v: string, k: number = 0): boolean { const tok = this.peek(k); return (tok.t === "punct" || tok.t === "ident") && tok.v === v; }
  refuse(at: Span | number, what: string): never {
    const start = typeof at === "number" ? at : at[0];
    throw new Unsupported(`unsupported: ${what} at line ${lineOf(this.src, start)}`);
  }
  private expect(v: string): Tok {
    const tok = this.next();
    if (!((tok.t === "punct" || tok.t === "ident") && tok.v === v))
      this.refuse(tok.span, `${JSON.stringify(tok.v || "end of file")} where ${JSON.stringify(v)} was expected`);
    return tok;
  }
  private ident(): Tok {
    const tok = this.next();
    if (tok.t !== "ident" || keywords.has(tok.v)) this.refuse(tok.span, `${JSON.stringify(tok.v)} where a name was expected`);
    return tok;
  }

  crate(): RCrate {
    const fns: RFn[] = [], structs: RStruct[] = [];
    while (this.peek().t !== "eof") {
      if (this.is("use")) {
        // Only `use wasm_bindgen::prelude::*;`.
        const start = this.next().span[0];
        for (const part of ["wasm_bindgen", "::", "prelude", "::", "*", ";"])
          if (!this.is(part)) this.refuse(start, "a `use` other than `use wasm_bindgen::prelude::*;`");
          else this.next();
        continue;
      }
      let exported = false;
      const itemStart = this.peek().span[0];
      if (this.is("#")) {
        this.next();
        this.expect("[");
        const attr = this.next();
        if (attr.v !== "wasm_bindgen" || !this.is("]")) this.refuse(attr.span, "an attribute other than #[wasm_bindgen]");
        this.next();
        exported = true;
      }
      const pub = this.is("pub");
      if (pub) this.next();
      if (exported && !pub) this.refuse(itemStart, "a #[wasm_bindgen] item that is not `pub`");
      if (this.is("fn")) fns.push(this.fn(exported, itemStart));
      else if (this.is("struct") && !exported) structs.push(this.struct(itemStart));
      else this.refuse(this.peek().span, exported ? "a #[wasm_bindgen] item other than a `pub fn`" : `the item ${JSON.stringify(this.peek().v)}`);
    }
    return { fns, structs };
  }

  private type(): RType {
    const tok = this.next();
    if (tok.t === "punct" && tok.v === "&") {
      const inner = this.next();
      if (inner.v !== "str") this.refuse(tok.span, "a reference type other than &str");
      return { k: "prim", name: "&str", span: [tok.span[0], inner.span[1]] };
    }
    if (tok.t !== "ident") return this.refuse(tok.span, `the type ${JSON.stringify(tok.v)}`);
    const prim = prims.get(tok.v);
    if (prim !== undefined) return { k: "prim", name: prim, span: tok.span };
    if (/^[A-Z]/.test(tok.v) && !this.is("<") && !this.is("::")) return { k: "struct", name: tok.v, span: tok.span };
    return this.refuse(tok.span, `the type ${tok.v}`);
  }

  private struct(start: number): RStruct {
    this.expect("struct");
    const name = this.ident().v;
    this.expect("{");
    const fields: RStruct["fields"] = [];
    while (!this.is("}")) {
      if (this.is("pub")) this.next();
      const f = this.ident();
      this.expect(":");
      fields.push({ name: f.v, type: this.type(), span: f.span });
      if (!this.is("}")) this.expect(",");
    }
    const end = this.expect("}").span[1];
    return { name, fields, span: [start, end] };
  }

  private fn(exported: boolean, start: number): RFn {
    this.expect("fn");
    const name = this.ident();
    if (this.is("<")) this.refuse(this.peek().span, "a generic function");
    this.expect("(");
    const params: RFn["params"] = [];
    while (!this.is(")")) {
      if (this.is("mut")) this.refuse(this.peek().span, "a `mut` parameter");
      const p = this.ident();
      this.expect(":");
      params.push({ name: p.v, span: p.span, type: this.type() });
      if (!this.is(")")) this.expect(",");
    }
    this.expect(")");
    let ret: RType | null = null;
    if (this.is("->")) { this.next(); ret = this.type(); }
    const body = this.block();
    return { name: name.v, nameSpan: name.span, params, ret, body, exported, span: [start, body.span[1]] };
  }

  private block(): RBlock {
    const start = this.expect("{").span[0];
    const stmts: RStmt[] = [];
    let tail: RExpr | null = null;
    while (!this.is("}")) {
      const at = this.peek().span[0];
      if (this.is("let")) {
        this.next();
        if (this.is("mut")) this.refuse(this.peek().span, "a `let mut`");
        const name = this.ident();
        let type: RType | null = null;
        if (this.is(":")) { this.next(); type = this.type(); }
        this.expect("=");
        const init = this.expr();
        const end = this.expect(";").span[1];
        stmts.push({ k: "let", name: name.v, nameSpan: name.span, type, init, span: [at, end] });
        continue;
      }
      if (this.is("return")) {
        this.next();
        if (this.is(";")) this.refuse(at, "a `return` without a value");
        const e = this.expr();
        const end = this.expect(";").span[1];
        stmts.push({ k: "return", e, span: [at, end] });
        continue;
      }
      const e = this.expr();
      if (this.is(";")) { const end = this.next().span[1]; stmts.push({ k: "expr", e, span: [at, end] }); continue; }
      if (this.is("}")) { tail = e; break; }
      // A block-like expression needs no `;` to be a statement.
      if (e.k === "if") { stmts.push({ k: "expr", e, span: e.span }); continue; }
      this.refuse(this.peek().span, `${JSON.stringify(this.peek().v)} after an expression`);
    }
    const end = this.expect("}").span[1];
    return { stmts, tail, span: [start, end] };
  }

  expr(level: number = 0): RExpr {
    const ops = binaryLevels[level];
    if (ops === undefined) return this.unary();
    let l = this.expr(level + 1);
    let chained = false;
    for (;;) {
      const tok = this.peek();
      const op = ops.find((o) => tok.t === "punct" && tok.v === o);
      if (op === undefined) return l;
      if (level === 2 && chained) this.refuse(tok.span, "a chained comparison");
      this.next();
      const r = this.expr(level + 1);
      l = { k: "binary", op, l, r, span: [l.span[0], r.span[1]] };
      chained = level === 2;
    }
  }

  private unary(): RExpr {
    const tok = this.peek();
    if (tok.t === "punct" && (tok.v === "-" || tok.v === "!" || tok.v === "&")) {
      this.next();
      if (tok.v === "&" && this.is("mut")) this.refuse(tok.span, "a `&mut` borrow");
      const e = this.unary();
      return { k: "unary", op: tok.v, e, span: [tok.span[0], e.span[1]] };
    }
    return this.postfix(this.primary());
  }

  private postfix(e: RExpr): RExpr {
    for (;;) {
      if (this.is("as")) this.refuse(this.peek().span, "an `as` cast");
      if (!this.is(".")) return e;
      this.next();
      const name = this.next();
      if (name.t !== "ident") this.refuse(name.span, "a tuple field");
      if (this.is("(")) {
        if (name.v !== "to_string") this.refuse(name.span, `the method ${name.v}`);
        this.next();
        const end = this.expect(")").span[1];
        e = { k: "toString", e, span: [e.span[0], end] };
      } else e = { k: "field", e, name: name.v, span: [e.span[0], name.span[1]] };
    }
  }

  private primary(): RExpr {
    const tok = this.next();
    switch (tok.t) {
      case "int": {
        const suffix = tok.suffix === "" || tok.suffix === undefined ? null : tok.suffix;
        if (suffix !== null && suffix !== "i32" && suffix !== "u32" && suffix !== "i64") return this.refuse(tok.span, `the suffix ${suffix}`);
        return { k: "int", digits: tok.v, suffix, span: tok.span };
      }
      case "float": return { k: "float", text: tok.v, span: tok.span };
      case "str": return { k: "str", value: tok.v, span: tok.span };
      case "punct":
        if (tok.v === "(") {
          const e = this.expr();
          if (this.is(",")) this.refuse(this.peek().span, "a tuple");
          this.expect(")");
          return e;
        }
        return this.refuse(tok.span, `${JSON.stringify(tok.v)} where an expression was expected`);
      case "ident": {
        if (tok.v === "true" || tok.v === "false") return { k: "bool", value: tok.v === "true", span: tok.span };
        if (tok.v === "if") return this.ifExpr(tok.span[0]);
        if (keywords.has(tok.v)) return this.refuse(tok.span, `the expression \`${tok.v}\``);
        if (this.is("!")) return this.refuse(tok.span, "a macro");
        if (this.is("::")) return this.refuse(tok.span, "a path");
        if (this.is("(")) {
          this.next();
          const args: RExpr[] = [];
          while (!this.is(")")) { args.push(this.expr()); if (!this.is(")")) this.expect(","); }
          const end = this.expect(")").span[1];
          return { k: "call", callee: tok.v, args, span: [tok.span[0], end] };
        }
        // `S { a: e, … }`; a struct name starts with a capital, as Rust's
        // naming convention has it, which keeps `if x { … }` a condition.
        if (this.is("{") && /^[A-Z]/.test(tok.v)) {
          this.next();
          const fields: { name: string; e: RExpr; span: Span }[] = [];
          while (!this.is("}")) {
            const f = this.ident();
            this.expect(":");
            const e = this.expr();
            fields.push({ name: f.v, e, span: [f.span[0], e.span[1]] });
            if (!this.is("}")) this.expect(",");
          }
          const end = this.expect("}").span[1];
          return { k: "structLit", name: tok.v, fields, span: [tok.span[0], end] };
        }
        return { k: "path", name: tok.v, span: tok.span };
      }
      default:
        return this.refuse(tok.span, "the end of the file where an expression was expected");
    }
  }

  private ifExpr(start: number): RExpr {
    const cond = this.expr();
    const then = this.block();
    let else_: RBlock | null = null;
    if (this.is("else")) {
      this.next();
      if (this.is("if")) {
        const at = this.next().span[0];
        const nested = this.ifExpr(at);
        else_ = { stmts: [], tail: nested, span: nested.span };
      } else else_ = this.block();
    }
    return { k: "if", cond, then, else_, span: [start, (else_ ?? then).span[1]] };
  }
}
