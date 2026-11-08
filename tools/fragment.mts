/** The fragment: the subset of TypeScript this pipeline accepts, written as an
 * abstract syntax tree. Mirrors Fragment.lean, whose decoders read exactly these
 * shapes. They are structural on purpose: this is a wire format, and its field
 * names are the contract. The parser that produces a tree is fragment-parse.mts.
 * Every annotation is a source type term, the language of declaration bodies.
 */
import type { Atom } from "./claim.mts";
import type { DeclarationDocument, IndexFact, PropertyKey, SourceTypeParameter, StatedEffect, TypeTerm } from "./declaration-types.mts";
// span.mts declares the source span every Fragment node carries, the one declaration the claims, the diagnostics and the reports share.
import type { Span } from "./span.mts";
import type { GuardUndefined } from "./host-families.mts";

/** The name an optional chain's body reads its saved receiver by; no source
 * identifier is spelled so (Fragment.lean's `chainName`). */
export const CHAIN = "?.";
/** The name an optional method call's body reads its saved object by, the
 * call's receiver; no source identifier is spelled so (Fragment.lean's
 * `objectName`). */
export const OBJECT = "?.object";
/** The arithmetic a compound assignment may perform: the bitwise operators
 * `&`, `|`, `^`, `<<`, `>>` and `>>>` among them. */
export type ArithOp = "add" | "sub" | "mul" | "div" | "pow" | "rem" | "bitAnd" | "bitOr" | "xor" | "shl" | "shr" | "ushr";
/** Every binary operator on primitive operands: arithmetic, and the
 * relational comparisons `<`, `<=`, `>`, `>=`. */
export type BinaryOp = ArithOp | "lt" | "le" | "gt" | "ge";
/** `-e`, `+e` and `~e`, and `typeof e` as a value, the string naming the
 * operand's shape. */
export type UnaryOp = "neg" | "plus" | "bitNot" | "typeof";
export type TypeofShape = "number" | "string" | "boolean" | "undefined" | "function" | "bigint" | "symbol" | "object";
export type Expr =
  | { k: "id"; pos: Span; name: string }
  /* `this`: the receiver of the nearest enclosing ordinary function. An arrow
     has no receiver of its own, so inside one this is a capture. */
  | { k: "this"; pos: Span }
  | { k: "lit"; pos: Span; lit: Atom }
  | { k: "not"; pos: Span; e: Expr }
  /* `e as T`, `e satisfies T`, `e!` or `e as const`: the operand's value,
     unchanged. The annotation, when there is one, is what the operand must
     meet; `as const` has none, its claim being the operand's literal types. */
  | {
      k: "cast";
      pos: Span;
      cast: "as" | "satisfies" | "nonNull" | "const";
      annot: TypeTerm | null;
      e: Expr;
    }
  /* An object literal: one named field per initializer, in source order. A
     shorthand `{ x }` is `{ x: x }`. */
  /* A class instance's allocation also holds its class's prototype object,
     under the key no source property spells (`proto`); so does a derived
     class's prototype, its base's. A prototype `instanceof` tests owns its
     class's key, which no source property spells either, at `undefined`
     (`brand`, its value claimed at `pos`). A class's private field or
     method `#x` is keyed by its private name's symbol. */
  /* A computed key `[k]: v` (`computed`) is the field `(k satisfies ℓ, v)`,
     its key the one the literal ℓ converts to. */
  | { k: "alloc"; pos: Span; fields: { name: PropertyKey; e: Expr; computed?: true }[]; proto?: Expr;
      brand?: { key: string; pos: Span } }
  /* An object literal with spreads of values: its parts in source order, a
     named field or a spread. Each part is evaluated where written, and a
     spread's operand copied as soon as it is evaluated: its own enumerable
     properties, the later parts' over the earlier ones' (SOURCE-MODEL.md, "Object
     literals"). A spread of an object literal is its fields, in place. */
  | { k: "build"; pos: Span; parts: ({ name: string; e: Expr; spread?: never } | { spread: Expr })[]; proto?: Expr }
  /* A named read: `e.name`, or `e[k]` with `k` a `unique symbol` constant,
     which reads that symbol's key as a type's computed key names it. */
  | { k: "read"; pos: Span; field: PropertyKey; e: Expr }
  /* `e[key]`: evaluate the receiver, then the key. A string singleton names
     one field; a broad string reads through a dictionary view. */
  | { k: "index"; pos: Span; e: Expr; key: Expr }
  /* An array literal: one element per initializer, in source order.
     `spreads` are the indices of the elements written with `...`: each
     stands for the elements of its operand's store, read where it is
     written. */
  | { k: "arrayLit"; pos: Span; elems: Expr[]; spreads?: number[] }
  /* `[a, o.f = d, ...r] = rhs`: the right side once, then each target, a
     mutable local or a field, in turn: its reference (receiver, then key),
     then its position of the store, or its default when that read is
     undefined, written to it; the rest's target takes the fresh array of the
     positions from its index on, claimed at the rest's span; a `slice` rest, which TypeScript
     types as no one tuple of required positions, is collected by
     `%RestFrom:k%` (`intrinsics.mts`). The expression's value is the right
     side. */
  | { k: "arrayAssign"; pos: Span; targets: ArrayElemAst[];
      rest: { index: number; pos: Span; target: Expr; slice: boolean } | null; rhs: Expr }
  | { k: "indexWrite"; pos: Span; receiver: Expr; key: Expr; rhs: Expr }
  | { k: "bin"; pos: Span; op: string; l: Expr; r: Expr }
  /* A binary operator on primitive operands: `l`, then `r`, then the
     operation, as JavaScript performs it on two numbers, two bigints or, for
     a comparison, two strings or a number and a bigint. */
  | { k: "arith"; pos: Span; op: BinaryOp; l: Expr; r: Expr }
  /* A unary numeric operator on the operand's value, or `typeof`. */
  | { k: "unary"; pos: Span; op: UnaryOp; e: Expr }
  /* `target op= rhs`, `target++` and the like: the target's parts are
     evaluated once, its current value read, the right side (1 for an
     increment) evaluated, the operation applied and the result written back.
     `post` selects the old value as the expression's value. */
  | {
      k: "update";
      pos: Span;
      op: ArithOp;
      target: Expr;
      rhs: Expr | null;
      post: boolean;
    }
  | { k: "coalesce"; pos: Span; left: Expr; right: Expr }
  /* An optional chain, `r?.b`, `r?.[k]`, `r?.(a)`, with the links after it:
     the receiver once, then `undefined` where it is null or undefined, else
     `body`, which reads the receiver's value as the variable `CHAIN`, spelled
     at `at`, the `?.` token. */
  | { k: "optional"; pos: Span; at: Span; receiver: Expr; body: Expr }
  /* `o.m?.(a)`'s object, or `o.m!(a)`'s: `object` once, then `body`, which
     reads its value as the variable `OBJECT`, first spelled at `at`, the
     method's name (an element's closing `]`). */
  | { k: "withObject"; pos: Span; at: Span; object: Expr; body: Expr }
  /* `left, right`: the left operand for its effects, then the right one's
     value. `void e` is `e, undefined`. */
  | { k: "comma"; pos: Span; left: Expr; right: Expr }
  /* A family guard's call (HOST-FAMILIES.md, "A guard on any argument"):
     its argument, evaluated once, within the guard's domain, then whether
     its value, or its object's `field`, is one of the tags, each tested in
     turn. */
  | { k: "tagMember"; pos: Span; domain: TypeTerm; field: string | null; tags: Atom[]; onUndefined: GuardUndefined; e: Expr }
  | { k: "write"; pos: Span; field: PropertyKey; receiver: Expr; rhs: Expr }
  /* `target ??= rhs`, `||=` or `&&=` on a field, an element or, for the
     Boolean forms, a name: the target's parts once, its value read, the test
     on that value, and the right side written only on the writing arm. */
  | {
      k: "logicalAssign";
      pos: Span;
      op: "nullish" | "or" | "and";
      target: Expr;
      rhs: Expr;
    }
  /* A nullish assignment also reads the target at namePos. */
  | { k: "nullishAssign"; pos: Span; name: string; namePos: Span; rhs: Expr }
  /* Assignment to a mutable local. An expression, because JavaScript's is:
     it yields the value written, which the calculus's write does not. */
  | { k: "assign"; pos: Span; name: string; namePos: Span; rhs: Expr }
  | {
      k: "withValue";
      pos: Span;
      fn: Expr;
      initial: Expr;
      functionType: TypeTerm;
      bagType: TypeTerm;
    }
  /* `Object.assign(target, ...sources)` other than the callable form: the
     target, then each source, each copied onto the target as it is
     evaluated; the value is the target. */
  | { k: "objectAssign"; pos: Span; target: Expr; sources: Expr[] }
  /* `typeof e === "…"` (or `!==`, operands in either order): a test of the
     operand's shape. `"object"` holds of null and of an object without call
     code; a callable object, a class included, is `"function"`. */
  | { k: "typeofTest"; pos: Span; shape: TypeofShape; equal: boolean; e: Expr }
  /* `Array.isArray(e)`, the standard library's through its reviewed overlay
     entry: a test of whether the operand is an array. */
  | { k: "arrayTest"; pos: Span; e: Expr }
  /* `key in e`: the key, then the operand, then whether the operand has the
     key, its own or an inherited one. */
  | { k: "inTest"; pos: Span; key: Expr; e: Expr }
  /* `e instanceof C`, `C` a class of the file: the operand, then a read of
     the class's prototype object (`proto`), then whether the operand's
     prototype chain has the key only that object owns (`key`). */
  | { k: "instanceTest"; pos: Span; e: Expr; proto: Expr; key: string }
  /* `spreads` are the indices of the arguments written with `...`: each
     stands for the elements of its operand, read where it is written. `await
     e` and an async body's returns are written as calls of intrinsics
     (`intrinsics.mts`), whose names no source identifier spells. `typeArgs`,
     when written, state the callee's instance. */
  | { k: "apply"; pos: Span; callee: Expr; args: Expr[]; spreads?: number[]; typeArgs?: TypeTerm[] }
  /* `new callee(args)`: the callee, then the arguments left to right, then
     the callee's construct-only code runs. A plain function cannot be one.
     `spreads` marks tuple operands whose required elements supply actuals.
     `typeArgs`, when written, are the explicit type arguments: the
     instantiation the producer proposes, which Lean checks as any other. */
  | { k: "new"; pos: Span; callee: Expr; args: Expr[]; spreads?: number[]; typeArgs?: TypeTerm[] }
  /* A class value: its constructor lambda as construct-only code, which only
     `new` runs. */
  /* A generic class's binders, when it has any: they are in scope in its
     members, and Lean reads them as parameter rows of the declaring unit. */
  /* A class value: its constructor, and its static fields, each the
   * binding its initializer bound, in member order, left out when it has none. */
  | { k: "ctor"; pos: Span; typeParams?: TypeParamAst[]; lambda: Expr; statics?: { name: PropertyKey; e: Expr }[] }
  /* A call through a property reference, `o.m(a)` or `o[k](a)`, parentheses
     around the reference included: the object is saved, the method read from
     it and saved, the arguments evaluated, and the saved method invoked with
     the saved object as its receiver. `callee` is the `read` or `index`. */
  /* `typeArgs`, when written, instantiate the method's leading binders. */
  | { k: "invoke"; pos: Span; callee: Expr; args: Expr[]; spreads?: number[]; typeArgs?: TypeTerm[] }
  /* `f.apply(r, list)`: the target, the receiver and the list are evaluated
     and saved, then the list's length and each indexed element are read in
     order, then the target is invoked with the receiver and those actuals. A
     missing, null or undefined list gives no actuals when `requiredList` is false.
     Reflect.apply sets it true: lowering requires an array list. */
  | {
      k: "applyWithReceiver";
      pos: Span;
      callee: Expr;
      receiver: Expr;
      list: Expr | null;
      requiredList: boolean;
    }
  | {
      k: "callWithReceiver" | "bindWithReceiver";
      pos: Span;
      callee: Expr;
      receiver: Expr;
      args: Expr[];
    }
  | { k: "conditional"; pos: Span; cond: Expr; then: Expr; else_: Expr }
  | {
      k: "lambda";
      pos: Span;
      typeParams: TypeParamAst[];
      /* `type` is what the body reads. A parameter with a `default` also
         admits `undefined` where the closure is called: that is the value a
         short call binds, and the default replaces it before the body runs.
         A block body has no defaults: its parameters are lowered as a
         function's. A `rest` parameter's type is the array its arguments are
         collected into: a tuple, whose required elements are positions of
         the signature, or a `T[]`, which collects any number of them. */
      params: LambdaParamAst[];
      /* An arrow has none. An ordinary function expression binds the
         receiver of each call: `type` is its `this` annotation, `unknown`
         where it states none, and `strict` records that the code is strict
         (a module or a "use strict" directive), which the receiver rule
         assumes. */
      receiver: { type: TypeTerm; strict: boolean } | null;
      /* The result annotation; null where the source states none, and the
         producer's claim at the closure proposes the result instead. */
      result: TypeTerm | null;
      /* A guard's promise, where the result annotation is `x is T` or
         `asserts x is T`; `result` is then its plain result. */
      guard: Guard | null;
      /* The effect its result annotation states, `Within<F, T>`, of which
         `result` is `T`; null where it states none. */
      stated: StatedEffect | null;
      /* How a call of it completes: its own `async` modifier. */
      completion: Completion;
      body: Expr;
    }
  /* A closure's body written as statements: a block, or an expression body
     whose parameters are patterns. It is a function body, and lowered as
     one: a parameter written as a pattern or with a default is a hidden
     name the body's first statements destructure, and a body that can
     complete returns `undefined` at its closing brace. A class value's
     constructor is one too, ending in the `return` of its instance. Only a
     lambda's body is one. */
  | { k: "blockBody"; pos: Span; body: Stmt[] };

/** A loop invariant (`@invariant C` before a loop; PROGRAM-TYPING.md, "Loop
 * invariants"): the clause's index facts at positions naming the bindings
 * `names` holds, in scope at the loop's head, where every entry to the head
 * establishes them. */
export type LoopInvariant = { names: string[]; facts: IndexFact[] };
export type Stmt =
  | { k: "effect"; pos: Span; e: Expr }
  | { k: "return"; pos: Span; e: Expr }
  /* A `break` leaves the nearest enclosing loop or, with a label, the
     enclosing block of that label. */
  | { k: "break"; pos: Span; label: string | null }
  | { k: "continue"; pos: Span }
  /* `while (cond) body`, and the loop of `for (…; cond; update) body`: the
     head tests `cond`; the end of `body` and every `continue` targeting the
     loop run `update` and return to the head. A `while` has no update. */
  | { k: "while"; pos: Span; cond: Expr; body: Stmt[]; update: Stmt[]; invariant: LoopInvariant | null }
  /* `{ body }`: its statements in a lexical scope of their own, and no entry
     of their own (the first statement's is the block's). A labeled block is
     where a `break` of its label goes; a lowered `switch` is made of them. */
  | { k: "block"; pos: Span; label: string | null; body: Stmt[] }
  /* `for (const name of iterable) body`, over an array: the iterable once,
     then one run of the body per element, bound to `name`. */
  /** `iterate` is the iteration intrinsic stepping the iterable's iterator
   * (`intrinsics.mts`), which the parser picks by TypeScript's type of it. */
  | { k: "forOf"; pos: Span; name: string; namePos: Span; iterate: string; iterable: Expr; body: Stmt[] }
  /* The body of a `for...of` loop over an iterable the program defines, the
     last statement of its loop: `close` (IteratorClose) runs where `body` is
     left otherwise than by completing or by a `continue` of the loop: before
     a `break` of the loop leaves it, before a `return` returns, and, its own
     throws discarded, before a throw out of `body` resumes. */
  | { k: "closing"; pos: Span; close: Stmt[]; body: Stmt[] }
  | { k: "if"; pos: Span; cond: Expr; then: Stmt[]; else_: Stmt[] | null }
  /* `throw e`: `e`, then a throw of its value, which leaves the function
     unless an enclosing `try` catches it. */
  | { k: "throw"; pos: Span; e: Expr }
  /* `try { body } catch (param) { handler.body } finally { finalizer }`. A
     throw in the body goes to the handler, whose `param` binds the thrown
     value, `unknown`; the finalizer runs on every way out of the body and the
     handler, then that way out resumes. */
  | {
      k: "try";
      pos: Span;
      body: Stmt[];
      handler: { param: { name: string; namePos: Span } | null; body: Stmt[] } | null;
      finalizer: Stmt[] | null;
    }
  /* A declaration statement binds one or more names, left to right, each
     initializer seeing the earlier bindings. The statement is the entry; the
     producer states no cut between its declarators. */
  | { k: "const"; pos: Span; bindings: BindingAst[] }
  /* Mutable locals. A binding's `annot` is the storage contract every
     assignment is checked against. Absent, the producer supplies one and the
     adapter checks it; an initializer's type is what the binding happens to
     hold first, not what it may hold, so it is never taken for the contract. */
  | { k: "let"; pos: Span; bindings: BindingAst[] }
  /* A pattern on a `const`, `const target = init`: the initializer once,
     then the target binds it, `default_` (a parameter's) replacing it where
     it is undefined. A parameter pattern or default is one over the
     parameter's hidden name (`parameterName`), first in the body. Every
     binding is an immutable local. */
  | { k: "destructure"; pos: Span; target: PatternAst; default_: Expr | null; init: Expr };

/** What a pattern binds at one place: a name, or a nested pattern over the
 * value found there. An object pattern reads its fields in order; an array
 * pattern reads its positions in order (a hole is a position no element
 * names), and its rest, at the position after its elements, collects the
 * positions from there on into a fresh array, claimed at the rest's span like
 * an array literal: a `slice` rest by a call of `%RestFrom:k%`, `k` its
 * index (`intrinsics.mts`). An element's default replaces a read that is
 * undefined. */
export type PatternAst =
  | { k: "name"; name: string; pos: Span }
  /* An object pattern's rest copies the source's other own enumerable
     properties onto a fresh object, claimed at the rest's span. */
  | { k: "object"; pos: Span; props: PatternPropAst[]; rest: { pos: Span; target: PatternAst } | null }
  | { k: "array"; pos: Span; elems: PatternElemAst[];
      rest: { index: number; pos: Span; target: PatternAst; slice: boolean } | null };

/** One property of an object pattern: `field: target = default_`. */
export interface PatternPropAst {
  field: string;
  target: PatternAst;
  default_: Expr | null;
}

/** One element of an array pattern: position `index` binds `target`. */
export interface PatternElemAst {
  index: number;
  target: PatternAst;
  default_: Expr | null;
}

/** One element of an array assignment: position `index` assigns its target,
 * a mutable local (`id`) or a field (`read`, `index`), whose reference (the
 * receiver, then the key) is evaluated before the position is read. */
export interface ArrayElemAst {
  index: number;
  target: Expr;
  default_: Expr | null;
}

/** One declarator of a `const` or `let` statement. */
export interface BindingAst {
  name: string;
  namePos: Span;
  annot: TypeTerm | null;
  init: Expr;
  /** Whether the binding is early (SOURCE-ELABORATION.md, "Lexical bindings before
   * initialization"): a mention of it may run before its initialization, so
   * it is a cell allocated where its block is entered, every mention a
   * checked access. */
  early: boolean;
}

export type TypeParamAst = SourceTypeParameter<TypeTerm>;

/** A user-defined guard's promise, its result annotation `x is T` (a type
 * guard) or `asserts x is T` (an assertion function): the parameter `x`, by
 * its position among the call's actuals, and `T`. The function's type carries
 * it as a promise signature beside its plain one (`CallEffect`). */
export interface Guard {
  param: number;
  asserts: boolean;
  type: TypeTerm;
  span: Span;
}

/** How a call of a callable definition completes, read from the
 * definition's own `async` modifier: `sync`, the body's normal return and
 * throw are the call's; `async`, the call returns a promise, which the body's
 * throw rejects (SOURCE-CONTRACTS.md, "Async functions and await"). */
export type Completion = "sync" | "async";

/** A closure's parameter: its fragment name, its contract, the default
 * replacing an omitted argument, and whether it collects the rest. */
export type LambdaParamAst = { name: string; type: TypeTerm; default?: Expr; rest?: true };

/** A function declaration's parameter: its fragment name, where it is
 * written, its contract, and whether it collects the rest. */
export type FunctionParamAst = { name: string; pos: Span; type: TypeTerm; rest?: true };

export interface FunctionAst {
  name: string;
  namePos: Span;
  typeParams: TypeParamAst[];
  params: FunctionParamAst[];
  /** The result annotation: a guard's plain result, `boolean` or `void`. */
  retType: TypeTerm;
  guard: Guard | null;
  /** The effect the result annotation states, `Within<F, T>`, of which
   * `retType` is `T`; null where it states none. */
  stated: StatedEffect | null;
  /** The written precondition, its `@requires` clauses elaborated to index
   * facts at the call's positions: 0 the receiver, i + 1 the i-th actual
   * (`bound-annotations.mts`; PROGRAM-TYPING.md, "Preconditions"). */
  requires: IndexFact[];
  /** The facts it states of its result, index facts at position 0: the
   * invariants of the record types its result's type names
   * (`bound-annotations.mts`; PROGRAM-TYPING.md, "Type invariants"). */
  ensures: IndexFact[];
  completion: Completion;
  body: Stmt[];
  /** Whether the function's code is strict: a sloppy call converts a
   * receiver that is not an object. */
  strict: boolean;
}

/** A program module the checked file imports a function from, directly or
 * through another such module, lowered as a run of that file alone lowers it:
 * its artifact (`location`, the module identity its declarations carry, and
 * the sha256 of the exact bytes lowered), its declarations, top-level code
 * and functions, and each function it could not lower, with the reason. */
export interface ModuleAst {
  location: string;
  sourceSha256: string;
  declarations: DeclarationDocument;
  init: Stmt[];
  functions: FunctionAst[];
  absent: { name: string; namePos: Span; reason: string }[];
}
export interface Ast {
  file: string;
  sourceSha256: string;
  /** Resolved, fingerprinted source declarations. Lean refuses nonempty
   * closures until their graph interpretation joins the certified plan. */
  declarations: DeclarationDocument;
  /* The module's top-level code in source order: constant bindings and
     expression statements, run once after the function declarations exist. */
  init: Stmt[];
  functions: FunctionAst[];
  /** The program modules certified imports may read, each once. */
  modules: ModuleAst[];
  /** The names that code the lowering leaves out (a census's omitted
   * functions and statements) mentions: the module's own objects are decided
   * over every mention, so a module binding named here is none. */
  omittedMentions: string[];
}
