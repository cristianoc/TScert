/* Part of the trusted front end (fragment-parse.mts): Enums and classes: how the gate reads an enum declaration and lowers a class to the fragment.
 * Each function is a method of the gate: `Gate` holds it as a field, so a call
 * reads `this.name(...)`; its body names the gate `gate`, typed, which lets a
 * call that never returns (`gate.fail`) narrow what follows. */
import * as ts from "typescript/unstable/ast";
import type { ClassDeclaration, Expression, MethodDeclaration, Node, Statement } from "typescript/unstable/ast";
import type { DeclarationIdentity, PropertyKey, TypeTerm } from "./declaration-types.mts";
import { CLASS_ACCESS, classMemberRefusal, oneTerm, signature } from "./type-term.mts";
import type { BindingAst, Expr, Stmt, TypeParamAst } from "./fragment.mts";
import type { Span } from "./span.mts";
import { childrenOf, isStatic, nameOf } from "./syntax.mts";
import { enumIntrinsicName, enumMembersTerm, literalTerm } from "./intrinsics.mts";
import { type ClassRecord, type EnumMember, FORGED_PROMISE, GENERATOR, HAS_INSTANCE, PRIVATE_INHERITANCE, baseName, classKey, completes, conditionParen, enumMemberName, firstOptional, freshName, literalExpr, parameterName, prototypeName, selfConstructs, selfName, staticName, unnamedMember } from "./fragment-support.mts";
import type { Gate } from "./fragment-parse.mts";

/** A class declaration, in module initialization order: one constant per
 * method, holding a closure allocated once, whose receiver is the instance,
 * as every instance shares its prototype's method; then the class, holding
 * its constructor, which allocates an instance from the field initializers
 * and those methods. Within the fragment an instance's own fields and its
 * prototype's methods are indistinguishable. The class value is that
 * constructor as construct-only code: `new` runs it, a plain call cannot. */
/** An enum's members, in order, with the values the declaration graph
 * reported: `null` for a member TypeScript computes no value for, whose
 * value is known only at run time (a number, as TypeScript requires). */
export function enumMembers(this: Gate, name: string): EnumMember[] {
  const gate: Gate = this;
  const info = gate.enums.get(name);
  if (!info) return gate.fail(null, `enum ${name} missing`);
  return info.members.map((m) => {
    const value = m.value;
    // TypeScript's emit writes each member by assignment, which for
    // `__proto__` runs the prototype's setter and creates no property.
    if (m.name === "__proto__")
      return gate.fail(m.node, "an enum member named __proto__: its assignment runs the prototype's setter, which creates no property");
    if (value === undefined) return { ...m, value: null };
    if (typeof value === "number" && !Number.isFinite(value))
      return gate.fail(m.node, "an enum member that is NaN or infinite has no literal type");
    return { ...m, value };
  });
}

/** Whether an enum's object has keys its declaration does not name: an
 * ambient enum's, the environment's, or one with a member whose value,
 * and so whose reverse mapping's key, is known only at run time. */
export function enumOpen(this: Gate, name: string): boolean {
  const gate: Gate = this;
  return !!gate.enums.get(name)?.ambient || gate.enumMembers(name).some((m) => m.value === null);
}

/** The type an enum's value has: its object, each member a readonly field
 * at its literal, and, for a numeric member, the reverse mapping from the
 * value's property key to the member's name, the last member with that
 * value winning (`enumEntries`). An open enum's object (`enumOpen`) states
 * its members only, one known only at run time at `number`
 * (`enumMembersTerm`). */
export function enumObjectTerm(this: Gate, name: string, span: Span): TypeTerm {
  const gate: Gate = this;
  if (gate.enumOpen(name))
    return enumMembersTerm(gate.enumMembers(name).map((m) => ({ name: m.name, value: m.value ?? undefined })), span);
  return {
    k: "object",
    fields: gate.enumEntries(name).map((e) => ({ name: e.key, optional: false, readonly: true,
      type: literalTerm(e.value, span), span })),
    stringIndex: null,
    calls: [],
    span,
  };
}

/** The type `E`: the union of its members' literal types, `number` for a
 * member whose value is known only at run time; `never` for an enum
 * without members. */
export function enumTerm(this: Gate, name: string, span: Span): TypeTerm {
  const gate: Gate = this;
  const parts = gate.enumMembers(name).map((m): TypeTerm =>
    m.value === null ? { k: "atom", name: "number", span } : literalTerm(m.value, span));
  return parts.length ? { k: "union", parts, span } : { k: "atom", name: "never", span };
}

/** The own properties of an enum's object, in JavaScript's order: array
 * index keys ascending, then the others in the order they were created.
 * TypeScript's emit creates each member's property, then, for a numeric
 * member, the property named by its value's `ToString`; a later member
 * with the same value writes that property again, which keeps its place.
 * Each entry's value has a claim site of its own: a member's at its
 * initializer, or at its name where it has none, and a reverse entry's
 * from the member to the end of the declaration. */
export function enumEntries(this: Gate, name: string): { key: string; value: string | number; pos: Span }[] {
  const gate: Gate = this;
  const entries = new Map<string, { key: string; value: string | number; pos: Span }>();
  const members = gate.enumMembers(name);
  const end = gate.enums.get(name)?.end ?? 0;
  const names = new Set(members.map((m) => m.name));
  for (const m of members) {
    if (m.value === null) return gate.fail(m.node, `enum ${name} has a member known only at run time`);
    entries.set(m.name, { key: m.name, value: m.value, pos: m.init ?? m.nameSpan });
    if (typeof m.value !== "number") continue;
    const key = String(m.value);
    if (names.has(key))
      gate.fail(m.node, "an enum member's reverse mapping would replace a member of the same name");
    entries.set(key, { key, value: m.name, pos: [m.span[0], end] });
  }
  const index = (k: string) => /^(0|[1-9][0-9]*)$/.test(k) && Number(k) < 4294967295;
  const all = [...entries.values()];
  return [
    ...all.filter((e) => index(e.key)).sort((a, b) => Number(a.key) - Number(b.key)),
    ...all.filter((e) => !index(e.key)),
  ];
}

/** `enum E { … }` is the module constant `E`, bound to a fresh object whose
 * properties TypeScript's emit creates (`enumEntries`), each at a literal,
 * at the object type `enumObjectTerm`: the constant a function reading `E`
 * sees, never written, since every field is readonly.
 *
 * An enum with a member whose value is known only at run time is, first,
 * one constant `%E.M%: number` per such member, in order, bound to its
 * initializer, where a read of a member of `E` (`enumMemberReads`) is that
 * member's constant, or its value where TypeScript computes one; then `E`,
 * bound to `%Enum:E%` (`intrinsics.mts`) of the fresh object of its
 * members, which adds the reverse mapping at keys known only at run time.
 * JavaScript evaluates the initializers in the same order, writing each
 * member's property and its reverse entry between them, which only a read
 * of `E` could observe: one in an initializer is refused, and a call that
 * could read `E` before it is bound is refused by the initialization
 * order check. */
export function enumStmt(this: Gate, node: ts.EnumDeclaration): Stmt[] {
  const gate: Gate = this;
  const name = node.name.text;
  const members = gate.enumMembers(name);
  if (members.some((m) => m.value === null)) {
    // A member named by a canonical numeric string, which TypeScript
    // admits for `NaN` and `Infinity` only, may be replaced by the reverse
    // entry of a value known only at run time.
    for (const m of members)
      if (String(Number(m.name)) === m.name)
        gate.fail(m.node, "an enum member named NaN or Infinity beside a member known only at run time: that member's reverse mapping may replace it");
    const stmts: Stmt[] = [];
    members.forEach((m, index) => {
      const init = m.node.initializer;
      if (m.value !== null) return;
      if (!init) return gate.fail(m.node, "an enum member known only at run time needs an initializer");
      gate.enumInit = { name, members, index };
      try {
        stmts.push({ k: "const", pos: m.span, bindings: [{ name: enumMemberName(name, m.name), namePos: m.nameSpan,
          annot: { k: "atom", name: "number", span: m.nameSpan }, init: gate.expr(init) }] });
      } finally {
        gate.enumInit = null;
      }
    });
    // The call is at the declaration from its name, the intrinsic read at
    // the name, the object at the braces, and a member's field at the
    // member, or, holding its value, at its initializer.
    const at: Span = [node.name.getStart(gate.file), node.end];
    const brace: Span = [gate.file.text.indexOf("{", node.name.end), node.end];
    stmts.push({ k: "const", pos: gate.span(node), bindings: [{ name, namePos: gate.span(node.name),
      annot: gate.enumObjectTerm(name, gate.span(node.name)),
      init: gate.intrinsic(enumIntrinsicName(name), at, gate.span(node.name), [{ k: "alloc", pos: brace,
        fields: members.map((m) => ({ name: m.name,
          e: m.value === null ? { k: "id", pos: m.span, name: enumMemberName(name, m.name) }
            : literalExpr(m.value, m.init ?? m.nameSpan) })) }]) }] });
    return stmts;
  }
  const entries = gate.enumEntries(name);
  if (!entries.length)
    gate.fail(node, "an enum without members allocates an object with no property, which the heap model has no record for");
  const at: Span = [node.name.getStart(gate.file), node.end];
  return [{
    k: "const",
    pos: gate.span(node),
    bindings: [{
      name,
      namePos: gate.span(node.name),
      annot: gate.enumObjectTerm(name, gate.span(node.name)),
      init: {
        k: "alloc",
        pos: at,
        fields: entries.map((e) => ({ name: e.key, e: literalExpr(e.value, e.pos) })),
      },
    }],
  }];
}

/** A read in `enumInit`'s initializer: of a member of its enum
 * (`enumMemberReads`), the member's constant or value, refused for a
 * member not yet initialized; any other read of the enum is of an object
 * not yet built. */
export function enumRead(this: Gate, node: Expression): Expr | null {
  const gate: Gate = this;
  const current = gate.enumInit;
  if (!current) return null;
  const member = gate.enumMemberReads.get(gate.span(node).join(":"));
  if (member !== undefined) {
    const index = current.members.findIndex((m) => m.span.join(":") === member);
    const read = current.members[index];
    if (!read || index >= current.index)
      return gate.fail(node, "an enum member initializer reading a member not yet initialized: JavaScript reads undefined there");
    return read.value === null ? { k: "id", pos: gate.span(node), name: enumMemberName(current.name, read.name) }
      : literalExpr(read.value, gate.span(node));
  }
  if (ts.isIdentifier(node) && gate.local(node) === current.name)
    return gate.fail(node, "an enum member initializer reading its enum: its object is not yet built");
  return null;
}

export function classStmt(this: Gate, node: ClassDeclaration): Stmt {
  const gate: Gate = this;
  const name = node.name;
  if (!name) return gate.fail(node, "an anonymous class is outside the fragment");
  // A class extending another reads what that class's lowering recorded:
  // one declared earlier in the file. A class value from elsewhere, an
  // ambient or library class (`Array` included) and an expression are
  // outside the fragment: nothing here says what their constructors
  // allocate. Generic classes take no part in inheritance yet.
  const heritage = node.heritageClauses?.find((c) => c.token === ts.SyntaxKind.ExtendsKeyword);
  let base: ClassRecord | null = null;
  if (heritage) {
    const t = heritage.types[0];
    if (heritage.types.length !== 1 || !t || !ts.isIdentifier(t.expression))
      gate.fail(heritage, "a class extends one class, by its name");
    base = gate.classRecords.get(t.expression.text) ?? null;
    if (!base)
      gate.fail(t, "a class extends a class declared earlier in the file; one from a library, an ambient declaration or a value is outside the fragment");
    // A generic class's binders are the declaring unit's parameter rows,
    // one per spelling: a derived class extends a generic base at the
    // base's own binders, which it declares too, so the base's
    // construction and members are at the same rows. A base at other type
    // arguments would need its construction instantiated there.
    const own = (node.typeParameters ?? []).map((tp) => tp.name.text);
    const args = t.typeArguments ?? [];
    if (base.binders.length || args.length) {
      const binders = base.binders;
      const atOwn = args.length === binders.length && args.every((a, i) =>
        ts.isTypeReferenceNode(a) && ts.isIdentifier(a.typeName) && !a.typeArguments?.length &&
        a.typeName.text === binders[i] && own.includes(a.typeName.text));
      if (!atOwn)
        gate.fail(heritage, "a class extending a generic class other than at the base's own binders, which the derived class declares, is outside the fragment: the base's construction is at those binders' rows");
    }
  }
  const extended = gate.file.statements.some((st) => ts.isClassDeclaration(st) &&
    !!st.heritageClauses?.some((c) => c.token === ts.SyntaxKind.ExtendsKeyword &&
      c.types.some((t) => ts.isIdentifier(t.expression) && t.expression.text === name.text)));
  if (node.modifiers?.some((m) => m.kind !== ts.SyntaxKind.ExportKeyword))
    gate.fail(node, "a class modifier outside the fragment");
  const declared = gate.declaredTypes.get(name.text);
  if (!declared) return gate.fail(node, "a class declaration has no instance type");
  // A generic class's binders are in scope in its members; its instance
  // type is the class applied to them. Lean reads them as parameter rows of
  // the code unit that declares the class.
  const typeParams = gate.enterTypeParams(node.typeParameters);
  try {
    return gate.classBody(node, name, declared.declaration, typeParams, heritage, base, extended);
  } finally {
    gate.leaveTypeParams();
  }
}

export function classBody(this: Gate, node: ClassDeclaration, name: ts.Identifier, declaration: DeclarationIdentity,
    typeParams: TypeParamAst[], heritage: ts.HeritageClause | undefined, base: ClassRecord | null,
    extended: boolean): Stmt {
  const gate: Gate = this;
  const binders = node.typeParameters ?? [];
  const instance: TypeTerm = { k: "reference", reference: { name: name.text, span: gate.span(name),
    arguments: binders.map((tp) => gate.span(tp.name)), target: declaration },
    args: binders.map((tp) => ({ k: "binder", name: tp.name.text, span: gate.span(tp.name) })),
    span: gate.span(name) };
  const outerStrict = gate.strict;
  const outerSuper = gate.superClass;
  const outerSelf = gate.selfClass;
  // A class body is strict code; `super.m(...)` in its methods calls its
  // base's method. Its instance members read its own name as its class
  // binding; its static members, lowered after the class value is bound,
  // read that binding directly.
  gate.strict = true;
  gate.superClass = base;
  const instanceMembers = { name: name.text, generic: binders.length > 0 };
  gate.selfClass = instanceMembers;
  try {
    const methods: BindingAst[] = [];
    // A prototype is shared by every class instantiation. Its method
    // closures quantify the class parameters within their own contracts.
    const method = (member: MethodDeclaration, key: PropertyKey): Expr => {
      // Methods with their own binders require partial instantiation and
      // retain unit-scoped class binders.
      if (!typeParams.length || member.typeParameters?.length)
        return gate.lambda(member, instance, key);
      const parameters = gate.enterTypeParams(node.typeParameters,
        (_tp, index) => `${name.text}.${JSON.stringify(key)}#class${index}`);
      try {
        const receiver: TypeTerm = { ...instance,
          args: parameters.map((p, i) => ({ k: "binder", name: p.name,
            span: gate.span(binders[i].name) })) };
        const closure = gate.lambda(member, receiver, key);
        if (closure.k !== "lambda") throw new Error("a method lowers to a closure");
        return { ...closure, typeParams: [...parameters, ...closure.typeParams] };
      } finally {
        gate.leaveTypeParams();
      }
    };
    if ((base || extended) && node.members.some((m) => {
      const memberName = nameOf(m);
      return !!memberName && ts.isPrivateIdentifier(memberName);
    }))
      gate.fail(node, PRIVATE_INHERITANCE);
    // The methods its prototype holds: its base's, then its own over them.
    const methodBindings = new Map<string, string>(base?.methods ?? []);
    // The instance's own values, in the order JavaScript evaluates them:
    // field initializers and methods, parameter properties, then the
    // constructor's assignments. `bind` is where an evaluated value is
    // bound before a later constructor statement runs, at its field's type.
    type Field = { name: PropertyKey; text: string; e: Expr; bind: { pos: Span; type: TypeTerm } | null };
    const fields: Field[] = [];
    const constructors = node.members.filter(ts.isConstructorDeclaration);
    const constructor = constructors[0];
    if (constructors.length > 1) gate.fail(node, "a class has one constructor");
    // Fields without an initializer hold `undefined` when the instance is
    // created (JavaScript's class fields); a constructor may assign each
    // once, as a `this.f = e` statement of its own block whose value does
    // not read `this`. Nothing else in the constructor reads `this`, so the
    // instance is complete before anything can observe it, and it is
    // allocated with its final values. Whether a field left `undefined`
    // meets its type (`x!: T` promises TypeScript it does) is Lean's check
    // of that allocation.
    const uninitialized = new Map<string, { type: TypeTerm; pos: Span; key: PropertyKey }>();
    const readsThis = (n: Node): boolean =>
      n.kind === ts.SyntaxKind.ThisKeyword ||
      (!ts.isFunctionExpression(n) && !ts.isFunctionDeclaration(n) && !!n.forEachChild((c) => readsThis(c) || undefined));
    // In a static member, `super` is the base's constructor, whose statics
    // are bindings of their own, not the prototype `super.m(...)` reads.
    const readsSuper = (n: Node): boolean =>
      n.kind === ts.SyntaxKind.SuperKeyword ||
      (!ts.isFunctionExpression(n) && !ts.isFunctionDeclaration(n) && !ts.isClassDeclaration(n) && !ts.isClassExpression(n) &&
        !!n.forEachChild((c) => readsSuper(c) || undefined));
    const STATIC_SUPER = "`super` in a static member is outside the fragment: it is the base's class value, which the derived class value does not hold as its prototype";
    // A derived class without a constructor has JavaScript's implicit one,
    // `constructor(...args) { super(...args); }`: it takes its base's
    // parameters, at their types, under names no source binding spells,
    // and passes them on. Actuals past them reach no parameter of the
    // base's constructor, which binds exactly its own. Each forwarded
    // read is claimed at one character of the `extends` keyword, a site
    // nothing else claims.
    type ConstructorParam = { name: string; local: string; field: string; pos: Span; property: boolean;
      at: Span; type: TypeTerm; fieldType: TypeTerm; binding: Stmt | null };
    const implicitParams = (base: ClassRecord): ConstructorParam[] => {
      const keyword = heritage ? heritage.getStart(gate.file) : 0;
      if (base.params.length > "extends".length)
        gate.fail(node, "an implicit derived constructor forwarding more parameters than its `extends` keyword has characters has no source site for each");
      return base.params.map((p, i) => ({ name: parameterName(i), local: parameterName(i), field: parameterName(i),
        pos: [keyword + i, keyword + i + 1], property: false, at: gate.span(name), type: p.type,
        fieldType: p.type, binding: null }));
    };
    // An optional parameter, `x?: T`, binds `T | undefined`, as a closure's.
    // A parameter with a default binds a hidden name, which the caller's
    // argument initializes, and a `destructure` over it, first in the
    // constructor's body, binds the source's name, the default replacing an
    // undefined argument, as a closure's parameter with a default does.
    const params = constructor ? constructor.parameters.map((p, i, all) => {
      if (p.initializer && readsThis(p.initializer))
        gate.fail(p, "a constructor parameter default that reads `this` is outside the fragment: the instance is allocated at the end of the constructor");
      if (!ts.isIdentifier(p.name) || p.dotDotDotToken)
        gate.fail(p, "a constructor parameter must be plain, required or optional");
      if (!p.questionToken && !p.initializer && i > firstOptional(all))
        gate.fail(p, "a required parameter cannot follow an optional one");
      if (p.name.text === "undefined") gate.fail(p, "shadowing undefined is outside the fragment");
      if (p.modifiers?.length && p.name.text === "then") gate.fail(p, FORGED_PROMISE);
      const local = gate.local(p.name);
      const binding: Stmt | null = p.initializer ? {
        k: "destructure", pos: gate.span(p), target: { k: "name", name: local, pos: gate.span(p.name) },
        // The hidden name is read at the whole parameter, a site apart from
        // its name, which a parameter property's field reads again.
        default_: gate.expr(p.initializer), init: { k: "id", pos: gate.span(p), name: parameterName(i) },
      } : null;
      const fieldType = p.questionToken ? gate.optionalTypeOf(p.type, p) : gate.typeOf(p.type, p);
      return { name: p.initializer ? parameterName(i) : local, local, field: p.name.text, pos: gate.span(p.name),
        property: !!p.modifiers?.length, at: gate.span(p),
        // A caller may pass `undefined` where there is a default.
        type: p.initializer ? gate.optionalTypeOf(p.type, p) : fieldType, fieldType, binding };
    }) : base ? implicitParams(base) : [];
    // Static methods are bindings of their own, bound first, so that
    // instance members and static initializers may call them. A static
    // field's initializer and a static block run, in member order, before
    // the class value is bound, which is allocated holding the static
    // fields: each is a binding of its own, which `C.x` in a static
    // initializer reads (`staticReads`), and the class value's own field
    // elsewhere.
    const staticMethods: BindingAst[] = [], statics: BindingAst[] = [];
    const staticFields: { name: PropertyKey; binding: string; pos: Span; type: TypeTerm }[] = [];
    // The prototype's methods, in member order: every instance holds the
    // prototype object under its prototype key, and reads a method there.
    const prototype: { name: PropertyKey; e: Expr }[] = [];
    for (const member of node.members) {
      if (ts.isSemicolonClassElement(member) || ts.isConstructorDeclaration(member)) continue;
      // A static block is code the definition runs where it stands among
      // the static fields: the closure of its statements, called at once,
      // `static { S }` as `(() => { S })()`. Its receiver is the class
      // value, whose statics are bindings of their own, so it reads no
      // `this`; its declarations are its own, as a closure body's are.
      if (ts.isClassStaticBlockDeclaration(member)) {
        if (readsThis(member.body))
          gate.fail(member, "a static block that reads `this` is outside the fragment: its receiver is the class value, whose later static fields JavaScript has not defined yet and which the model allocates only after its static fields are initialized");
        if (readsSuper(member.body)) gate.fail(member, STATIC_SUPER);
        gate.selfClass = null;
        const start = member.getStart(gate.file);
        const keyword: Span = [start, start + "static".length];
        const brace: Span = [member.body.end - 1, member.body.end];
        const stmts = gate.statements(member.body.statements);
        const body: Stmt[] = completes(stmts)
          ? [...stmts, { k: "return", pos: brace, e: { k: "lit", pos: brace, lit: { a: "undefined" } } }]
          : stmts;
        const block: Expr = { k: "lambda", pos: gate.span(member.body), typeParams: [], receiver: null,
          params: [], result: { k: "atom", name: "undefined", span: keyword }, guard: null,
          body: { k: "blockBody", pos: gate.span(member.body), body } };
        statics.push({ name: staticName(name.text, `[[block@${start}]]`), namePos: keyword, annot: null,
          init: { k: "apply", pos: gate.span(member), callee: block, args: [] } });
        continue;
      }
      const memberName = nameOf(member);
      if (memberName && (ts.isIdentifier(memberName) || ts.isStringLiteral(memberName)) && memberName.text === "then")
        gate.fail(member, FORGED_PROMISE);
      const modifiers = childrenOf(member, "modifiers");
      if (modifiers.some((m) => m.kind !== ts.SyntaxKind.ReadonlyKeyword && m.kind !== ts.SyntaxKind.AsyncKeyword &&
          m.kind !== ts.SyntaxKind.StaticKeyword && !CLASS_ACCESS.includes(m.kind)))
        gate.fail(member, "a class member modifier outside the fragment");
      gate.selfClass = instanceMembers;
      if (modifiers.some((m) => m.kind === ts.SyntaxKind.StaticKeyword)) {
        // A static `[Symbol.hasInstance]` method is the binding `instanceof`
        // of the class calls (`binary`), named apart from every source name.
        // A static private member `#x` is a binding as any static is,
        // which `C.#x` in the class reads (`staticPrivate`).
        const hasInstance = ts.isMethodDeclaration(member) && gate.staticHasInstance(member.name);
        if (!(ts.isPropertyDeclaration(member) || ts.isMethodDeclaration(member)) ||
            (!ts.isIdentifier(member.name) && !ts.isPrivateIdentifier(member.name) && !hasInstance))
          return gate.fail(member, unnamedMember(member, true));
        const binding = staticName(name.text,
          ts.isIdentifier(member.name) || ts.isPrivateIdentifier(member.name) ? member.name.text : HAS_INSTANCE);
        if (ts.isMethodDeclaration(member)) {
          // `C.m()` passes `C` as the receiver, a detached call `undefined`:
          // a body that reads none is the same function either way, called
          // plainly. Its signature is its annotation: functions read it there.
          // It is bound first, before the class value, which it reads, as
          // an instance member does, as the class's own binding.
          if (member.body && readsThis(member.body))
            gate.fail(member, "a static method that reads `this` is outside the fragment");
          if (member.body && readsSuper(member.body)) gate.fail(member, STATIC_SUPER);
          const annot = member.type && !member.typeParameters?.length
            ? oneTerm(signature(gate.scope, member.parameters, member.type, member, gate.span(member), true), gate.span(member))
            : null;
          staticMethods.push({ name: binding, namePos: gate.span(member.name), annot, init: gate.lambda(member) });
          // A static method keyed by a symbol is also an own property of
          // the class value, at its signature, which no copy takes, as no
          // copy takes a symbol key (or, in JavaScript, a method).
          if (hasInstance && ts.isComputedPropertyName(member.name)) {
            const symbol = gate.symbolKeys.get(gate.span(member.name.expression).join(":"));
            if (symbol === undefined || !annot)
              gate.fail(member, "a static method keyed by a symbol is an own property of the class value, at its annotated signature");
            staticFields.push({ name: { symbol }, binding, pos: gate.span(member.name), type: annot });
          }
          continue;
        }
        gate.selfClass = null;
        // A static field's writes would be mutable module state.
        if (!modifiers.some((m) => m.kind === ts.SyntaxKind.ReadonlyKeyword) || member.postfixToken)
          gate.fail(member, "a static field must be readonly and required");
        if (member.initializer && readsThis(member.initializer))
          gate.fail(member, "a static initializer that reads `this` is outside the fragment");
        if (member.initializer && readsSuper(member.initializer)) gate.fail(member, STATIC_SUPER);
        const annot = member.type ? gate.typeOf(member.type, member) : null;
        statics.push({ name: binding, namePos: gate.span(member.name), annot,
          init: member.initializer ? gate.expr(member.initializer)
            : { k: "lit", pos: gate.span(member.name), lit: { a: "undefined" } } });
        // A static field named by a property name is an own enumerable
        // data property of the class value, which the class value is
        // allocated holding, at the type its annotation states, or, without
        // one, the literal type TypeScript gives a readonly field's literal
        // initializer.
        if (ts.isIdentifier(member.name)) {
          const inferred = annot ? null : gate.staticTypes.get(gate.span(member.name).join(":"));
          if (!annot && (!inferred || "refused" in inferred))
            gate.fail(member, `a static field without an annotation, whose type TypeScript gives no term of the fragment states: ${inferred && "refused" in inferred ? inferred.refused : "no type"}`);
          const type = annot ?? (inferred && !("refused" in inferred) ? inferred : gate.fail(member, "a static field's type"));
          staticFields.push({ name: member.name.text, binding, pos: gate.span(member.name), type });
        }
        continue;
      }
      if (ts.isPropertyDeclaration(member)) {
        // A private field `#x` is an own key of each instance, its private
        // name's symbol (`memberKey`).
        if (!ts.isIdentifier(member.name) && !ts.isPrivateIdentifier(member.name))
          gate.fail(member, unnamedMember(member, false));
        const key = gate.memberKey(member.name);
        const type = gate.typeOf(member.type, member);
        if (member.initializer) {
          if (readsThis(member.initializer)) gate.fail(member, "a field initializer that reads `this` is outside the fragment");
          fields.push({ name: key, text: member.name.text, e: gate.expr(member.initializer),
            bind: { pos: gate.span(member), type } });
        } else uninitialized.set(member.name.text, { type, pos: gate.span(member.name), key });
      } else if (ts.isMethodDeclaration(member)) {
        // A method named by a `unique symbol` constant, `[Symbol.iterator]()`,
        // is the prototype's property under that symbol's key, bound under
        // a name no source spells.
        const symbol = ts.isComputedPropertyName(member.name) ? gate.writtenSymbol(member.name, member) : null;
        if (symbol !== null) {
          if (member.asteriskToken)
            gate.fail(member, GENERATOR);
          const binding = `${name.text}.[symbol ${symbol}]`;
          methods.push({ name: binding, namePos: gate.span(member.name), annot: null,
            init: method(member, { symbol }) });
          prototype.push({ name: { symbol }, e: { k: "id", pos: gate.span(member.name), name: binding } });
          continue;
        }
        // A private method `#m` is held by the prototype under its private
        // name's symbol, as a method under its name; a derived class
        // reaches none, so it is no base method.
        if (!ts.isIdentifier(member.name) && !ts.isPrivateIdentifier(member.name))
          gate.fail(member, unnamedMember(member, false));
        methods.push({ name: `${name.text}.${member.name.text}`, namePos: gate.span(member.name),
          annot: null, init: method(member, gate.memberKey(member.name)) });
        if (ts.isIdentifier(member.name))
          methodBindings.set(member.name.text, `${name.text}.${member.name.text}`);
        prototype.push({ name: gate.memberKey(member.name),
          e: { k: "id", pos: gate.span(member.name), name: `${name.text}.${member.name.text}` } });
      } else gate.fail(member, classMemberRefusal(member));
    }
    gate.selfClass = instanceMembers;
    for (const p of params)
      if (p.property) fields.push({ name: p.field, text: p.field, e: { k: "id", pos: p.pos, name: p.local }, bind: { pos: p.at, type: p.fieldType } });
    // A class allocates its prototype object once, holding its methods, and
    // each instance holds it under the prototype key, first: the key's
    // value is a read of a constant, so its place changes nothing. A
    // derived class's prototype holds its own methods and links to its
    // base's under the prototype key, as JavaScript's does. A class that
    // `instanceof` tests owns its key there. A prototype holding nothing
    // of its own, which nothing tests, is not allocated: its instances
    // hold its base's, or none, and every read and test answers alike.
    const prototypeBinding: BindingAst[] = [];
    let proto: Expr | null = null;
    let protoBinding: string | null = null;
    const baseType = heritage?.types[0];
    const baseProto: Expr | null = base?.proto && baseType
      ? { k: "id", pos: gate.span(baseType.expression), name: base.proto } : null;
    const tested = [...this.classTests.values()].includes(name.text);
    if (!prototype.length && !tested && base?.proto) protoBinding = base.proto;
    if (prototype.length || tested) {
      const at: Span = [name.getStart(gate.file), node.end];
      protoBinding = prototypeName(name.text);
      prototypeBinding.push({ name: prototypeName(name.text), namePos: at, annot: null,
        init: { k: "alloc", pos: at, fields: prototype, ...(baseProto ? { proto: baseProto } : {}),
          ...(tested ? { brand: { key: classKey(name.text), pos: [name.end, node.end] } } : {}) } });
    }
    if (protoBinding) {
      // Read at the `class` keyword, a site no other claim has; the
      // allocation states it apart from the fields, as no source key.
      const keyword = gate.file.text.indexOf("class", node.getStart(gate.file));
      if (keyword < 0 || keyword > name.getStart(gate.file)) gate.fail(node, "a class declaration without its keyword");
      proto = { k: "id", pos: [keyword, keyword + "class".length], name: protoBinding };
    }
    // A `return` in a constructor's own code, outside any function nested
    // in it: `new` would evaluate to the instance, not to what it returns.
    const nested = (n: Node): boolean => ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) ||
      ts.isArrowFunction(n) || ts.isMethodDeclaration(n) || ts.isClassDeclaration(n) || ts.isClassExpression(n);
    const returns = (n: Node): boolean => ts.isReturnStatement(n) ||
      (!nested(n) && !!n.forEachChild((c) => returns(c) || undefined));
    const assignment = (statement: Statement) => {
      const e = ts.isExpressionStatement(statement) ? statement.expression : undefined;
      return e && ts.isBinaryExpression(e) && e.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
        ts.isPropertyAccessExpression(e.left) && e.left.expression.kind === ts.SyntaxKind.ThisKeyword &&
        (ts.isIdentifier(e.left.name) || ts.isPrivateIdentifier(e.left.name))
        ? { field: e.left.name.text, value: e.right } : undefined;
    };
    const assigns = (statement: Statement): boolean => !!assignment(statement) ||
      (ts.isBlock(statement) && statement.statements.some(assigns)) ||
      (ts.isIfStatement(statement) && (assigns(statement.thenStatement) ||
        (!!statement.elseStatement && assigns(statement.elseStatement))));
    // The constructor's statements from `body` on, then its allocation.
    // Statements other than field assignments run before the allocation:
    // the values evaluated before one are bound first, in order, to names
    // no source binding can spell, so evaluation order is the source's. A
    // last `if` that assigns fields ends each arm with its own allocation.
    const construct = (body: readonly Statement[], before: Field[], done: Set<string>,
        prelude: Stmt[] = [], end: Span | null = null): Stmt[] => {
      const fields = before.map((f) => ({ ...f }));
      const assigned = new Set(done);
      const statements: Stmt[] = [...prelude];
      let branched = false;
      const flush = () => {
        for (const f of fields) {
          if (!f.bind || f.e.k === "lit") continue;
          const hidden = `this.${f.text}`;
          statements.push({ k: "const", pos: f.bind.pos,
            bindings: [{ name: hidden, namePos: f.bind.pos, annot: f.bind.type, init: f.e }] });
          f.e = { k: "id", pos: f.bind.pos, name: hidden };
          f.bind = null;
        }
      };
      for (const [i, statement] of body.entries()) {
        const assigning = assignment(statement);
        if (assigning) {
          const field = uninitialized.get(assigning.field);
          if (!field || assigned.has(assigning.field))
            gate.fail(statement, "a constructor assigns each uninitialized field once");
          if (readsThis(assigning.value))
            gate.fail(statement, "a constructor assignment that reads `this` is outside the fragment");
          assigned.add(assigning.field);
          fields.push({ name: field.key, text: assigning.field, e: gate.expr(assigning.value),
            bind: { pos: gate.span(statement), type: field.type } });
          continue;
        }
        if (ts.isIfStatement(statement) && assigns(statement) && i === body.length - 1) {
          if (readsThis(statement.expression))
            gate.fail(statement, "a constructor statement that reads `this` is outside the fragment");
          // An unbraced arm, `else if` included, is the one statement a
          // block around it would hold.
          // Each arm's allocation is its own statement, entered at the
          // arm's last character, or, with no `else`, at the condition's
          // closing parenthesis.
          const arm = (s: Statement | undefined): Stmt[] =>
            construct(!s ? [] : ts.isBlock(s) ? s.statements : [s], fields, assigned, [],
              s ? [s.end - 1, s.end] : conditionParen(statement, gate.file));
          flush();
          statements.push({ k: "if", pos: gate.span(statement), cond: gate.expr(statement.expression),
            then: arm(statement.thenStatement), else_: arm(statement.elseStatement) });
          branched = true;
          break;
        }
        if (returns(statement))
          gate.fail(statement, "a constructor does not return");
        if (readsThis(statement))
          gate.fail(statement, assigns(statement)
            ? "a constructor assigns fields in its own block, or in the arms of its last `if`"
            : "a constructor statement that reads `this` is outside the fragment");
        flush();
        statements.push(gate.stmt(statement));
      }
      if (!branched) {
        for (const [f, { pos, key }] of uninitialized)
          if (!assigned.has(f)) fields.push({ name: key, text: f, e: { k: "lit", pos, lit: { a: "undefined" } }, bind: null });
        // The allocation ends the constructor's block: the instance is what
        // `new` evaluates to. A derived instance is its base's part, copied,
        // then its own fields over it: the allocation from parts an object
        // literal with a spread is.
        const at = gate.span(name);
        const instanceValue: Expr = derivedBase
          ? { k: "build", pos: at, parts: [{ spread: derivedBase },
              ...fields.map(({ name, e }) => ({ name: typeof name === "string" ? name : gate.fail(node, PRIVATE_INHERITANCE), e }))],
              ...(proto ? { proto } : {}) }
          : { k: "alloc", pos: at, fields: fields.map(({ name, e }) => ({ name, e })),
            ...(proto ? { proto } : {}) };
        statements.push({ k: "return", pos: end ?? at, e: instanceValue });
      }
      return statements;
    };
    // A derived constructor: its statements before `super(...)`, which may
    // not touch `this`, then the base's constructor at the actuals, bound
    // to a name no source binding spells, then its own fields and
    // statements, as JavaScript runs them.
    let body: readonly Statement[] = constructor?.body?.statements ?? [];
    let prelude: Stmt[] = [];
    let derivedBase: Expr | null = null;
    if (base && heritage) {
      const isSuperCall = (st: Statement): st is ts.ExpressionStatement =>
        ts.isExpressionStatement(st) && ts.isCallExpression(st.expression) &&
        st.expression.expression.kind === ts.SyntaxKind.SuperKeyword;
      const callsSuper = (n: Node): boolean => n.kind === ts.SyntaxKind.SuperKeyword ||
        (!ts.isFunctionExpression(n) && !ts.isFunctionDeclaration(n) && !!n.forEachChild((c) => callsSuper(c) || undefined));
      let at: Span = gate.span(heritage);
      let calleeAt: Span = [node.end - 1, node.end];
      let actuals: Expr[] = params.map((p) => ({ k: "id", pos: p.pos, name: p.name }));
      if (constructor) {
        const index = body.findIndex(isSuperCall);
        if (index < 0 || body.some((st, i) => i !== index && callsSuper(st)))
          gate.fail(constructor, "a derived constructor calls `super(...)` once, as a statement of its own body");
        for (const st of body.slice(0, index))
          if (readsThis(st))
            gate.fail(st, "`this` before `super(...)` throws in JavaScript; the instance is allocated at the end of the constructor, so a read or write of it there is refused");
        prelude = body.slice(0, index).map((st) => gate.stmt(st));
        const superCall = body[index];
        const call = superCall && ts.isExpressionStatement(superCall) && ts.isCallExpression(superCall.expression)
          ? superCall.expression
          : gate.fail(constructor, "a derived constructor calls `super(...)` once, as a statement of its own body");
        for (const a of call.arguments)
          if (ts.isSpreadElement(a) || readsThis(a)) gate.fail(a, "a `super(...)` argument is an ordinary expression not reading `this`");
        actuals = call.arguments.map((a) => gate.expr(a));
        at = gate.span(call);
        calleeAt = gate.span(call.expression);
        body = body.slice(index + 1);
      }
      const slot = baseName(name.text);
      prelude.push({ k: "const", pos: at, bindings: [{ name: slot, namePos: at, annot: null,
        init: { k: "new", pos: at, callee: { k: "id", pos: calleeAt, name: base.fresh }, args: actuals } }] });
      derivedBase = { k: "id", pos: [heritage.getStart(gate.file), heritage.getStart(gate.file) + "extends".length], name: slot };
    }
    // The class value is its constructor as construct-only code, which only
    // `new` runs, holding its static fields.
    // A static field names none of the class's binders (TypeScript refuses
    // one that does), so a generic class value's bag is the same at each
    // of its instances.
    // A static initializer constructing the class constructs it through
    // its construct-only code, bound before them (`selfConstruction`).
    const constructs = node.members.some((m) => {
      let found = false;
      const visit = (n: Node): void => {
        if (ts.isNewExpression(n) && ts.isIdentifier(n.expression) &&
            gate.classReads.get(gate.span(n.expression).join(":")) === name.text) found = true;
        n.forEachChild(visit);
      };
      if ((ts.isPropertyDeclaration(m) && m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword)) ||
          ts.isClassStaticBlockDeclaration(m)) visit(m);
      return found;
    });
    const constructorLambda: Expr = { k: "lambda", pos: gate.span(node),
      typeParams: [], receiver: null, params: params.map((p) => ({ name: p.name, type: p.type })),
      result: instance, guard: null, body: { k: "blockBody", pos: gate.span(constructor?.body ?? node),
        body: [...params.flatMap((p) => p.binding ? [p.binding] : []),
          ...construct(body, fields, new Set(), prelude)] } };
    const lambda: Expr = { k: "ctor", pos: gate.span(node), ...(typeParams.length ? { typeParams } : {}),
      // Its code is the construct-only code bound before the static
      // initializers, where they construct the class (`decodeBindings`).
      lambda: constructs || extended ? { k: "id", pos: gate.span(name), name: freshName(name.text) } : constructorLambda,
      ...(staticFields.length ? { statics: staticFields.map((f) =>
        ({ name: f.name, e: { k: "id", pos: f.pos, name: f.binding } satisfies Expr })) } : {}) };
    const type: TypeTerm = { k: "constructor", params: params.map((p) => p.type), rest: null, result: instance,
      ...(staticFields.length ? { statics: staticFields.map((f) => ({ name: f.name, type: f.type })) } : {}),
      span: gate.span(name) };
    // A class another extends is also bound, first, as its fresh
    // constructor, claimed at the instance it allocates besides its own
    // construct signature; the class value is that binding.
    // A class another extends, or whose static initializers construct it,
    // is also bound, first, as its fresh constructor, before its static
    // initializers, claimed at the instance it allocates besides its own
    // construct signature: a derived class's construction, and a static
    // initializer's (`selfConstruction`), construct through it. The class
    // value is that binding, or, holding static fields, its constructor
    // allocated again with them (`decodeBindings`).
    let freshBinding: BindingAst[] = [];
    let classBindings: BindingAst[] = [{ name: name.text, namePos: gate.span(name), annot: type, init: lambda }];
    if (extended || constructs) {
      const brace = gate.file.text.indexOf("{", heritage ? heritage.end : name.end);
      freshBinding = [{ name: freshName(name.text), namePos: [node.getStart(gate.file), name.end], annot: null,
        init: { k: "ctor", pos: [node.getStart(gate.file), name.end], ...(typeParams.length ? { typeParams } : {}),
          lambda: constructorLambda } }];
      classBindings = [{ name: name.text, namePos: gate.span(name), annot: type,
        init: staticFields.length ? lambda : { k: "id", pos: [brace, brace + 1], name: freshName(name.text) } }];
    }
    gate.classRecords.set(name.text, { params: params.map((p) => ({ name: p.name, type: p.type })),
      methods: methodBindings, fresh: freshName(name.text), proto: protoBinding,
      binders: binders.map((tp) => tp.name.text) });
    return { k: "const", pos: gate.span(node),
      bindings: [...staticMethods, ...methods, ...prototypeBinding, ...freshBinding, ...statics, ...classBindings] };
  } finally {
    gate.strict = outerStrict;
    gate.superClass = outerSuper;
    gate.selfClass = outerSelf;
  }
}

export function registerDeclaredType(this: Gate, name: string, required: number, total: number,
    declaration: DeclarationIdentity, node: Node, expression: TypeTerm): void {
  const gate: Gate = this;
  if (gate.declaredTypes.has(name))
    gate.fail(node, "duplicate type name");
  gate.declaredTypes.set(name, { required, total, declaration });
  if (expression.k === "array" || expression.k === "tuple" || expression.k === "reference")
    gate.aliasEquations.set(name, { total, declaration, expression });
}

/** The key a member name spells: its text, or a private name's symbol,
 * the key of the member TypeScript binds it to, which no code outside
 * the class spells. */
export function memberKey(this: Gate, name: ts.MemberName): PropertyKey {
  const gate: Gate = this;
  if (ts.isIdentifier(name)) return name.text;
  const symbol = gate.privateKeys.get(gate.span(name).join(":"));
  if (symbol === undefined) return gate.fail(name, "a private name TypeScript binds to no member");
  return { symbol };
}

/** `C.#x` of a static private member of the file's class `C`, with `C`
 * the class TypeScript binds it to: the binding the class statement gives
 * the member. Null for a private name no static member declares. */
export function staticPrivate(this: Gate, node: ts.PropertyAccessExpression): { binding: string; cls: string } | null {
  const gate: Gate = this;
  const name = node.name;
  if (!ts.isPrivateIdentifier(name)) return null;
  const symbol = gate.privateKeys.get(gate.span(name).join(":"));
  const cls = symbol === undefined ? undefined : gate.symbolIdentities[symbol]?.name.split(".")[0];
  const declaration = cls === undefined ? undefined : gate.file.statements.find((st): st is ClassDeclaration =>
    ts.isClassDeclaration(st) && st.name?.text === cls);
  const member = declaration?.members.find((m) => {
    const memberName = nameOf(m);
    return !!memberName && ts.isPrivateIdentifier(memberName) && memberName.text === name.text;
  });
  if (!cls || !member || !isStatic(member))
    return null;
  if (!ts.isIdentifier(node.expression) || gate.classReads.get(gate.span(node.expression).join(":")) !== cls)
    gate.fail(node, "a static private member read other than through its class's name: private statics are bindings of their own");
  return { binding: staticName(cls, name.text), cls };
}

/** `new C(…)` in a static initializer of `C`, which runs before the class
 * value exists: the class's construct-only code, bound before the static
 * initializers (`freshName`), where constructing runs no code that
 * could read the class value (`selfConstructs`). Null for any other `new`. */
export function selfConstruction(this: Gate, node: ts.NewExpression): Expr | null {
  const gate: Gate = this;
  const callee = node.expression;
  if (!ts.isIdentifier(callee)) return null;
  const cls = gate.classReads.get(gate.span(callee).join(":"));
  const init = gate.staticInitOf(node);
  if (cls === undefined || init?.cls !== cls || init.closure) return null;
  const declaration = gate.file.statements.find((st): st is ClassDeclaration =>
    ts.isClassDeclaration(st) && st.name?.text === cls);
  if (!declaration || !selfConstructs(declaration))
    gate.fail(node, "a static initializer constructing its class where constructing it reads the class or runs code, or another static initializer runs code: it could read a static field not yet defined, `undefined` in JavaScript, or the class value, which the model allocates only after its static fields are initialized");
  return { k: "id", pos: gate.span(callee), name: freshName(cls) };
}

/** Whether `body` reads class `cls`: an identifier TypeScript binds to it. */
export function readsClass(this: Gate, body: Node, cls: string): boolean {
  const gate: Gate = this;
  const visit = (n: Node): boolean =>
    (ts.isIdentifier(n) && gate.classReads.get(gate.span(n).join(":")) === cls) ||
    !!n.forEachChild((c) => visit(c) || undefined);
  return visit(body);
}

/** The class whose static field initializer or static block `node` is in,
 * and whether a closure created there holds it. */
export function staticInitOf(this: Gate, node: Node): { cls: string; closure: boolean } | null {
  let closure = false;
  for (let at: Node = node; at.parent; at = at.parent) {
    const parent = at.parent;
    if (ts.isClassDeclaration(parent)) {
      const isStaticInit = ts.isClassStaticBlockDeclaration(at) ||
        (ts.isPropertyDeclaration(at) && at.initializer !== undefined &&
          !!at.modifiers?.some((m) => m.kind === ts.SyntaxKind.StaticKeyword));
      return isStaticInit && parent.name ? { cls: parent.name.text, closure } : null;
    }
    if (ts.isFunctionLikeDeclaration(at)) closure = true;
  }
  return null;
}

/** The class binding an identifier of an instance member reads, where
 * TypeScript binds it to the class being lowered. */
export function ownClass(this: Gate, node: Node): string | null {
  const gate: Gate = this;
  const cls = gate.classReads.get(gate.span(node).join(":"));
  if (!cls || cls !== gate.selfClass?.name) return null;
  if (gate.selfClass.generic)
    gate.fail(node, "a generic class's instance member or static method reading its own class: the class value is quantified over the binders its declaring unit reads as parameter rows, and a module value is read only at ground instances");
  return selfName(cls);
}
