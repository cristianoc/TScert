/* Part of the trusted front end (fragment-parse.mts): Expressions: how the gate reads each expression form, operators and closures included.
 * Each function is a method of the gate: `Gate` holds it as a field, so a call
 * reads `this.name(...)`; its body names the gate `gate`, typed, which lets a
 * call that never returns (`gate.fail`) narrow what follows. */
import * as ts from "typescript/unstable/ast";
import type { ArrowFunction, ClassDeclaration, BinaryExpression, Expression, FunctionExpression, Identifier, MethodDeclaration, Node, Statement } from "typescript/unstable/ast";
import type { PropertyKey, TypeTerm } from "./declaration-types.mts";
import type { Atom } from "./claim.mts";
import { bigintText, CLASS_ACCESS, numericLexeme, GENERIC_METHOD_RECEIVER, numericKey, optionalTerm } from "./type-term.mts";
import type { Expr, PatternAst, Stmt, ArithOp, BinaryOp, UnaryOp, ArrayElemAst, TypeofShape } from "./fragment.mts";
import { CHAIN } from "./fragment.mts";
import type { Span } from "./span.mts";
import { nameOf } from "./syntax.mts";
import { asyncReturnName, elementAtName, hasPropertyName, literalTerm } from "./intrinsics.mts";
import { guardResult } from "./fragment-guards.mts";
import { GENERATOR, HAS_INSTANCE, booleanForm, booleanReturn, TAG_WRITE, INSTANCE_STATIC, type ObjectPart, SPREAD_POSITION, STATIC_INIT_CLASS, STATIC_INIT_CLOSURE, bindingScope, callableAssign, classKey, completes, firstOptional, inKey, literalExpr, parameterName, prototypeName, skipParentheses, staticFieldOf, staticMethodOf, staticName } from "./fragment-support.mts";
import type { Gate } from "./fragment-parse.mts";

export function expr(this: Gate, node: Expression): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  // As in `atomsOf`: Expression is one base interface, so each form of
  // expression is recognized by its own predicate.
  if (ts.isParenthesizedExpression(node))
    // Parentheses carry no meaning of their own, but the producer records
    // the type of a parenthesized expression at the span of the outermost
    // parenthesis. Unwrap, and widen the span to match, so the two agree
    // on the key. Nested parentheses widen again at each level.
    return { ...this.expr(node.expression), pos: gate.span(node) };

  // A read in an enum member's initializer of a member of its enum.
  if (ts.isIdentifier(node) || ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node)) {
    const read = gate.enumRead(node);
    if (read) return read;
  }

  // A `const enum` member's read is its value, which TypeScript writes in
  // its place.
  if (ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node)) {
    const inlined = gate.constEnumReads.get(gate.span(node).join(":"));
    if (inlined !== undefined) return literalExpr(inlined, gate.span(node));
  }

  // A link of an optional chain: the chain up to it is one `optional`.
  if (
    (ts.isPropertyAccessExpression(node) || ts.isElementAccessExpression(node) ||
      ts.isCallExpression(node) || ts.isNonNullExpression(node)) &&
    node.flags & ts.NodeFlags.OptionalChain
  )
    return gate.optionalChain(node);

  if (ts.isConditionalExpression(node))
    return {
      k: "conditional",
      pos: gate.span(node),
      cond: gate.expr(node.condition),
      then: gate.expr(node.whenTrue),
      else_: gate.expr(node.whenFalse),
    };

  if (ts.isAwaitExpression(node)) return gate.awaitExpr(node);

  // `void e` is `e, undefined`: the operand for its effects, then the value
  // `undefined`, a literal at the keyword.
  if (ts.isVoidExpression(node)) {
    const start = node.getStart(gate.file);
    return {
      k: "comma",
      pos: gate.span(node),
      left: gate.expr(node.expression),
      right: { k: "lit", pos: [start, start + "void".length], lit: { a: "undefined" } },
    };
  }

  // A template without substitutions is its string; `text` is the cooked
  // value, as for a string literal.
  if (ts.isNoSubstitutionTemplateLiteral(node))
    return { k: "lit", pos: gate.span(node), lit: { a: "stringlit", v: node.text } };
  if (ts.isTemplateExpression(node)) return gate.template(node);

  if (ts.isIdentifier(node)) {
    // `undefined` is the value where TypeScript binds it to the global; a
    // binding of that name (an import's) is no value the fragment reads.
    if (node.text === "undefined") {
      if (!gate.globalUndefined.has(gate.span(node).join(":")))
        gate.fail(node, "a binding named `undefined` other than the global is outside the fragment");
      return { k: "lit", pos: gate.span(node), lit: { a: "undefined" } };
    }
    // A class is a value like any other: its construct-only code is what a
    // plain call cannot run, which its type records. Its own name in its
    // instance members, which run only once the class exists, is its class
    // binding, which they cannot capture where they are created. A static
    // initializer runs before the class value exists.
    const cls = gate.classReads.get(gate.span(node).join(":"));
    if (cls !== undefined && gate.staticInitOf(node)?.cls === cls) gate.fail(node, STATIC_INIT_CLASS);
    return { k: "id", pos: gate.span(node), name: gate.ownClass(node) ?? gate.local(node) };
  }

  if (ts.isNewExpression(node)) {
    // `new Promise(e)`, which the overlay reads as a call of the intrinsic
    // stating the same step, read at the constructor's name. Its type
    // arguments, if written, are TypeScript's: the intrinsic's instance is
    // the producer's to propose and Lean's to check.
    const intrinsic = gate.globalIntrinsics.get(gate.span(node).join(":"));
    if (intrinsic)
      return gate.intrinsic(intrinsic, gate.span(node), gate.span(node.expression),
        (node.arguments ?? []).map(a => gate.expr(a)));
    // Explicit type arguments name the instantiation the producer proposes;
    // Lean validates that instantiation like any other. The callee is any
    // value; its type decides whether it has construct-only code.
    const spreads: number[] = [];
    const args = (node.arguments ?? []).map((arg, i) => {
      if (!ts.isSpreadElement(arg)) return gate.expr(arg);
      spreads.push(i);
      return gate.spreadOperand(arg);
    });
    return {
      k: "new",
      pos: gate.span(node),
      callee: gate.selfConstruction(node) ?? gate.expr(node.expression),
      args,
      ...(spreads.length ? { spreads } : {}),
      ...(node.typeArguments?.length
        ? { typeArgs: node.typeArguments.map((t) => gate.typeOf(t, t)) }
        : {}),
    };
  }

  if (node.kind === ts.SyntaxKind.ThisKeyword) {
    // Only an ordinary function expression, a method, or a declaration
    // stating a `this` parameter binds a receiver.
    // In sloppy code Lean admits the read where the receiver's type holds
    // objects only (`Fragment.sloppyReceiverReason`), from the function's
    // `strict` fact.
    if (gate.receiverMode === null)
      gate.fail(node, "`this` where no receiver is bound");
    return { k: "this", pos: gate.span(node) };
  }

  if (node.kind === ts.SyntaxKind.NullKeyword)
    return { k: "lit", pos: gate.span(node), lit: { a: "null" } };
  if (node.kind === ts.SyntaxKind.TrueKeyword)
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "booleanlit", v: "true" },
    };
  if (node.kind === ts.SyntaxKind.FalseKeyword)
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "booleanlit", v: "false" },
    };

  // `/P/F` allocates a regex each time it is evaluated: a call of the
  // intrinsic of its shape (`regexp.mts`): the call at the literal, the
  // intrinsic read at its opening slash.
  if (node.kind === ts.SyntaxKind.RegularExpressionLiteral) {
    const intrinsic = gate.regexps.get(gate.span(node).join(":"));
    if (!intrinsic) gate.fail(node, "a regular expression literal the declaration graph did not read");
    const start = node.getStart(gate.file);
    return gate.intrinsic(intrinsic, gate.span(node), [start, start + 1], []);
  }
  if (ts.isStringLiteral(node))
    // `text` is the DECODED value, which is what a literal type denotes.
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "stringlit", v: node.text },
    };

  // A bigint literal, negated or not, is its integer whatever its spelling.
  if (ts.isBigIntLiteral(node))
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "bigintlit", v: bigintText(node.text, false) },
    };
  if (
    ts.isPrefixUnaryExpression(node) &&
    node.operator === ts.SyntaxKind.MinusToken &&
    ts.isBigIntLiteral(node.operand)
  )
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "bigintlit", v: bigintText(node.operand.text, true) },
    };

  if (
    ts.isPrefixUnaryExpression(node) &&
    node.operator === ts.SyntaxKind.MinusToken &&
    ts.isNumericLiteral(node.operand)
  ) {
    const lexeme = numericLexeme(node.operand, gate.file);
    if (lexeme === null)
      gate.fail(node, "non-decimal numeric literal");
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "numberlit", v: "-" + lexeme },
    };
  }
  // `+1` is the number `1`: unary plus returns a number operand unchanged,
  // and TypeScript types it as the literal, as it does `-1`.
  if (
    ts.isPrefixUnaryExpression(node) &&
    node.operator === ts.SyntaxKind.PlusToken &&
    ts.isNumericLiteral(node.operand) &&
    numericLexeme(node.operand, gate.file) !== null
  )
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "numberlit", v: numericLexeme(node.operand, gate.file) ?? "" },
    };

  if (ts.isNumericLiteral(node)) {
    const lexeme = numericLexeme(node, gate.file);
    if (lexeme === null)
      gate.fail(node, "non-decimal numeric literal");
    return {
      k: "lit",
      pos: gate.span(node),
      lit: { a: "numberlit", v: lexeme },
    };
  }

  if (ts.isArrowFunction(node) || ts.isFunctionExpression(node))
    return gate.lambda(node);

  if (ts.isObjectLiteralExpression(node)) {
    const parts = gate.objectFields(node, new Set<string>());
    const fields = parts.flatMap((p) => "spread" in p ? [] : [p]);
    if (fields.length === parts.length) return { k: "alloc", pos: gate.span(node), fields };
    // Beside a spread, a key is a string: the copy's keys are compared with
    // the written ones by name.
    return { k: "build", pos: gate.span(node), parts: parts.map((p) => "spread" in p ? p
      : p.computed ? gate.fail(node, "a computed key in an object literal with a spread is outside the fragment")
      : typeof p.name === "string" ? { name: p.name, e: p.e }
      : gate.fail(node, "a symbol key in an object literal with a spread is outside the fragment")) };
  }

  if (ts.isPropertyAccessExpression(node)) {
    // `ns.x`, a member of a namespace import: a read of the binding it is
    // (`namespace-members.mts`).
    const member = gate.namespaceMember(node);
    if (member !== undefined) return { k: "id", pos: gate.span(node), name: member };
    if (node.questionDotToken)
      gate.fail(node, "optional property access is outside the fragment");
    // `C.x` that TypeScript binds to a static field of class `C` reads the
    // binding its initializer bound, in a static initializer of `C`, which
    // runs before the class value exists, and the class value's own field
    // anywhere else; a static method's is the binding the class statement
    // gives it first (`classStmt`), which a static initializer may call
    // where its body does not read the class, which the model allocates only
    // after the static initializers. A
    // private static field is a binding of its own after the members.
    // A static member a base class declares is reached through the class
    // value's prototype, the base class value, which the model's class
    // value does not hold.
    if (gate.inheritedStatics.has(gate.span(node.name).join(":")))
      gate.fail(node, "a static member read through a class that inherits it from its base is outside the fragment: " +
        "the class value reaches it through its prototype, which the model's class value does not hold");
    const cls = gate.staticReads.get(gate.span(node.name).join(":"));
    const init = gate.staticInitOf(node);
    if (cls !== undefined && staticFieldOf(gate.file, cls, node.name.text)) {
      if (init?.cls !== cls)
        return { k: "read", pos: gate.span(node), field: gate.memberKey(node.name), e: gate.expr(node.expression) };
      if (init.closure) gate.fail(node, STATIC_INIT_CLOSURE);
      return { k: "id", pos: gate.span(node), name: staticName(cls, node.name.text) };
    }
    const privateStatic = gate.staticPrivate(node);
    const owner = cls ?? privateStatic?.cls;
    const method = owner === undefined ? undefined : staticMethodOf(gate.file, owner, node.name.text);
    if (owner !== undefined && init?.cls === owner && method &&
        (init.closure || (method.body !== undefined && gate.readsClass(method.body, owner))))
      gate.fail(node, STATIC_INIT_CLASS);
    if (privateStatic !== null && !method && privateStatic.cls === gate.selfClass?.name)
      gate.fail(node, INSTANCE_STATIC);
    if (cls !== undefined)
      return { k: "id", pos: gate.span(node), name: staticName(cls, node.name.text) };
    if (privateStatic !== null) return { k: "id", pos: gate.span(node), name: privateStatic.binding };
    return {
      k: "read",
      pos: gate.span(node),
      field: gate.memberKey(node.name),
      e: gate.expr(node.expression),
    };
  }

  if (ts.isArrayLiteralExpression(node)) {
    // `[...e]` over a program's iterable is the fresh array its iterator's
    // values are collected into (`collect`).
    const [only] = node.elements;
    if (node.elements.length === 1 && only && ts.isSpreadElement(only)) {
      const kind = gate.iterations.get(gate.span(only.expression).join(":"));
      if (kind?.startsWith("client")) {
        if (gate.hoist?.spread !== only) gate.fail(only, SPREAD_POSITION);
        return gate.collect(only.expression);
      }
    }
    if (node.elements.some((e) => ts.isOmittedExpression(e)))
      gate.fail(node, "array literal holes are outside the fragment");
    // A spread stands for its operand's elements, read where it is written,
    // as an argument spread's operand is (`spreadOperand`): over a string, a
    // `Set`, a `Map` or a host collection iterator, those of `%Spread:K%(e)`,
    // the fresh array of what the host's iterator yields. The literal is a
    // fresh array of its own, whose contract its claim states.
    const spreads: number[] = [];
    const elems = node.elements.map((e, i) => {
      if (!ts.isSpreadElement(e)) return gate.expr(e);
      spreads.push(i);
      return gate.spreadOperand(e);
    });
    return {
      k: "arrayLit",
      pos: gate.span(node),
      elems,
      ...(spreads.length ? { spreads } : {}),
    };
  }

  if (ts.isElementAccessExpression(node)) {
    if (node.questionDotToken)
      gate.fail(node, "optional element access is outside the fragment");
    // A `unique symbol` constant names one key: evaluating it has no
    // effect, so the read is the named read of that symbol's key.
    // `xs[k]` of an array at a `number` key is the host's read of the
    // property the number names (`%ElementAt%`, `intrinsics.mts`): the
    // object, the key, then the read, as the access evaluates them.
    // The read a `for...in` body starts with at its key is the value of
    // the entry the loop's step yielded (`forInStmt`).
    const entry = gate.entryReads.get(gate.span(node).join(":"));
    if (entry !== undefined)
      return { k: "index", pos: gate.span(node), e: { k: "id", pos: gate.span(node.expression), name: entry },
        key: { k: "lit", pos: gate.span(node.argumentExpression), lit: { a: "numberlit", v: "1" } } };
    if (gate.hostElements.has(gate.span(node).join(":"))) {
      const bracket = node.expression.end;
      return gate.intrinsic(elementAtName, gate.span(node), [bracket, bracket + 1],
        [gate.expr(node.expression), gate.expr(node.argumentExpression)]);
    }
    const [start, end] = gate.span(node.argumentExpression);
    const symbol = gate.symbolKeys.get(`${start}:${end}`);
    if (symbol !== undefined)
      return {
        k: "read",
        pos: gate.span(node),
        field: { symbol },
        e: gate.expr(node.expression),
      };
    return {
      k: "index",
      pos: gate.span(node),
      e: gate.expr(node.expression),
      key: gate.expr(node.argumentExpression),
    };
  }

  // `typeof e` as a value: the string naming the operand's shape. A
  // comparison of it with a shape's literal is a test (`typeofTest`).
  if (ts.isTypeOfExpression(node))
    return {
      k: "unary",
      op: "typeof",
      pos: gate.span(node),
      e: gate.expr(node.expression),
    };

  // A type assertion is the operand's value; the runtime never sees it.
  // What it asserts is an obligation on the operand, never a fact. `as
  // const` asserts nothing: it asks for the operand's literal types, which
  // the claims state and the checker establishes from the operand. The
  // older form `<T>e` is the same assertion as `e as T`.
  if (
    (ts.isAsExpression(node) || ts.isTypeAssertion(node)) &&
    ts.isTypeReferenceNode(node.type) &&
    ts.isIdentifier(node.type.typeName) &&
    node.type.typeName.text === "const" &&
    !node.type.typeArguments
  )
    return {
      k: "cast",
      pos: gate.span(node),
      cast: "const",
      annot: null,
      e: gate.expr(node.expression),
    };
  if (ts.isAsExpression(node) || ts.isTypeAssertion(node) || ts.isSatisfiesExpression(node))
    return {
      k: "cast",
      pos: gate.span(node),
      cast: ts.isSatisfiesExpression(node) ? "satisfies" : "as",
      annot: gate.typeOf(node.type),
      e: gate.expr(node.expression),
    };
  if (ts.isNonNullExpression(node))
    return {
      k: "cast",
      pos: gate.span(node),
      cast: "nonNull",
      annot: null,
      e: gate.expr(node.expression),
    };

  if (ts.isPostfixUnaryExpression(node))
    return gate.update(node, node.operand, node.operator, null, true);
  if (
    ts.isPrefixUnaryExpression(node) &&
    (node.operator === ts.SyntaxKind.PlusPlusToken ||
      node.operator === ts.SyntaxKind.MinusMinusToken)
  )
    return gate.update(node, node.operand, node.operator, null, false);

  if (ts.isPrefixUnaryExpression(node)) {
    const unary: Record<number, UnaryOp> = {
      [ts.SyntaxKind.MinusToken]: "neg",
      [ts.SyntaxKind.PlusToken]: "plus",
      [ts.SyntaxKind.TildeToken]: "bitNot",
    };
    const op = unary[node.operator];
    if (op) return { k: "unary", pos: gate.span(node), op, e: gate.expr(node.operand) };
    if (node.operator !== ts.SyntaxKind.ExclamationToken)
      gate.fail(node, "unary operator outside the fragment");
    return { k: "not", pos: gate.span(node), e: gate.expr(node.operand) };
  }

  if (ts.isBinaryExpression(node)) return gate.binary(node);

  if (ts.isCallExpression(node)) {
    // `Array.isArray(e)`, which the declaration graph found to be the
    // standard library's, read through its reviewed overlay entry.
    const [tested] = node.arguments;
    if (gate.globalTests.has(gate.span(node).join(":")) && tested)
      return { k: "arrayTest", pos: gate.span(node), e: gate.expr(tested) };
    // A listed guard of the compiler API's family (HOST-FAMILIES.md, "A
    // guard on any argument"): the test of its argument's value, or of its
    // object's tag field, against the entry's exact tag set, after the
    // obligation that the argument is within the guard's domain. An
    // immutable name is tested where it is held; any other argument but a
    // name is evaluated once, into a slot of its own. A name that is
    // assigned, may throw on its read or is a library value is an ordinary
    // call's argument, at the guard's plain signature.
    const callee = ts.isPropertyAccessExpression(node.expression) ? gate.namespaceMember(node.expression)
      : ts.isIdentifier(node.expression) ? gate.local(node.expression) : undefined;
    const guard = callee === undefined ? undefined : gate.hostGuards.get(callee);
    if (guard && (node.arguments.length !== 1 || node.arguments.some(ts.isSpreadElement) || node.typeArguments?.length))
      gate.fail(node, "a call of a family guard passes its one argument, written as one");
    let argument: Expression | undefined = tested;
    while (argument && ts.isParenthesizedExpression(argument)) argument = argument.expression;
    if (guard && argument && ts.isIdentifier(argument) && !node.questionDotToken &&
        !gate.assignedNames().has(argument.text) && gate.readCannotThrow(argument) &&
        !gate.libraryValues.has(gate.span(argument).join(":")))
      return { k: "tagMember", pos: gate.span(node), domain: guard.domain, field: guard.field,
        tags: guard.tags.map((t): Atom => typeof t === "number" ? { a: "numberlit", v: String(t) } : { a: "stringlit", v: t }),
        onUndefined: guard.onUndefined,
        e: { k: "id", pos: gate.span(argument), name: gate.local(argument) } };
    if (guard && argument && !ts.isIdentifier(argument) && !node.questionDotToken)
      return { k: "tagMember", pos: gate.span(node), domain: guard.domain, field: guard.field,
        tags: guard.tags.map((t): Atom => typeof t === "number" ? { a: "numberlit", v: String(t) } : { a: "stringlit", v: t }),
        onUndefined: guard.onUndefined,
        e: gate.expr(argument) };
    // `Promise.resolve(v)` and the like, which the overlay reads as a call
    // of the intrinsic stating the same step, read at the member's name.
    const intrinsic = gate.globalIntrinsics.get(gate.span(node).join(":"));
    if (intrinsic && ts.isPropertyAccessExpression(node.expression))
      return gate.intrinsic(intrinsic, gate.span(node), gate.span(node.expression.name),
        node.arguments.map(a => gate.expr(a)));
    // `Error(m)`, which the overlay reads as the global's construct: the
    // host runs `new Error(m)`.
    if (gate.globalConstructs.has(gate.span(node).join(":")))
      return { k: "new", pos: gate.span(node), callee: gate.expr(node.expression),
        args: node.arguments.map(a => gate.expr(a)) };
    // `Object.assign` of the global `Object` is the intrinsic only where
    // TypeScript binds both names to the standard library alone: a
    // declaration augmenting `ObjectConstructor.assign` states another
    // contract, which no global value carries here.
    if (ts.isPropertyAccessExpression(node.expression) &&
        gate.assignObjects.has(gate.span(node.expression.expression).join(":")) &&
        !(gate.libraryName(node.expression.expression) && gate.libraryName(node.expression.name)))
      gate.fail(node, "Object.assign here is not the standard library's alone: a declaration augments it, " +
        "and the fragment reads Object.assign only as the standard intrinsic");
    if (
      ts.isPropertyAccessExpression(node.expression) &&
      node.expression.name.text === "assign" &&
      gate.libraryName(node.expression.expression) && gate.libraryName(node.expression.name)
    ) {
      if (node.questionDotToken || node.expression.questionDotToken)
        gate.fail(node, "an optional call of Object.assign is outside the fragment");
      // The callable form: an arrow and an object literal, at the two type
      // arguments written, or else at the two TypeScript infers.
      const assign = callableAssign(node);
      const callable = assign && (!node.typeArguments || node.typeArguments.length === 2) ? assign : null;
      if (!callable) {
        // Copies onto a target: the target, then each source, copied as
        // it is evaluated. A spread among the arguments names sources
        // known only at run time.
        if (node.arguments.length === 0 || node.arguments.some(ts.isSpreadElement))
          gate.fail(node, "Object.assign needs its target and its sources written as arguments");
        const [target, ...sources] = node.arguments;
        return {
          k: "objectAssign",
          pos: gate.span(node),
          target: gate.expr(target),
          sources: sources.map((a) => gate.expr(a)),
        };
      }
      const { fn, initial } = callable;
      const typeArguments = node.typeArguments;
      const inferred = typeArguments ? null : gate.assignTypes.get(gate.span(node).join(":"));
      if (inferred && !inferred.ok) gate.fail(node, inferred.refused);
      const [functionType, bagType] = inferred?.ok ? [inferred.value.functionType, inferred.value.bagType]
        : typeArguments?.length === 2 ? [gate.typeOf(typeArguments[0]), gate.typeOf(typeArguments[1])]
        : gate.fail(node, "Object.assign's callable form needs its two type arguments");
      // These names either replace an intrinsic used by the lowering or
      // encounter special/non-writable properties on JavaScript functions.
      for (const property of initial.properties) {
        if (
          ts.isPropertyAssignment(property) &&
          ts.isIdentifier(property.name) &&
          [
            "call",
            "bind",
            "apply",
            "name",
            "length",
            "caller",
            "arguments",
            "__proto__",
          ].includes(property.name.text)
        )
          gate.fail(
            property,
            "special function properties are outside callable initialization",
          );
      }
      return {
        k: "withValue",
        pos: gate.span(node),
        fn: gate.expr(fn),
        initial: gate.expr(initial),
        functionType,
        bagType,
      };
    }
    if (
      ts.isPropertyAccessExpression(node.expression) &&
      node.expression.name.text === "apply" &&
      gate.libraryName(node.expression.name)
    ) {
      // Function.prototype.apply reads its list as an array-like: its
      // length, then each index in order. It never iterates the list.
      if (
        node.questionDotToken ||
        node.expression.questionDotToken ||
        node.typeArguments?.length ||
        node.arguments.length === 0 ||
        node.arguments.length > 2 ||
        node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
        !gate.knownLocal(node.expression.expression)
      )
        gate.refuseReceiverForm(node,
          ".apply requires a known local function, an explicit receiver and at most one argument list");
      const list = node.arguments[1];
      // A fresh array literal as the list is its elements: its allocation
      // is unobservable, and `apply` reads back exactly the values it was
      // built from, in order, so the call is the `.call` with them.
      let written: Expression | undefined = list;
      while (written && ts.isParenthesizedExpression(written)) written = written.expression;
      if (written && ts.isArrayLiteralExpression(written) &&
          !written.elements.some((e) => ts.isSpreadElement(e) || ts.isOmittedExpression(e)))
        return {
          k: "callWithReceiver",
          pos: gate.span(node),
          callee: gate.expr(node.expression.expression),
          receiver: gate.expr(node.arguments[0]),
          args: written.elements.map((e) => gate.expr(e)),
        };
      return {
        k: "applyWithReceiver",
        pos: gate.span(node),
        callee: gate.expr(node.expression.expression),
        receiver: gate.expr(node.arguments[0]),
        list: list ? gate.expr(list) : null,
      };
    }
    if (
      ts.isPropertyAccessExpression(node.expression) &&
      ["call", "bind"].includes(node.expression.name.text) &&
      gate.libraryName(node.expression.name)
    ) {
      if (
        node.questionDotToken ||
        node.expression.questionDotToken ||
        node.typeArguments?.length ||
        node.arguments.length === 0 ||
        node.arguments.some((arg) => ts.isSpreadElement(arg)) ||
        !gate.knownLocal(node.expression.expression)
      )
        gate.refuseReceiverForm(node,
          `.${node.expression.name.text} requires a known local function, an explicit receiver and ordinary arguments`);
      return {
        k:
          node.expression.name.text === "bind"
            ? "bindWithReceiver"
            : "callWithReceiver",
        pos: gate.span(node),
        callee: gate.expr(node.expression.expression),
        receiver: gate.expr(node.arguments[0]),
        args: node.arguments.slice(1).map((arg) => gate.expr(arg)),
      };
    }
    if (node.questionDotToken)
      gate.fail(node, "expected an ordinary call, not an optional one");
    // A property reference, parenthesized or not, is a call target that
    // keeps its object as the receiver (EvaluateCall). A copied method is a
    // value, and takes the `apply` form below.
    let target: Expression = node.expression;
    while (ts.isParenthesizedExpression(target)) target = target.expression;
    // `super.m(args)` calls the method the base class's prototype holds,
    // with this method's receiver: that binding's `.call(this, args)`.
    if (ts.isPropertyAccessExpression(target) && target.expression.kind === ts.SyntaxKind.SuperKeyword) {
      const binding = ts.isIdentifier(target.name) ? gate.superClass?.methods.get(target.name.text) : undefined;
      if (!binding) gate.fail(node, "`super.m(...)` calls a method of the base class's prototype");
      if (node.typeArguments?.length || node.arguments.some((arg) => ts.isSpreadElement(arg)))
        gate.fail(node, "a `super.m(...)` call takes ordinary arguments");
      if (gate.receiverMode !== "strict") gate.fail(node, "`super` where no receiver is bound");
      return { k: "callWithReceiver", pos: gate.span(node),
        callee: { k: "id", pos: gate.span(target), name: binding },
        receiver: { k: "this", pos: gate.span(target.expression) },
        args: node.arguments.map((arg) => gate.expr(arg)) };
    }
    // A static method is not read from its class but bound on its own, so
    // its call is a plain call: its body reads no receiver it is given. A
    // static field is the class value's, and a call of it a method call.
    const staticOwner = ts.isPropertyAccessExpression(target) ? gate.staticReads.get(gate.span(target.name).join(":")) : undefined;
    const isStatic = ts.isPropertyAccessExpression(target) &&
      ((staticOwner !== undefined && !staticFieldOf(gate.file, staticOwner, target.name.text)) ||
        gate.staticPrivate(target) !== null);
    // A call of a static field passes the class value as its receiver,
    // which a static initializer has not yet.
    if (staticOwner !== undefined && !isStatic && gate.staticInitOf(target)?.cls === staticOwner)
      gate.fail(node, STATIC_INIT_CLASS);
    // `s.m(o, …)`, a string method dispatching to its object argument's
    // well-known-symbol method: `%Dispatch:m%(s, o, …)`, evaluated as
    // written (`regexp.mts`), the intrinsic read at the member's name.
    const dispatch = gate.dispatches.get(gate.span(node).join(":"));
    if (dispatch && ts.isPropertyAccessExpression(target)) {
      if (node.arguments.some((arg) => ts.isSpreadElement(arg)) || node.typeArguments?.length)
        gate.fail(node, "a string method dispatching to a regex takes ordinary arguments");
      return gate.intrinsic(dispatch, gate.span(node), gate.span(target.name),
        [gate.expr(target.expression), ...node.arguments.map((arg) => gate.expr(arg))]);
    }
    // A namespace member's call is a call of the binding it reads; the
    // declaration graph refuses one whose callee states its receiver.
    if (
      (ts.isPropertyAccessExpression(target) && !isStatic && gate.namespaceMember(target) === undefined) ||
      ts.isElementAccessExpression(target)
    ) {
      const spreads: number[] = [];
      const args = node.arguments.map((arg, i) => {
        if (!ts.isSpreadElement(arg)) return gate.expr(arg);
        spreads.push(i);
        return gate.spreadOperand(arg);
      });
      // Explicit type arguments instantiate the method's leading binders;
      // Lean checks the claimed instance against them.
      const typeArgs = node.typeArguments?.map((t) => gate.typeOf(t, node));
      return {
        k: "invoke",
        pos: gate.span(node),
        callee: gate.expr(node.expression),
        args,
        ...(spreads.length ? { spreads } : {}),
        ...(typeArgs?.length ? { typeArgs } : {}),
      };
    }
    // A spread writes the elements of one array in place of several
    // arguments, read where it is written: after every argument before it
    // and before every one after it. What it stands for — a tuple's
    // required positions, or elements a variadic callee collects — the
    // checker reads from the claims.
    const spreads: number[] = [];
    const args = node.arguments.map((arg, i) => {
      if (!ts.isSpreadElement(arg)) return gate.expr(arg);
      spreads.push(i);
      return gate.spreadOperand(arg);
    });
    // Explicit type arguments state the callee's instance; Lean checks the
    // claimed instance against them, as for a method call.
    const typeArgs = node.typeArguments?.map((t) => gate.typeOf(t, node));
    return {
      k: "apply",
      pos: gate.span(node),
      callee: gate.expr(node.expression),
      args,
      ...(spreads.length ? { spreads } : {}),
      ...(typeArgs?.length ? { typeArgs } : {}),
    };
  }

  gate.fail(
    node,
    `expression outside the fragment (${ts.SyntaxKind[node.kind]})`,
  );
}

/** An object literal's fields, in order: each property's key and value.
 * A key is its identifier, its string, or its number's `ToString`
 * (`{0: x}` owns `"0"`). A method is an ordinary function expression in a
 * field: it has no `super` or construction here, which is all that tells
 * them apart. `{ x }` is `{ x: x }`, the name read where it is written. A
 * spread of an object literal is its fields, in place: evaluated where
 * written, owning exactly those keys (SOURCE-MODEL.md, "Object literals"). A
 * spread of any other value is a part of its own, copied where written
 * (SOURCE-MODEL.md, "Object literals"). A key is written once: a later field
 * over an earlier one is refused, as in a literal without spreads. */
export function objectFields(this: Gate, node: ts.ObjectLiteralExpression, seen: Set<string>): Within<{ value: "any"; store: "grow" }, ObjectPart[]> {
  const gate: Gate = this;
  // A computed key whose expression, a name or a member read, TypeScript
  // types as one string or number literal is the key that literal spells:
  // the expression is evaluated first, checked at the literal, then the
  // value (ECMA-262, PropertyDefinitionEvaluation; SOURCE-MODEL.md, "Object
  // literals").
  const literalKey = (name: Node): { key: string; check: () => Expr } | null => {
    if (!ts.isComputedPropertyName(name)) return null;
    const result = gate.symbolNames.get(gate.span(name.expression).join(":"));
    if (result === undefined || !result.ok || typeof result.value === "number") return null;
    const { literal, value } = result.value;
    const span = gate.span(name.expression);
    return { key: literal, check: () => ({ k: "cast", pos: gate.span(name), cast: "satisfies",
      annot: literalTerm(value, span), e: gate.expr(name.expression) }) };
  };
  // The key's check, then the value, evaluated in that order.
  const valued = (name: Node, value: () => Expr): Expr => {
    const literal = literalKey(name);
    if (!literal) return value();
    const left = literal.check();
    const right = value();
    return { k: "comma", pos: right.pos, left, right };
  };
  const key = (f: Node, name: Node): PropertyKey => {
    const literal = literalKey(name);
    if (literal) {
      if (seen.has(literal.key)) gate.fail(f, "duplicate field name in a record");
      if (literal.key === "__proto__") gate.fail(f, "prototype initializers are outside the fragment");
      seen.add(literal.key);
      return literal.key;
    }
    // A computed key naming a `unique symbol` constant, such as the
    // well-known `Symbol.iterator`, is that symbol's key: evaluating the
    // name has no effect, and TypeScript decides which symbol it is.
    if (ts.isComputedPropertyName(name)) {
      const symbol = gate.writtenSymbol(name, f);
      if (symbol === null)
        return gate.fail(f, "a computed key in an object literal other than a `unique symbol` constant or a name or member read TypeScript types as one string or number literal is outside the fragment: an allocation's keys are the property names the literal spells, and a key computed at run time is none of them");
      const text = `[symbol ${symbol}]`;
      if (seen.has(text)) gate.fail(f, "duplicate field name in a record");
      seen.add(text);
      return { symbol };
    }
    const text = ts.isIdentifier(name) || ts.isStringLiteral(name) ? name.text
      : ts.isNumericLiteral(name) ? numericKey(name.text)
      : gate.fail(f, "expected a plain property name");
    if (seen.has(text)) gate.fail(f, "duplicate field name in a record");
    if (text === "__proto__") gate.fail(f, "prototype initializers are outside the fragment");
    seen.add(text);
    return text;
  };
  return node.properties.flatMap((f) => {
    // A field whose key a literal-typed computed key spells is marked, for
    // Lean to compare the key with the literal it checks.
    const field = (name: Node, part: ObjectPart & { name: PropertyKey }): ObjectPart[] =>
      [literalKey(name) ? { ...part, computed: true } : part];
    if (ts.isMethodDeclaration(f)) return field(f.name, { name: key(f, f.name), e: valued(f.name, () => gate.lambda(f)) });
    if (ts.isShorthandPropertyAssignment(f) && !f.objectAssignmentInitializer && ts.isIdentifier(f.name))
      return [{ name: key(f, f.name), e: gate.expr(f.name) }];
    if (ts.isPropertyAssignment(f)) {
      const name = key(f, f.name);
      return field(f.name, { name, e: valued(f.name, () => gate.expr(f.initializer)) });
    }
    if (ts.isSpreadAssignment(f)) {
      let operand: Expression = f.expression;
      while (ts.isParenthesizedExpression(operand)) operand = operand.expression;
      if (ts.isObjectLiteralExpression(operand)) return gate.objectFields(operand, seen);
      // A spread of a value copies its own enumerable properties when it
      // is evaluated; which it has is its type's to say, and Lean's.
      return [{ spread: gate.expr(f.expression) }];
    }
    if (ts.isGetAccessorDeclaration(f) || ts.isSetAccessorDeclaration(f))
      return gate.fail(f, "an accessor runs code where its property is read or written; the heap model has data properties only");
    return gate.fail(f, "expected a plain property; no accessors, methods or spreads");
  });
}

/** An optional chain: `r?.x` evaluates `r` once and is `undefined` where it
 * is null or undefined, else the rest of the chain on its value, which the
 * body reads as the variable `CHAIN` at the `?.` token. A link after the
 * chain's `?.` (`.c` in `r?.b.c`) extends the body, so it is skipped with
 * the rest; a second `?.` tests the chain so far, whose `undefined` it
 * passes on, as JavaScript's short-circuit does. The body's nodes span from
 * the `?.` token, so each has a claim site of its own. On a `null` or
 * `undefined` literal the chain is that literal, then `undefined`: its
 * body never runs. */
export function optionalChain(this: Gate, 
  node: ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression | ts.NonNullExpression,
): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  const question = ts.isNonNullExpression(node) ? undefined : node.questionDotToken;
  if (question) {
    const at = gate.span(question);
    const receiver = gate.expr(node.expression);
    if (receiver.k === "lit" && (receiver.lit.a === "null" || receiver.lit.a === "undefined"))
      return { k: "comma", pos: gate.span(node), left: receiver, right: { k: "lit", pos: at, lit: { a: "undefined" } } };
    const saved: Expr = { k: "id", pos: at, name: CHAIN };
    return { k: "optional", pos: gate.span(node), at, receiver, body: gate.chainLink(node, saved, [at[0], node.end]) };
  }
  const chain = gate.expr(node.expression);
  if (chain.k === "comma") return { ...chain, pos: gate.span(node) };
  if (chain.k !== "optional") gate.fail(node, "a link of an optional chain without its `?.`");
  return { ...chain, pos: gate.span(node), body: gate.chainLink(node, chain.body, [chain.at[0], node.end]) };
}

/** One link of an optional chain applied to `object`, the chain so far. */
export function chainLink(this: Gate, 
  node: ts.PropertyAccessExpression | ts.ElementAccessExpression | ts.CallExpression | ts.NonNullExpression,
  object: Expr,
  pos: Span,
): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  if (ts.isNonNullExpression(node)) return { k: "cast", pos, cast: "nonNull", annot: null, e: object };
  if (ts.isPropertyAccessExpression(node)) {
    if (gate.staticReads.has(gate.span(node.name).join(":")) || gate.staticPrivate(node) !== null)
      gate.fail(node, "an optional read of a static member is outside the fragment");
    return { k: "read", pos, field: gate.memberKey(node.name), e: object };
  }
  if (ts.isElementAccessExpression(node)) {
    const [start, end] = gate.span(node.argumentExpression);
    const symbol = gate.symbolKeys.get(`${start}:${end}`);
    if (symbol !== undefined) return { k: "read", pos, field: { symbol }, e: object };
    return { k: "index", pos, e: object, key: gate.expr(node.argumentExpression) };
  }
  let target: Expression = node.expression;
  while (ts.isParenthesizedExpression(target)) target = target.expression;
  // `o.m?.(a)` reads `o.m` once, the chain's tested value, and calls it with
  // `o` as its receiver (ECMA-262, OptionalChain: the reference's base is the
  // call's `this`): the call of the tested value with the receiver read
  // again, which is the value read before where `o` is `this` or a name
  // whose read cannot throw nor run code and that the file assigns nowhere.
  if (node.questionDotToken && ts.isElementAccessExpression(target))
    gate.fail(node, "an optional call of a method read at a computed key is outside the fragment");
  if (node.questionDotToken && ts.isPropertyAccessExpression(target)) {
    let base: Expression = target.expression;
    while (ts.isParenthesizedExpression(base)) base = base.expression;
    // The receiver read again is claimed at the method's name, a site of
    // its own.
    const at = gate.span(target.name);
    const receiver: Expr | null = base.kind === ts.SyntaxKind.ThisKeyword ? { k: "this", pos: at }
      : ts.isIdentifier(base) && !gate.assignedNames().has(base.text) && gate.readCannotThrow(base) &&
        !gate.libraryValues.has(gate.span(base).join(":")) ? { k: "id", pos: at, name: gate.local(base) }
      : null;
    if (!receiver)
      gate.fail(node, "an optional call of a method whose object is other than `this` or a name read without effect and never assigned is outside the fragment: the object is read once, and again as the call's receiver");
    if (node.arguments.some(ts.isSpreadElement) || node.typeArguments?.length)
      gate.fail(node, "an optional call of a method takes ordinary arguments");
    return { k: "callWithReceiver", pos, callee: object, receiver, args: node.arguments.map((arg) => gate.expr(arg)) };
  }
  const spreads: number[] = [];
  const args = node.arguments.map((arg, i) => {
    if (!ts.isSpreadElement(arg)) return gate.expr(arg);
    spreads.push(i);
    return gate.spreadOperand(arg);
  });
  const method = !node.questionDotToken && (object.k === "read" || object.k === "index");
  const typeArgs = node.typeArguments?.map((t) => gate.typeOf(t, node));
  if (typeArgs?.length && !method)
    gate.fail(node, "explicit type arguments are admitted on a method call only");
  return {
    k: method ? "invoke" : "apply",
    pos,
    callee: object,
    args,
    ...(spreads.length ? { spreads } : {}),
    ...(method && typeArgs?.length ? { typeArgs } : {}),
  };
}

// A call signature alone does not establish the inherited .call intrinsic.
// Follow immutable lexical aliases to source-created functions, and to a
// function-valued member of a `const` object literal whose member no write
// in the file can replace. Parameters and arbitrary call results may carry
// their own .call property, so are refused.
/** `f.call(r, …)`, `.apply` or `.bind` of what is no known local
 * function. Of a method TypeScript resolves the member to, the form passes
 * it a receiver other than its host, where a method's contract is relative
 * to its host: extraction, refused by that reason. */
export function refuseReceiverForm(this: Gate, node: ts.CallExpression, refusal: string): never {
  const gate: Gate = this;
  const form = ts.isPropertyAccessExpression(node.expression) ? node.expression.name.text : "call";
  let target: Expression = ts.isPropertyAccessExpression(node.expression) ? node.expression.expression : node.expression;
  while (ts.isParenthesizedExpression(target)) target = target.expression;
  if (ts.isPropertyAccessExpression(target) && gate.methodTargets.has(gate.span(target.name).join(":")))
    gate.fail(node, `a method read off its object is not a function value: \`.${form}\` passes it a receiver ` +
      "other than the object it is read from, and a method's contract is relative to that object " +
      "(DESIGN.md, \"Method members are host-relative\")");
  gate.fail(node, refusal);
}

/** `localArrow`, and every local it follows is confined: code that may
 * hold the local's value cannot have replaced the member or added an own
 * `call`, `apply` or `bind`. */
export function knownLocal(this: Gate, node: Expression): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  const seen = new Set<number>();
  const followed = new Set<string>();
  const functions = new Set<Node>();
  return gate.localArrow(node, seen, followed, functions) && gate.confined(seen, followed, functions);
}

/** The declaration a name resolves to, lexically: the nearest scope
 * enclosing the reference that binds it (`bindingScope`), a parameter
 * before a named function expression's own name; none for a global. */
export function resolve(this: Gate, id: Identifier): Within<{ value: "any"; store: "grow" }, Node | undefined> {
  const gate: Gate = this;
  let table = gate.bindings;
  if (table === null) {
    const bindings = new Map<Node, Map<string, Node>>();
    const visit = (n: Node): void => {
      if (ts.isTypeNode(n) || ts.isInterfaceDeclaration(n) || ts.isTypeAliasDeclaration(n)) return;
      const name = nameOf(n);
      if ((ts.isParameterDeclaration(n) || ts.isVariableDeclaration(n) || ts.isBindingElement(n) ||
           ts.isFunctionDeclaration(n) || ts.isClassDeclaration(n) || ts.isEnumDeclaration(n) ||
           ts.isFunctionExpression(n) || ts.isClassExpression(n) || ts.isImportSpecifier(n) ||
           ts.isNamespaceImport(n) || ts.isImportClause(n)) && name && ts.isIdentifier(name)) {
        const scope = ts.isImportSpecifier(n) || ts.isNamespaceImport(n) || ts.isImportClause(n)
          ? gate.file : bindingScope(n);
        const own = ts.isFunctionExpression(n) || ts.isClassExpression(n);
        const names = bindings.get(scope) ?? new Map<string, Node>();
        bindings.set(scope, names);
        const before = names.get(name.text);
        if (!before || (!own && (ts.isFunctionExpression(before) || ts.isClassExpression(before))))
          names.set(name.text, n);
      }
      n.forEachChild(visit);
    };
    visit(gate.file);
    table = bindings;
    gate.bindings = bindings;
  }
  for (let at: Node | undefined = id.parent; at; at = at.parent) {
    const found = table.get(at)?.get(id.text);
    if (found) return found;
  }
  return undefined;
}

/** Whether the values followed are confined: code holding one is the
 * file's own, whose writes `memberMayBeWritten` reads. Every reference to
 * a local declared at `seen`, or to one of the file's function
 * declarations in `functions` (a reference resolved to it, `resolve`), is
 * the callee of a call, the object of `.call`, `.apply` or `.bind`
 * (directly or through a member), the target of a plain assignment to it,
 * the object of a read or write, not a call, of a member other than
 * `call`, `apply`, `bind` and the members `followed`, or a local's value: a
 * local's initializer or the right side of a plain assignment to it, the
 * reference itself, or a spread or member value in an object literal that
 * is. Such a local is confined in turn, and the member it is given at is
 * followed. Any other reference (an argument, `Object.assign`'s target, a
 * method call's receiver, a return, a read of a followed member) may hand
 * the value to code that replaces its member or adds a `call` of its own.
 * An object literal a local holds has no accessor: a spread of it runs its
 * getters with the object as receiver. */
export function confined(this: Gate, seen: Set<number>, followed: Set<string>, functions: Set<Node>): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  const targets = new Set<Node>(functions);
  const declared = new Map<number, ts.VariableDeclaration>();
  const collect = (n: Node): void => {
    if (ts.isVariableDeclaration(n)) declared.set(n.getStart(gate.file), n);
    n.forEachChild(collect);
  };
  collect(gate.file);
  for (const start of seen) {
    const decl = declared.get(start);
    if (decl) targets.add(decl);
  }
  const strip = (n: Node): Node => {
    let at = n;
    while (ts.isParenthesizedExpression(at.parent)) at = at.parent;
    return at;
  };
  const hasAccessor = (literal: Node): boolean => ts.isObjectLiteralExpression(literal) &&
    literal.properties.some((p) => ts.isGetAccessorDeclaration(p) || ts.isSetAccessorDeclaration(p));
  // The local whose value `value` is: its initializer, or the right side
  // of a plain assignment to it.
  const holderOf = (value: Node): Node | undefined => {
    const at = strip(value);
    const holder = at.parent;
    if (ts.isVariableDeclaration(holder) && holder.initializer === at) return holder;
    if (ts.isBinaryExpression(holder) && holder.right === at &&
        holder.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
      let left: Expression = holder.left;
      while (ts.isParenthesizedExpression(left)) left = left.expression;
      const target = ts.isIdentifier(left) ? gate.resolve(left) : undefined;
      return target && ts.isVariableDeclaration(target) ? target : undefined;
    }
    return undefined;
  };
  const gateCallee = (access: Node): boolean => {
    if (!ts.isPropertyAccessExpression(access) || !["call", "apply", "bind"].includes(access.name.text))
      return false;
    const call = strip(access).parent;
    return ts.isCallExpression(call) && call.expression === strip(access);
  };
  const allowed = (n: Identifier): boolean => {
    const at = strip(n);
    const parent = at.parent;
    if (ts.isCallExpression(parent) && parent.expression === at) return true;
    if (ts.isPropertyAccessExpression(parent) && parent.expression === at) {
      if (gateCallee(parent)) return true;
      const outer = strip(parent).parent;
      if (ts.isPropertyAccessExpression(outer) && outer.expression === strip(parent) && gateCallee(outer))
        return true;
      // Another member, read or written, not called: its value is not one
      // followed, and the object is not handed on.
      const key = parent.name.text;
      return !followed.has(key) && !["call", "apply", "bind"].includes(key) &&
        !((ts.isCallExpression(outer) || ts.isNewExpression(outer)) && outer.expression === strip(parent)) &&
        !ts.isTaggedTemplateExpression(outer);
    }
    if (ts.isBinaryExpression(parent) && parent.left === at &&
        parent.operatorToken.kind === ts.SyntaxKind.EqualsToken) return true;
    let value: Node = at;
    if (ts.isSpreadAssignment(parent) || ts.isShorthandPropertyAssignment(parent) ||
        (ts.isPropertyAssignment(parent) && parent.initializer === at)) {
      if (!ts.isSpreadAssignment(parent)) {
        if (!ts.isIdentifier(parent.name)) return false;
        followed.add(parent.name.text);
      }
      value = parent.parent;
    }
    const holder = holderOf(value);
    if (!holder || hasAccessor(value)) return false;
    targets.add(holder);
    return true;
  };
  // A declaration's own name, or a member's: no reference.
  const isName = (n: Identifier): boolean => {
    const parent = n.parent;
    return (ts.isPropertyAccessExpression(parent) && parent.name === n) ||
      (ts.isQualifiedName(parent) && parent.right === n) ||
      ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent) ||
        ts.isPropertyDeclaration(parent) || ts.isGetAccessorDeclaration(parent) ||
        ts.isSetAccessorDeclaration(parent) || ts.isVariableDeclaration(parent) ||
        ts.isParameterDeclaration(parent) || ts.isBindingElement(parent) ||
        ts.isFunctionDeclaration(parent) || ts.isFunctionExpression(parent) ||
        ts.isClassDeclaration(parent) || ts.isClassExpression(parent)) && nameOf(parent) === n);
  };
  // A local or member followed late may have been referenced before:
  // repeat until neither grows.
  for (let size = -1; size !== targets.size + followed.size;) {
    size = targets.size + followed.size;
    let ok = true;
    const visit = (n: Node): void => {
      // A type names no value.
      if (!ok || ts.isTypeNode(n)) return;
      if (ts.isIdentifier(n) && !isName(n)) {
        const target = gate.resolve(n);
        if (target && targets.has(target) && !allowed(n)) ok = false;
      }
      n.forEachChild(visit);
    };
    visit(gate.file);
    if (!ok) return false;
    for (const target of targets)
      if (ts.isVariableDeclaration(target) &&
          (!ts.isIdentifier(target.name) || (target.initializer && hasAccessor(target.initializer))))
        return false;
  }
  return true;
}

export function localArrow(this: Gate, node: Expression, seen: Set<number> = new Set(), followed: Set<string> = new Set(),
    functions: Set<Node> = new Set()): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  if (ts.isParenthesizedExpression(node))
    return gate.localArrow(node.expression, seen, followed, functions);
  if (ts.isArrowFunction(node) || ts.isFunctionExpression(node)) return true;
  if (
    ts.isPropertyAccessExpression(node) &&
    !node.questionDotToken &&
    ts.isIdentifier(node.expression)
  ) {
    // A member of a local every value of which is an object literal that
    // gives the member a known function, which no write in the file can
    // replace.
    const member = node.name.text;
    if (gate.memberMayBeWritten(member)) return false;
    followed.add(member);
    const values = gate.localValues(node.expression, seen);
    return !!values && values.every((v) => gate.memberOf(v, member, seen, followed, functions) === true);
  }
  if (
    ts.isCallExpression(node) &&
    ts.isPropertyAccessExpression(node.expression) &&
    node.expression.name.text === "assign" &&
    gate.libraryName(node.expression.expression) && gate.libraryName(node.expression.name)
  )
    // Its initializer is separately parsed through the full Object.assign
    // gate. Do not parse it again here: its body may refer back to this name.
    return (
      node.arguments.length === 2 &&
      ts.isArrowFunction(node.arguments[0]) &&
      ts.isObjectLiteralExpression(node.arguments[1])
    );
  if (
    ts.isCallExpression(node) &&
    ts.isPropertyAccessExpression(node.expression) &&
    node.expression.name.text === "bind" &&
    gate.libraryName(node.expression.name)
  )
    return gate.localArrow(node.expression.expression, seen, followed, functions);
  if (!ts.isIdentifier(node)) return false;
  const values = gate.localValues(node, seen);
  if (values) return values.every((v) => gate.localArrow(v, seen, followed, functions));
  const declaration = gate.resolve(node);
  if (!declaration || !gate.moduleFunction(node)) return false;
  functions.add(declaration);
  return true;
}

/** What the object literal `value` holds at `member` once built: `true`
 * where the last of its parts giving the key gives a known local function
 * (a method, or a value `localArrow` admits), `"absent"` where no part
 * gives it, `false` where that is not known. A spread gives the key where
 * its source does: a local every value of which is an object literal, or a
 * literal; it copies the own enumerable data properties, which a literal's
 * members are. */
export function memberOf(this: Gate, value: Expression, member: string, seen: Set<number>,
    followed: Set<string>, functions: Set<Node>): Within<{ value: "any"; store: "grow" }, boolean | "absent"> {
  const gate: Gate = this;
  while (ts.isParenthesizedExpression(value)) value = value.expression;
  if (!ts.isObjectLiteralExpression(value)) return false;
  let found: boolean | "absent" = "absent";
  for (const p of value.properties) {
    if (ts.isSpreadAssignment(p)) {
      let source = p.expression;
      while (ts.isParenthesizedExpression(source)) source = source.expression;
      const sources = ts.isIdentifier(source) ? gate.localValues(source, seen)
        : ts.isObjectLiteralExpression(source) ? [source] : undefined;
      if (!sources) return false;
      const parts = sources.map((s) => gate.memberOf(s, member, seen, followed, functions));
      if (parts.every((x) => x === "absent")) continue;
      // A source that may lack the key leaves the earlier part's value.
      found = parts.every((x) => x === true || (x === "absent" && found === true));
      continue;
    }
    if (!p.name || ts.isComputedPropertyName(p.name) || ts.isPrivateIdentifier(p.name)) return false;
    if (p.name.text !== member) continue;
    found = ts.isMethodDeclaration(p) ? true
      : ts.isPropertyAssignment(p) ? gate.localArrow(p.initializer, seen, followed, functions)
      : ts.isShorthandPropertyAssignment(p) ? gate.localArrow(p.name, seen, followed, functions)
      : false;
  }
  return found;
}

/** Whether this identifier resolves to one of the file's function
 * declarations with a body, not exported: an exported one is held by
 * every importer, where other code may give it an own `call`. A script's
 * top-level function is also a property of the global object, which, by
 * the trusted assumption that only the file writes its top-level
 * bindings, no other code writes (DESIGN, Trust surface). No write in the
 * file can replace the `call`, `apply` or `bind` its object inherits (an
 * assignment to the declaration's binding is refused where it is
 * written). */
export function moduleFunction(this: Gate, node: Identifier): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  const declaration = gate.resolve(node);
  if (!declaration || !ts.isFunctionDeclaration(declaration) || !declaration.parent ||
      !ts.isSourceFile(declaration.parent))
    return false;
  const declared = gate.file.statements.filter((s) => {
    const name = nameOf(s);
    return !!name && ts.isIdentifier(name) && name.text === node.text &&
      !ts.isInterfaceDeclaration(s) && !ts.isTypeAliasDeclaration(s);
  });
  return declared.every((s) => ts.isFunctionDeclaration(s) && !!s.body &&
      !s.modifiers?.some((m) => m.kind === ts.SyntaxKind.DeclareKeyword || m.kind === ts.SyntaxKind.ExportKeyword)) &&
    !["call", "apply", "bind"].some((member) => gate.memberMayBeWritten(member));
}

/** Whether any assignment in the file may replace a member of this name: a
 * write to it by name, or to a computed key that is not another name. */
export function memberMayBeWritten(this: Gate, member: string): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  let found = false;
  const visit = (n: Node): void => {
    if (found) return;
    if (
      ts.isBinaryExpression(n) &&
      n.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
      n.operatorToken.kind <= ts.SyntaxKind.LastAssignment
    ) {
      let target: Expression = n.left;
      while (ts.isParenthesizedExpression(target)) target = target.expression;
      if (
        ts.isPropertyAccessExpression(target) &&
        target.name.text === member
      )
        found = true;
      if (
        ts.isElementAccessExpression(target) &&
        !(
          ts.isStringLiteral(target.argumentExpression) &&
          target.argumentExpression.text !== member
        )
      )
        found = true;
    }
    n.forEachChild(visit);
  };
  visit(gate.file);
  return found;
}

/** Every value the local this identifier names may hold, lexically: a
 * `const`'s initializer; a `let`'s initializer and the right side of each
 * plain assignment to it in its block, the only places a write to it can
 * be. None where it names a parameter, something declared elsewhere, or a
 * `let` that is written otherwise (a compound assignment, an update, a
 * pattern, a loop head) or whose name a declaration inside its block
 * shadows. */
export function localValues(this: Gate, 
  node: Identifier,
  seen: Set<number>,
): Within<{ value: "any"; store: "grow" }, Expression[] | undefined> {
  const gate: Gate = this;
  const decl = gate.resolve(node);
  if (!decl || !ts.isVariableDeclaration(decl) || !ts.isIdentifier(decl.name) || !decl.initializer)
    return undefined;
  const list = decl.parent;
  const statement = list?.parent;
  if (!list || ts.isCatchClause(list) || !statement || !ts.isVariableStatement(statement) ||
      !statement.parent || !ts.isBlock(statement.parent))
    return undefined;
  if (seen.has(decl.getStart(gate.file))) return undefined;
  seen.add(decl.getStart(gate.file));
  if (list.flags & ts.NodeFlags.Const) return [decl.initializer];
  if (!(list.flags & ts.NodeFlags.Let)) return undefined;
  return gate.letWrites(statement.parent, decl.name);
}

/** The values the `let` declared at `declared` in `block` is given: its
 * initializer and each plain assignment's right side; none where another
 * form writes it or a declaration in the block shadows it. */
export function letWrites(this: Gate, block: ts.Block, declared: Identifier): Within<{ value: "any"; store: "grow" }, Expression[] | undefined> {
  const name = declared.text;
  const values: Expression[] = [];
  let unknown = false;
  const outermost = (n: Node): Node => {
    let at = n;
    while (ts.isParenthesizedExpression(at.parent) || ts.isArrayLiteralExpression(at.parent) ||
        ts.isObjectLiteralExpression(at.parent) || ts.isSpreadElement(at.parent) ||
        ts.isSpreadAssignment(at.parent) || ts.isPropertyAssignment(at.parent) ||
        ts.isShorthandPropertyAssignment(at.parent))
      at = at.parent;
    return at;
  };
  const visit = (n: Node): void => {
    if (unknown) return;
    // Another declaration of the name inside the block: refused rather
    // than resolved.
    const declaredName = n === declared.parent ? undefined
      : ts.isVariableDeclaration(n) || ts.isParameterDeclaration(n) || ts.isBindingElement(n) ||
        ts.isFunctionDeclaration(n) || ts.isFunctionExpression(n) ||
        ts.isClassDeclaration(n) || ts.isClassExpression(n) ? n.name : undefined;
    if (declaredName && ts.isIdentifier(declaredName) && declaredName.text === name) {
      unknown = true;
      return;
    }
    if (ts.isIdentifier(n) && n !== declared && n.text === name) {
      const parent = n.parent;
      if (ts.isPropertyAccessExpression(parent) && parent.name === n) return;
      if ((ts.isPropertyAssignment(parent) || ts.isMethodDeclaration(parent)) && parent.name === n) return;
      const top = outermost(n);
      const holder = top.parent;
      if (ts.isBinaryExpression(holder) && holder.left === top &&
          holder.operatorToken.kind >= ts.SyntaxKind.FirstAssignment &&
          holder.operatorToken.kind <= ts.SyntaxKind.LastAssignment) {
        if (outermostIs(top, n) && holder.operatorToken.kind === ts.SyntaxKind.EqualsToken)
          values.push(holder.right);
        else unknown = true;
      } else if ((ts.isPrefixUnaryExpression(holder) || ts.isPostfixUnaryExpression(holder)) &&
          (holder.operator === ts.SyntaxKind.PlusPlusToken || holder.operator === ts.SyntaxKind.MinusMinusToken)) {
        unknown = true;
      } else if ((ts.isForOfStatement(holder) || ts.isForInStatement(holder)) && holder.initializer === top) {
        unknown = true;
      }
    }
    n.forEachChild(visit);
  };
  const outermostIs = (top: Node, n: Node): boolean => {
    let at: Node = top;
    while (ts.isParenthesizedExpression(at)) at = at.expression;
    return at === n;
  };
  const decl = declared.parent;
  if (!ts.isVariableDeclaration(decl) || !decl.initializer) return undefined;
  values.push(decl.initializer);
  visit(block);
  return unknown ? undefined : values;
}

/** A compound assignment or an increment: the target's parts are evaluated
 * once, so the verifier is handed one form rather than a rewrite that would
 * evaluate an effectful key twice. */
export function update(this: Gate, 
  node: Expression,
  target: Expression,
  token: ts.SyntaxKind,
  rhs: Expression | null,
  post: boolean,
): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  const ops: Record<number, ArithOp> = {
    [ts.SyntaxKind.PlusEqualsToken]: "add",
    [ts.SyntaxKind.MinusEqualsToken]: "sub",
    [ts.SyntaxKind.AsteriskEqualsToken]: "mul",
    [ts.SyntaxKind.SlashEqualsToken]: "div",
    [ts.SyntaxKind.AsteriskAsteriskEqualsToken]: "pow",
    [ts.SyntaxKind.PercentEqualsToken]: "rem",
    [ts.SyntaxKind.AmpersandEqualsToken]: "bitAnd",
    [ts.SyntaxKind.BarEqualsToken]: "bitOr",
    [ts.SyntaxKind.CaretEqualsToken]: "xor",
    [ts.SyntaxKind.LessThanLessThanEqualsToken]: "shl",
    [ts.SyntaxKind.GreaterThanGreaterThanEqualsToken]: "shr",
    [ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken]: "ushr",
    [ts.SyntaxKind.PlusPlusToken]: "add",
    [ts.SyntaxKind.MinusMinusToken]: "sub",
  };
  const op = ops[token];
  if (!op)
    gate.fail(
      node,
      `binary operator outside the fragment (${ts.tokenToString(token)})`,
    );
  const lhs = gate.expr(target);
  if (lhs.k !== "id" && lhs.k !== "read" && lhs.k !== "index")
    gate.fail(target, "only field and local assignments are supported");
  return {
    k: "update",
    pos: gate.span(node),
    op,
    target: lhs,
    rhs: rhs ? gate.expr(rhs) : null,
    post,
  };
}

/** A template literal is the concatenation of its parts, in order:
 * `` `h${a}m${b}t` `` is `(((("h" + a) + "m") + b) + "t")`, which converts
 * each substitution by `ToString` where the template does, after the ones
 * before it; the first part, a string, makes every `+` a concatenation.
 * Each partial concatenation spans from the template's start to the end of
 * its last part, so every node has a span of its own and the whole has the
 * template's. */
export function template(this: Gate, node: ts.TemplateExpression): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  const start = node.getStart(gate.file);
  let acc: Expr = { k: "lit", pos: gate.span(node.head), lit: { a: "stringlit", v: node.head.text } };
  for (const part of node.templateSpans) {
    acc = { k: "arith", pos: [start, part.expression.end], op: "add", l: acc, r: gate.expr(part.expression) };
    acc = {
      k: "arith",
      pos: [start, part.literal.end],
      op: "add",
      l: acc,
      r: { k: "lit", pos: gate.span(part.literal), lit: { a: "stringlit", v: part.literal.text } },
    };
  }
  return acc;
}

/** Whether an `instanceof` right operand names a class of this file that
 * declares or inherits, from a class of this file, a static
 * `[Symbol.hasInstance]`. Syntactic: it only chooses a refusal's reason. */
export function hasInstanceClass(this: Gate, right: Expression): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  return gate.hasInstanceAlong(ts.isIdentifier(right) ? right.text : undefined) !== null;
}

/** The class, of those the file declares at its top level, along `name`'s
 * chain of bases whose static `[Symbol.hasInstance]` method `instanceof`
 * of `name` calls: the nearest declaring one, which a derived class
 * inherits through its constructor's prototype chain. Syntactic up to the
 * key, which `staticHasInstance` resolves. */
export function hasInstanceAlong(this: Gate, name: string | undefined): Within<{ value: "any"; store: "grow" }, { cls: string; member: ts.MethodDeclaration } | null> {
  const gate: Gate = this;
  const classes = new Map<string, ClassDeclaration>();
  for (const s of gate.file.statements)
    if (ts.isClassDeclaration(s) && s.name) classes.set(s.name.text, s);
  const seen = new Set<string>();
  while (name && !seen.has(name)) {
    seen.add(name);
    const c = classes.get(name);
    if (!c) return null;
    const member = c.members.find((m): m is ts.MethodDeclaration => ts.isMethodDeclaration(m) &&
      ts.isComputedPropertyName(m.name) && !!m.modifiers?.some((k) => k.kind === ts.SyntaxKind.StaticKeyword) &&
      m.name.expression.getText(gate.file) === "Symbol.hasInstance");
    if (member) return { cls: name, member };
    const base = c.heritageClauses?.find((h) => h.token === ts.SyntaxKind.ExtendsKeyword)?.types[0]?.expression;
    name = base && ts.isIdentifier(base) ? base.text : undefined;
  }
  return null;
}

/** Whether a class member's computed key is the built-in well-known
 * `Symbol.hasInstance`: TypeScript binds it to the standard library's
 * `unique symbol` property of that name (`symbolKeys`). */
export function staticHasInstance(this: Gate, name: ts.PropertyName): Within<{ value: "any"; store: "grow" }, boolean> {
  const gate: Gate = this;
  if (!ts.isComputedPropertyName(name) || !ts.isPropertyAccessExpression(name.expression)) return false;
  const symbol = gate.symbolKeys.get(gate.span(name.expression).join(":"));
  const identity = symbol === undefined ? undefined : gate.symbolIdentities[symbol];
  return !!identity && identity.module.startsWith("typescript/lib/") && identity.name === "hasInstance";
}

export function binary(this: Gate, node: BinaryExpression): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  if (node.operatorToken.kind === ts.SyntaxKind.CommaToken)
    return { k: "comma", pos: gate.span(node), left: gate.expr(node.left), right: gate.expr(node.right) };
  // `e instanceof Array`, which the declaration graph found to name the
  // standard library's global: the same test as `Array.isArray(e)`.
  if (node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword &&
      gate.globalTests.has(gate.span(node).join(":")))
    return { k: "arrayTest", pos: gate.span(node), e: gate.expr(node.left) };
  // `e instanceof Error`, which the overlay reads as a call of the intrinsic
  // stating the Boolean (`%InstanceOf:Error%`): the operand, then the
  // global's read, which runs nothing, then the walk.
  const instanceIntrinsic = node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword
    ? gate.globalIntrinsics.get(gate.span(node).join(":")) : undefined;
  if (instanceIntrinsic)
    return gate.intrinsic(instanceIntrinsic, gate.span(node), gate.span(node.right), [gate.expr(node.left)]);
  // Any other `instanceof` looks for a constructor's prototype along the
  // operand's prototype chain, or calls the constructor's static
  // `[Symbol.hasInstance]`. For a class of this file, which TypeScript binds
  // the right operand to, it evaluates the operand, then reads the class's
  // prototype object, and looks for the key only that object owns along
  // the operand's chain (SOURCE-ELABORATION.md, "`instanceof`").
  if (node.operatorToken.kind === ts.SyntaxKind.InstanceOfKeyword) {
    const cls = gate.classTests.get(gate.span(node.right).join(":"));
    // A class whose chain of constructors holds a static
    // `[Symbol.hasInstance]`: `instanceof` calls that method with the
    // operand and converts its result by `ToBoolean` (ECMA-262,
    // InstanceofOperator), walking no prototype chain. The method reads no
    // `this` (`classBody`), so its receiver, the class, is unobservable,
    // and it is the static binding a plain call reads. Its answer says
    // nothing of the operand's type, so the test narrows nothing.
    const custom = cls ? gate.hasInstanceAlong(cls) : null;
    if (custom && gate.staticHasInstance(custom.member.name)) {
      const keyword = node.operatorToken.getStart(gate.file);
      const callee: Expr = { k: "id", pos: gate.span(node.right), name: staticName(custom.cls, HAS_INSTANCE) };
      const call: Expr = { k: "apply", pos: [node.getStart(gate.file), node.operatorToken.end], callee,
        args: [gate.expr(node.left)] };
      return { k: "not", pos: gate.span(node),
        e: { k: "not", pos: [keyword, keyword + "instanceof".length], e: call } };
    }
    if (gate.hasInstanceClass(node.right))
      gate.fail(node, "`instanceof` of a class with a static `[Symbol.hasInstance]` calls that method, a computed static member, outside the fragment");
    // A right operand whose type states `[Symbol.hasInstance]`:
    // `instanceof` reads that method off it and calls it with the operand,
    // the right operand its receiver, converting the result by
    // `ToBoolean` (ECMA-262, InstanceofOperator). The operands are names,
    // whose reads JavaScript's order and the call's alike leave unchanged.
    if (!cls && gate.hookTests.has(gate.span(node.right).join(":"))) {
      const symbol = gate.symbolIdentities.findIndex((s) =>
        s.module.startsWith("typescript/lib/") && s.name === "hasInstance");
      if (!ts.isIdentifier(node.left) || symbol < 0)
        gate.fail(node, "`instanceof` of a value whose type states `[Symbol.hasInstance]` calls it: its left operand is a name");
      const start = node.getStart(gate.file);
      const keyword = node.operatorToken.getStart(gate.file);
      const keywordEnd = node.operatorToken.end;
      const call: Expr = { k: "invoke", pos: [start, keywordEnd],
        callee: { k: "read", pos: [keyword, node.end], field: { symbol }, e: gate.expr(node.right) },
        args: [gate.expr(node.left)] };
      return { k: "not", pos: gate.span(node), e: { k: "not", pos: [keyword, keywordEnd], e: call } };
    }
    if (!cls)
      gate.fail(node, "`instanceof` whose right operand is not a class declared at the file's top level: nothing in the file says which prototype a constructor from elsewhere gives its instances");
    return { k: "instanceTest", pos: gate.span(node), e: gate.expr(node.left),
      proto: { k: "id", pos: gate.span(node.right), name: gate.ownClass(node.right) ?? prototypeName(cls) },
      key: classKey(cls) };
  }
  // `key in o`: whether `o` has the key, its own or an inherited one.
  // Which keys and operands the model answers as JavaScript does is Lean's
  // to decide (`inKeyRefusal`, `inOperand`, `inKeyList`).
  if (node.operatorToken.kind === ts.SyntaxKind.InKeyword) {
    const key = inKey(node);
    // A key TypeScript types as other than string literals (a number, an
    // array index among them, a symbol, a string known only at run time)
    // names what the model does not answer as JavaScript does: the test is
    // the host's `%HasProperty%(k, o)`, a Boolean that narrows nothing
    // (`intrinsics.mts`), evaluated as `in` evaluates: the key, the object,
    // then the lookup.
    if (gate.hostIns.has(gate.span(key).join(":"))) {
      const keyword = node.operatorToken.getStart(gate.file);
      return gate.intrinsic(hasPropertyName, gate.span(node), [keyword, keyword + "in".length],
        [gate.expr(node.left), gate.expr(node.right)]);
    }
    // `#x in o` asks whether `o` itself holds the slot, as its class's
    // construction installs it; the model's key test walks the prototype
    // chain, and would find an instance's slot from an object inheriting
    // from it.
    if (ts.isPrivateIdentifier(key))
      gate.fail(node.left, "`#x in o` tests an object's own private slot, where the model's key test walks the prototype chain");
    return { k: "inTest", pos: gate.span(node), key: gate.expr(node.left), e: gate.expr(node.right) };
  }
  switch (node.operatorToken.kind) {
    case ts.SyntaxKind.PlusEqualsToken:
    case ts.SyntaxKind.MinusEqualsToken:
    case ts.SyntaxKind.AsteriskEqualsToken:
    case ts.SyntaxKind.SlashEqualsToken:
    case ts.SyntaxKind.AsteriskAsteriskEqualsToken:
    case ts.SyntaxKind.PercentEqualsToken:
    case ts.SyntaxKind.AmpersandEqualsToken:
    case ts.SyntaxKind.BarEqualsToken:
    case ts.SyntaxKind.CaretEqualsToken:
    case ts.SyntaxKind.LessThanLessThanEqualsToken:
    case ts.SyntaxKind.GreaterThanGreaterThanEqualsToken:
    case ts.SyntaxKind.GreaterThanGreaterThanGreaterThanEqualsToken:
      return gate.update(
        node,
        node.left,
        node.operatorToken.kind,
        node.right,
        false,
      );
  }
  const arithmetic: Record<number, BinaryOp> = {
    [ts.SyntaxKind.PlusToken]: "add",
    [ts.SyntaxKind.MinusToken]: "sub",
    [ts.SyntaxKind.AsteriskToken]: "mul",
    [ts.SyntaxKind.SlashToken]: "div",
    [ts.SyntaxKind.AsteriskAsteriskToken]: "pow",
    [ts.SyntaxKind.PercentToken]: "rem",
    // On numbers, through `ToInt32` and `ToUint32`, running no code; the
    // typing admits numbers alone, and `^` two bigints too.
    [ts.SyntaxKind.AmpersandToken]: "bitAnd",
    [ts.SyntaxKind.BarToken]: "bitOr",
    [ts.SyntaxKind.CaretToken]: "xor",
    [ts.SyntaxKind.LessThanLessThanToken]: "shl",
    [ts.SyntaxKind.GreaterThanGreaterThanToken]: "shr",
    [ts.SyntaxKind.GreaterThanGreaterThanGreaterThanToken]: "ushr",
    [ts.SyntaxKind.LessThanToken]: "lt",
    [ts.SyntaxKind.LessThanEqualsToken]: "le",
    [ts.SyntaxKind.GreaterThanToken]: "gt",
    [ts.SyntaxKind.GreaterThanEqualsToken]: "ge",
  };
  const arith = arithmetic[node.operatorToken.kind];
  if (arith)
    return {
      k: "arith",
      pos: gate.span(node),
      op: arith,
      l: gate.expr(node.left),
      r: gate.expr(node.right),
    };
  const logical: Record<number, "nullish" | "or" | "and"> = {
    [ts.SyntaxKind.QuestionQuestionEqualsToken]: "nullish",
    [ts.SyntaxKind.BarBarEqualsToken]: "or",
    [ts.SyntaxKind.AmpersandAmpersandEqualsToken]: "and",
  };
  const logicalOp = logical[node.operatorToken.kind];
  if (logicalOp && (logicalOp !== "nullish" || !ts.isIdentifier(node.left))) {
    const target = gate.expr(node.left);
    if (target.k !== "id" && target.k !== "read" && target.k !== "index")
      gate.fail(node.left, "only field and local assignments are supported");
    if (target.k === "id" && target.name === "undefined")
      gate.fail(node.left, "shadowing undefined is outside the fragment");
    return {
      k: "logicalAssign",
      pos: gate.span(node),
      op: logicalOp,
      target,
      rhs: gate.expr(node.right),
    };
  }
  if (node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionEqualsToken) {
    if (!ts.isIdentifier(node.left) || node.left.text === "undefined")
      gate.fail(node.left, "nullish assignment requires a local identifier");
    return {
      k: "nullishAssign",
      pos: gate.span(node),
      name: gate.local(node.left),
      namePos: gate.span(node.left),
      rhs: gate.expr(node.right),
    };
  }
  if (node.operatorToken.kind === ts.SyntaxKind.QuestionQuestionToken)
    return {
      k: "coalesce",
      pos: gate.span(node),
      left: gate.expr(node.left),
      right: gate.expr(node.right),
    };
  if (
    node.operatorToken.kind === ts.SyntaxKind.EqualsToken &&
    ts.isArrayLiteralExpression(node.left)
  ) {
    // `[a, b = d, ...r] = rhs`: each element names a mutable local or a
    // field, with a default written as an assignment inside the literal; a
    // hole names none, and a rest, last, takes the positions after the
    // others. A field target's reference, its receiver and then its key, is
    // evaluated before its position is read and defaulted.
    const names = new Set<string>();
    const named = (target: Node): Expr => {
      if (ts.isIdentifier(target)) {
        if (target.text === "undefined")
          gate.fail(target, "shadowing undefined is outside the fragment");
        if (names.has(target.text)) gate.fail(target, "duplicate pattern binding");
        names.add(target.text);
        return { k: "id", pos: gate.span(target), name: gate.local(target) };
      }
      if (!ts.isPropertyAccessExpression(target) && !ts.isElementAccessExpression(target))
        gate.fail(target, "an array assignment pattern writes a local or a field");
      const reference = gate.expr(target);
      if (reference.k !== "read" && reference.k !== "index")
        gate.fail(target, "an array assignment pattern writes a local or a field");
      return reference;
    };
    let rest: Extract<Expr, { k: "arrayAssign" }>["rest"] = null;
    const targets: ArrayElemAst[] = node.left.elements.flatMap((el, index): ArrayElemAst[] => {
      if (ts.isOmittedExpression(el)) return [];
      if (ts.isSpreadElement(el)) {
        rest = { index, pos: gate.span(el), target: named(el.expression),
          slice: gate.slices.has(gate.span(node.right).join(":")) };
        return [];
      }
      const target =
        ts.isBinaryExpression(el) &&
        el.operatorToken.kind === ts.SyntaxKind.EqualsToken
          ? el.left
          : el;
      const dflt =
        ts.isBinaryExpression(el) &&
        el.operatorToken.kind === ts.SyntaxKind.EqualsToken
          ? el.right
          : null;
      return [{
        index,
        target: named(target),
        default_: dflt ? gate.expr(dflt) : null,
      }];
    });
    if (targets.length === 0 && !rest) gate.fail(node.left, "an empty pattern binds nothing");
    gate.steppedPattern(ts.isArrayLiteralExpression(skipParentheses(node.right)), gate.assignedSteps(node.left));
    return {
      k: "arrayAssign",
      pos: gate.span(node),
      targets,
      rest,
      rhs: gate.expr(node.right),
    };
  }
  if (node.operatorToken.kind === ts.SyntaxKind.EqualsToken) {
    // Assigning a name is assigning a mutable local. Whether one was
    // declared is the adapter's to check: it builds the scope, and a name
    // that is not a mutable local there has no slot to write.
    if (ts.isIdentifier(node.left)) {
      if (node.left.text === "undefined")
        gate.fail(node.left, "shadowing undefined is outside the fragment");
      return {
        k: "assign",
        pos: gate.span(node),
        name: gate.local(node.left),
        namePos: gate.span(node.left),
        rhs: gate.expr(node.right),
      };
    }
    // `o[k] = v` with `k` a `unique symbol` constant is the named write of
    // that symbol's key, as the read is.
    const symbolKey = ts.isElementAccessExpression(node.left)
      ? gate.symbolKeys.get(gate.span(node.left.argumentExpression).join(":")) : undefined;
    if (symbolKey !== undefined && gate.tagSymbols.has(symbolKey))
      gate.fail(node.left, TAG_WRITE);
    if (symbolKey !== undefined && ts.isElementAccessExpression(node.left) && !node.left.questionDotToken)
      return { k: "write", pos: gate.span(node), field: { symbol: symbolKey },
        receiver: gate.expr(node.left.expression), rhs: gate.expr(node.right) };
    if (
      ts.isElementAccessExpression(node.left) &&
      !node.left.questionDotToken
    )
      return {
        k: "indexWrite",
        pos: gate.span(node),
        receiver: gate.expr(node.left.expression),
        key: gate.expr(node.left.argumentExpression),
        rhs: gate.expr(node.right),
      };
    if (
      !ts.isPropertyAccessExpression(node.left) ||
      node.left.questionDotToken
    )
      gate.fail(node.left, "only field and local assignments are supported");
    return {
      k: "write",
      pos: gate.span(node),
      field: ts.isPropertyAccessExpression(node.left)
        ? (gate.staticPrivate(node.left) !== null
          ? gate.fail(node.left, "a write to a static member: statics are immutable bindings")
          : gate.memberKey(node.left.name))
        : gate.fail(
            node.left,
            "only field and local assignments are supported",
          ),
      receiver: gate.expr(
        ts.isPropertyAccessExpression(node.left)
          ? node.left.expression
          : gate.fail(
              node.left,
              "only field and local assignments are supported",
            ),
      ),
      rhs: gate.expr(node.right),
    };
  }
  const ops: Record<number, string> = {
    [ts.SyntaxKind.EqualsEqualsEqualsToken]: "===",
    [ts.SyntaxKind.ExclamationEqualsEqualsToken]: "!==",
    [ts.SyntaxKind.EqualsEqualsToken]: "==",
    [ts.SyntaxKind.ExclamationEqualsToken]: "!=",
    [ts.SyntaxKind.AmpersandAmpersandToken]: "&&",
    [ts.SyntaxKind.BarBarToken]: "||",
  };
  const op = ops[node.operatorToken.kind];
  if (!op)
    gate.fail(
      node,
      `binary operator outside the fragment (${gate.text(node.operatorToken)})`,
    );
  if (op === "===" || op === "!==" || op === "==" || op === "!=") {
    // Both operands of a typeof/literal test are strings, so loose equality
    // has the same result as strict equality and runs no conversion hook.
    const unwrap = (e: Expression): Expression =>
      ts.isParenthesizedExpression(e) ? unwrap(e.expression) : e;
    const left = unwrap(node.left),
      right = unwrap(node.right);
    const shapes: readonly TypeofShape[] = ["number", "string", "boolean", "undefined", "function", "bigint", "symbol", "object"];
    const shapeOf = (e: Expression): TypeofShape | undefined =>
      ts.isStringLiteral(e) ? shapes.find((s) => s === e.text) : undefined;
    const pair =
      ts.isTypeOfExpression(left) && shapeOf(right)
        ? { operand: left, shape: shapeOf(right) }
        : ts.isTypeOfExpression(right) && shapeOf(left)
          ? { operand: right, shape: shapeOf(left) }
          : null;
    if (pair?.shape)
      return {
        k: "typeofTest",
        pos: gate.span(node),
        shape: pair.shape,
        equal: op === "===" || op === "==",
        e: gate.expr(pair.operand.expression),
      };
  }
  const l = gate.expr(node.left);
  const r = gate.expr(node.right);
  if (op === "===" || op === "!==" || op === "==" || op === "!=") {
    const tested = chainComparison(gate, node, op, l, r);
    if (tested) return tested;
  }
  return { k: "bin", pos: gate.span(node), op, l, r };
}

/** The receiver of an optional chain's `?.`, parentheses around it
 * removed, where `at` is a chain of links ending at one. */
function chainReceiver(at: Node): Within<{ value: "any"; store: "grow" }, Node | null> {
  if (ts.isPropertyAccessExpression(at) || ts.isElementAccessExpression(at) || ts.isCallExpression(at))
    return at.questionDotToken ? skipParentheses(at.expression) : chainReceiver(at.expression);
  if (ts.isNonNullExpression(at)) return chainReceiver(at.expression);
  return null;
}

/** Whether a read of `receiver` runs no code: `this`, or a name the file
 * binds outside an ambient context (`resolve`). A global, which a `declare`
 * only types, may be an accessor of the global object. */
function inertRead(gate: Gate, receiver: Node): Within<{ value: "any"; store: "grow" }, boolean> {
  if (receiver.kind === ts.SyntaxKind.ThisKeyword) return true;
  if (!ts.isIdentifier(receiver)) return false;
  const declaration = gate.resolve(receiver);
  return declaration !== undefined && !(declaration.flags & ts.NodeFlags.Ambient);
}

/** `x?.p ⊙ c`, `⊙` an equality, `c` a literal and `.p` named reads (either
 * operand order): the test of the receiver, then the comparison of the
 * receiver's reads, `x != null && x.p ⊙ c` where `undefined ⊙ c` is false,
 * `x == null || x.p ⊙ c` where it is true (SOURCE-ELABORATION.md, optional
 * chains). `x` is a name whose read runs no code (`inertRead`), or `this`,
 * read again where the chain reads its saved value: nothing runs between
 * the two reads, so they give one value, and the literal's evaluation runs
 * nothing. The nullish test is spelled at the chain, its `null` at the `?`
 * of `?.`, the comparison at its operator; the reads keep their spans, the
 * receiver read again the `?.` token's, where the chain's saved value was. */
function chainComparison(gate: Gate, node: BinaryExpression, op: "===" | "!==" | "==" | "!=", l: Expr, r: Expr): Within<{ value: "any"; store: "grow" }, Expr | null> {
  const chainLeft = l.k === "optional";
  const chain = chainLeft ? l : r;
  const other = chainLeft ? r : l;
  if (chain.k !== "optional" || other.k !== "lit") return null;
  const source = chainReceiver(skipParentheses(chainLeft ? node.left : node.right));
  if (!source || !inertRead(gate, source)) return null;
  const receiver = chain.receiver;
  if (receiver.k !== "id" && receiver.k !== "this") return null;
  const reread: Expr = receiver.k === "id" ? { k: "id", pos: chain.at, name: receiver.name } : { k: "this", pos: chain.at };
  // The chain's links: named reads of its saved value, which the receiver
  // read again replaces.
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
  // `undefined ⊙ c`: strict equality holds of `undefined` alone, loose
  // equality of `null` too.
  const undefinedEquals = op === "==" || op === "!=" ? lit === "null" || lit === "undefined" : lit === "undefined";
  const absent = undefinedEquals === equal;
  const test: Expr = { k: "bin", pos: chain.pos, op: absent ? "==" : "!=", l: receiver,
    r: { k: "lit", pos: [chain.at[0], chain.at[0] + 1], lit: { a: "null" } } };
  const comparison: Expr = { k: "bin", pos: gate.span(node.operatorToken), op,
    l: chainLeft ? body : other, r: chainLeft ? other : body };
  return { k: "bin", pos: gate.span(node), op: absent ? "||" : "&&", l: test, r: comparison };
}

export function lambda(this: Gate, 
  node: ArrowFunction | FunctionExpression | MethodDeclaration,
  instance?: TypeTerm,
  member?: PropertyKey,
): Within<{ value: "any"; store: "grow" }, Expr> {
  const gate: Gate = this;
  // A method's accessibility is TypeScript's alone (`CLASS_ACCESS`); a static
  // one is bound on its own (`classStmt`).
  const modifiers = (node.modifiers ?? []).filter((m) => !(ts.isMethodDeclaration(node) &&
    (CLASS_ACCESS.includes(m.kind) || m.kind === ts.SyntaxKind.StaticKeyword)));
  const isAsync = modifiers.length === 1 && modifiers[0]?.kind === ts.SyntaxKind.AsyncKeyword;
  if (modifiers.length && !isAsync)
    gate.fail(node, "expected a closure without modifiers other than `async`");
  const ordinary = !ts.isArrowFunction(node);
  if (!ts.isArrowFunction(node)) {
    if (node.asteriskToken)
      gate.fail(node, GENERATOR);
    // A named function expression binds its own name inside itself. A name
    // the function never refers to binds nothing it reads; one it does refer
    // to is a recursive binding, which the fragment has no frame for, as for
    // a cyclic closure initialization.
    if (ts.isFunctionExpression(node) && node.name) {
      const own = node.name.text;
      let uses = false;
      const visit = (n: Node): void => {
        if (uses) return;
        if (ts.isPropertyAccessExpression(n)) {
          visit(n.expression);
          return;
        }
        if (ts.isIdentifier(n) && n.text === own) uses = true;
        n.forEachChild(visit);
      };
      node.parameters.forEach(visit);
      if (node.body) visit(node.body);
      if (uses)
        gate.fail(
          node,
          "a function expression that refers to its own name is a recursive binding, outside the fragment",
        );
    }
    if (ts.isMethodDeclaration(node) && node.postfixToken)
      gate.fail(
        node,
        "an optional or definite method is outside the fragment",
      );
  }
  // An ordinary function's leading `this: T` states its receiver; without
  // one, any receiver is accepted. An arrow cannot declare one. A class
  // method's states a type its host, the instance it is read from, must
  // meet, which a generic method's scheme does not state.
  const head = node.parameters[0];
  const stated =
    !!head && ts.isIdentifier(head.name) && head.name.text === "this";
  if (stated && instance && node.typeParameters?.length)
    gate.fail(head, GENERIC_METHOD_RECEIVER);
  if (stated && !ordinary)
    gate.fail(head, "an arrow cannot declare a receiver");
  if (
    stated &&
    (!head.type ||
      head.questionToken ||
      head.dotDotDotToken ||
      head.initializer)
  )
    gate.fail(head, "a receiver needs a required type annotation");
  const parameters = stated ? node.parameters.slice(1) : [...node.parameters];
  const body = node.body;
  if (!body) gate.fail(node, "a function must have a body");
  // A directive prologue in the function's own body makes it strict. It
  // is a syntax error beside parameters that are not simple.
  const prologue = ts.isBlock(body)
    ? gate.useStrict(body.statements)
    : { strict: false, skip: new Set<Statement>() };
  if (
    prologue.strict &&
    parameters.some((p) => p.initializer || p.dotDotDotToken)
  )
    gate.fail(node, '"use strict" beside non-simple parameters');
  const outerStrict = gate.strict;
  const outerReceiverMode = gate.receiverMode;
  const outerAsync = gate.asyncBody;
  const outerGuard = gate.guardBody;
  gate.strict = outerStrict || prologue.strict;
  if (ordinary) {
    gate.receiverMode = gate.strict ? "strict" : "sloppy";
  }
  // A class's generic method is the instance's member with quantified
  // signatures. Its closure's binders are named by the member's key and
  // the binder's position, so the producer's claims and the closure's
  // annotations name them alike; the closure's scheme binds them.
  const typeParams = gate.enterTypeParams(node.typeParameters, member === undefined ? undefined :
    (tp, index) => {
      if (tp.constraint)
        gate.fail(tp, "a bounded type parameter of a generic class method is outside the fragment: its binder row is named by its bound");
      return `${JSON.stringify(member)}#${index}`;
    });
  try {
    gate.asyncBody = isAsync;
    const receiver = !ordinary
      ? null
      : {
          // A class method's receiver is its instance, or the type its
          // `this` parameter states.
          type: stated
            ? gate.typeOf(head.type, head)
            : instance ? instance : ({ k: "atom", name: "unknown", span: gate.span(node) } satisfies TypeTerm),
          strict: gate.strict,
        };
    // Each name is taken where its parameter has just been checked: a
    // narrowing does not survive into the second pass over the same list.
    const bound = new Set<string>();
    const patterns: (PatternAst | null)[] = parameters.map((p) =>
      ts.isIdentifier(p.name) ? null : gate.pattern(p.name, bound));
    for (const p of parameters) {
      if (ts.isIdentifier(p.name) && p.name.text === "this")
        gate.fail(p, "expected an ordinary closure parameter");
      if (!ts.isIdentifier(p.name) && p.dotDotDotToken)
        gate.fail(p, "a rest parameter pattern is outside the fragment");
      if (p.questionToken && p.initializer)
        gate.fail(p, "a parameter cannot be both optional and defaulted");
      if (p.dotDotDotToken) {
        if (p.questionToken || p.initializer)
          gate.fail(p, "a rest parameter is neither optional nor defaulted");
        if (p !== parameters[parameters.length - 1])
          gate.fail(p, "a rest parameter must be the last one");
      }
      if (
        !p.questionToken &&
        !p.initializer &&
        !p.dotDotDotToken &&
        parameters.indexOf(p) > firstOptional(parameters)
      )
        gate.fail(p, "a required parameter cannot follow an optional one");
      if (ts.isIdentifier(p.name) && p.name.text === "undefined")
        gate.fail(p, "shadowing undefined is outside the fragment");
    }

    // A closure without a result annotation leaves its result to the
    // producer: the claim at the closure states it, and the body is checked
    // against that claim. A class method's result is its instance type's
    // member, which states it, so a method still needs the annotation.
    // A guard closure's annotation is its plain result and its promise.
    const guard = gate.guardOf(node);
    gate.guardBody = guard !== null;
    // A result `Within<F, T>` states the closure's effect, `F`, of `T`. A
    // generic closure's binders are bounded as its claim states, so no
    // check covers the domain its own bounds state: it states none.
    const written = gate.statedResult(node.type, node);
    if (written.stated && (node.typeParameters?.length || typeParams.length))
      gate.fail(node.type ?? node, "`Within` on a generic closure or method is outside the fragment: its code is checked at the binder bounds its claim states, which need not cover its own");
    const declaredResult: TypeTerm | null = guard ? guardResult(guard)
      : written.result || instance ? gate.typeOf(written.result, node) : null;
    const arrow = ts.isArrowFunction(node) ? gate.span(node.equalsGreaterThanToken) : null;
    const keyword = modifiers[0];
    const rest = (p: ts.ParameterDeclaration) => p.dotDotDotToken ? { rest: true as const } : {};
    // A parameter a pattern did not read is named by an identifier.
    const identifierOf = (p: ts.ParameterDeclaration): Identifier =>
      ts.isIdentifier(p.name) ? p.name : gate.fail(p, "a parameter pattern makes the body a block");
    // A block body, or a parameter written as a pattern, makes the body
    // statements, lowered as a function's are: a parameter written as a
    // pattern or with a default binds a hidden name, which the caller's
    // argument initializes, and a `destructure` over it, first in the body
    // in parameter order, binds the source's names, the default replacing
    // an undefined argument, as JavaScript initializes parameters.
    // A guard arrow's expression body with a defaulted parameter is a block
    // too, its return the one `booleanReturn` rewrites.
    if (ts.isBlock(body) || patterns.some((t) => t !== null) ||
        (guard !== null && parameters.some((p) => p.initializer))) {
      const bindings: Stmt[] = [];
      const params = parameters.map((p, i) => {
        if (ts.isIdentifier(p.name) && !p.initializer)
          return {
            name: gate.local(p.name),
            type: p.dotDotDotToken ? gate.restType(p) : gate.closureParamType(p),
            ...rest(p),
          };
        const hidden = parameterName(i);
        const at = gate.span(p.name);
        bindings.push({
          k: "destructure",
          pos: gate.span(p),
          target: patterns[i] ?? { k: "name", name: gate.local(identifierOf(p)), pos: at },
          default_: p.initializer ? gate.expr(p.initializer) : null,
          init: { k: "id", pos: at, name: hidden },
        });
        // A caller may pass `undefined` where there is a default.
        return {
          name: hidden,
          type: !p.type ? (p.initializer ? optionalTerm(gate.closureParamType(p), gate.span(p)) : gate.closureParamType(p))
            : p.questionToken || p.initializer ? gate.optionalTypeOf(p.type, p) : gate.typeOf(p.type, p),
        };
      });
      gate.initializedBefore(node, params.map((q): [PatternAst, Expr | null] => {
        const b = bindings.find((st) => st.k === "destructure" && st.init.k === "id" && st.init.name === q.name);
        return b?.k === "destructure" ? [b.target, b.default_] : [{ k: "name", name: q.name, pos: gate.span(node) }, null];
      }));
      let statements: Stmt[];
      if (ts.isBlock(body)) {
        const stmts = gate.statements(body.statements.filter((s) => !prologue.skip.has(s)));
        // A body that can complete returns `undefined` at its closing
        // brace, the literal there too; an async one, `%AsyncComplete%()`.
        const brace: Span = [body.end - 1, body.end];
        statements = isAsync ? gate.asyncCompletion(body, stmts)
          : completes(stmts) ? [...stmts, { k: "return", pos: brace,
              e: { k: "lit", pos: brace, lit: { a: "undefined" } } }]
          : stmts;
      } else {
        // An expression body is its return: `%AsyncReturn%(e)` when async,
        // the call at `=>`, the intrinsic read at `async`.
        const e = isAsync && arrow && keyword
          ? gate.intrinsic(asyncReturnName, arrow, gate.span(keyword), [gate.expr(body)])
          : gate.expr(body);
        statements = [guard && !isAsync && arrow && booleanForm(e)
          ? booleanReturn(gate.span(body), e, arrow[0])
          : { k: "return", pos: gate.span(body), e }];
      }
      return {
        k: "lambda",
        pos: gate.span(node),
        typeParams,
        receiver,
        params,
        result: declaredResult,
        guard,
        stated: written.stated,
        completion: isAsync ? "async" : "sync",
        body: { k: "blockBody", pos: gate.span(body), body: [...bindings, ...statements] },
      };
    }
    const value = isAsync && arrow && keyword
      ? gate.intrinsic(asyncReturnName, arrow, gate.span(keyword), [gate.expr(body)])
      : gate.expr(body);
    // A guard's Boolean by its form returns its truth's Boolean
    // (`booleanReturn`), the literals at the arrow's `=>`.
    const inner: Expr = guard && !isAsync && arrow && booleanForm(value)
      ? { k: "blockBody", pos: gate.span(body), body: [booleanReturn(gate.span(body), value, arrow[0])] }
      : value;
    const defaults = parameters.map((p) => p.initializer ? gate.expr(p.initializer) : null);
    // A parameter default's own schedule is Lean's (`parameterOrder`).
    gate.initializedBefore(node, parameters.map((p): [PatternAst, Expr | null] =>
      [{ k: "name", name: gate.local(identifierOf(p)), pos: gate.span(p.name) }, null]));
    return {
      k: "lambda",
      pos: gate.span(node),
      typeParams,
      receiver,
      params: parameters.map((p, i) => ({
        name: gate.local(identifierOf(p)),
        // A defaulted parameter's type is what the body reads; the default
        // itself is the expression that replaces an omitted argument. A rest
        // parameter's type is the tuple its arguments are collected into.
        type: p.dotDotDotToken ? gate.restType(p) : gate.closureParamType(p),
        ...(defaults[i] ? { default: defaults[i] } : {}),
        ...rest(p),
      })),
      result: declaredResult,
      guard,
      stated: written.stated,
      completion: isAsync ? "async" : "sync",
      body: inner,
    };
  } finally {
    gate.leaveTypeParams();
    gate.strict = outerStrict;
    gate.receiverMode = outerReceiverMode;
    gate.asyncBody = outerAsync;
    gate.guardBody = outerGuard;
  }
}
