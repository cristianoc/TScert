# Source fragment

The source fragment is the subset of TypeScript admitted by the parser and
source elaborator. This document is the index of its refusals: each row names
a construct, the reason it is refused, the section that owns the rule, and the
pipeline cases that exercise it (`pipeline/cases.mts`; a case marked
"Node" also runs under Node in `tests/node-runs.mts`). A refusal establishes
that this pipeline cannot verify that source under its rules; it does not
establish that the program is unsafe.
[Source contracts](SOURCE-CONTRACTS.md) gives the interpretation of annotations
and external declarations; [the trust surface](DESIGN.md#trust-surface) states
the assumptions used when connecting the extracted graph to JavaScript.

## Fragment boundary

What the pipeline refuses, each with its reason, in two classes. A refusal is
**principled** only when the construct is unsound, not faithful to
JavaScript, rejected by TypeScript, or safe only under an assumption the
project declines; any other refusal is a **model limit**, a gap, with the
obstacle named. A search failure is neither. Within each class the rows are
grouped by area. The parser's refusals are its `fail` sites
(`tools/fragment-*.mts`, `tools/type-term.mts`); syntax no row names (an
operator, expression, statement or type form the parser does not list, a
non-decimal numeric literal) is refused at its location as outside the
fragment.

### Refused on principle

**Values, keys and strings**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| A read at a key the object may lack that may name a member of `Object.prototype` (`toString`, `constructor`, `__proto__`, …, `objectProtoKeys`): an optional field or an index under such a name, by a member access, a computed key or a pattern; a key known only at run time to be some string | The model's objects hold no prototype there, so its read finds `undefined` where JavaScript's finds the member. A key the type proves own, a number key, and a string singleton naming no member are read; a computed read at some string is refused at its site (`comparisonsExpr` in `Source/Lowering/Types.lean`) | [key-adding writes](PROGRAM-TYPING.md#key-adding-writes) | `invalid-dictionary-inherited-key`, `invalid-dictionary-inherited-named`, `invalid-optional-inherited-key`, `invalid-pattern-inherited-key` (Node); `own-inherited-name` |
| A string holding a lone surrogate (`"\uD800"`), in a literal, a template, a key or a name | Every string on the wire is well-formed Unicode; a reader of a lone surrogate would read another string | [wire text](REQUEST-PROTOCOL.md#wire-text) | `invalid-lone-surrogate-string` |
| A read of a name `undefined` bound to anything but the global (`import { x as undefined }`); any other binding of the name | The read is that binding's value, which the fragment's `undefined` literal is not | [imported values](SOURCE-CONTRACTS.md#imported-ambient-and-global-values) | `invalid-undefined-import-value-import` (Node) |
| A key-adding write whose key may be `Symbol.toStringTag` (a key typed `symbol` included); a write at the tag; a literal or class member keyed by it | The native `Promise` contract requires the tag of a promise's prototype, which no object the program makes holds | [objects owning `then`](SOURCE-CONTRACTS.md#objects-owning-then) | `symbol-key-growth-refused`; `symbol-key-write` |

**Objects and writes**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| A record type where an index signature or a dictionary is expected (TypeScript's implicit index signature); width subtyping into an optional field; an array where a number index is expected | A record is open, owning further keys at any type; an array has a prototype a dictionary lacks | [index signatures](SOURCE-MODEL.md#index-signatures) | — |
| An object spread, an object pattern's rest, `Object.assign` or a key-adding write whose operand's or target's type excludes no host value: `unknown`, `{}`, a record of readonly or optional fields alone, a readonly array, a union with such an arm | A host object's own keys are package-internal fields the model leaves unknown; a merge is stuck on one | [restricted values](COMPILER-API.md#restricted-values) (R8, L7) | `spread-readonly-record-refused`, `growth-optional-accumulator-refused` |
| A spread of a value whose type states a symbol-keyed field, at a result stating that field | An own non-enumerable symbol property meets the type and the spread omits it | [object literals](SOURCE-MODEL.md#object-literals) | `invalid-spread-symbol-nonenumerable` (Node) |
| A write through a parameter that may add a key (`x.k = e` where `x`'s type does not state `k`, a writable optional field, an index key; `x[k] = e` at a run-time key) | The caller may hold the object at a type that leaves the key absent, or optional at another type | [key-adding writes](PROGRAM-TYPING.md#key-adding-writes) | `invalid-key-adding-parameter-write` (Node) |
| A function of the program owning `toString`: a class's static member named `toString`, a key `toString` (a name, a string, or a computed key typed as that literal) or a spread in the literal of `Object.assign`'s callable form, a write of `toString` (by name or at a computed key typed `"toString"`) on a receiver typed as a function | A function's `toString` is read from `Function.prototype`, whose native returns a string and runs no code; an own `toString` would be found first and run | [`Function.prototype.toString`](SOURCE-CONTRACTS.md#functionprototypetostring) | `invalid-function-own-to-string` (Node), `invalid-function-own-to-string-assign` (Node), `invalid-function-own-to-string-computed` (Node), `invalid-function-to-string-write`, `invalid-function-to-string-write-computed`; `function-to-string` |
| A write of a namespace member (`ns.x = e`, `ns.x++`, `delete ns.x`, a destructuring target) | A member is an import binding, whose [[Set]] and [[Delete]] throw a `TypeError` | [namespace imports](SOURCE-ELABORATION.md#namespace-imports) | `invalid-namespace-member-write-value-import` (Node) |
| A type that normalizes to nothing as a whole (`string & { a: number }`, `number[] & { map: number }`); as a union arm it adds nothing | No value of the model inhabits it; it is refused rather than verified vacuously | [library types](SOURCE-CONTRACTS.md#library-types) | — |
| `Object.freeze` of anything but an object literal of named fields written as its argument: an array literal, a reference to an object, a literal with a method, an accessor, a spread, a computed key or `__proto__` | The model's writes never raise, a frozen object's do; only the call's result, at readonly views, may reach the frozen object | [library globals](SOURCE-CONTRACTS.md#library-globals) | `invalid-object-freeze-array` (Node), `invalid-object-freeze-reference` (Node), `invalid-object-freeze-method` (Node); `object-freeze-literal` |

**Arrays and iteration**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| `new Array(x)` with one argument | A numeric argument constructs holes, which a readable element contract excluding `undefined` cannot justify | [arrays](SOURCE-MODEL.md#arrays) | — |
| An element write at an index not proven in bounds or appending | It could create a hole, which a later spread into a rest passes as `undefined` | [arrays](SOURCE-MODEL.md#arrays) | `spread-holes` |
| A mutable `Dog[]` as an `Animal[]`, a mutable dictionary of `true` as one of `boolean`, a readonly view as a writable one | Mutable storage is invariant: a write through the wider alias breaks the narrower one's contract | [writable string index signatures](SOURCE-MODEL.md#writable-string-index-signatures) | — |
| A position past a mutable tuple's arity; its `length` read at the arity | `push` may have extended it | [arrays](SOURCE-MODEL.md#arrays) | — |
| An array `Array.isArray` or `instanceof Array` finds in `unknown` or a record, passed at a generic call's mutable `Array<A>` | It may be a tuple, which a callee rearranging its `Array<A>` breaks | [arrays](SOURCE-MODEL.md#arrays) | `invalid-open-array-generic-call` (Node) |
| A class extending `Array` | `map`, `filter` and `slice` construct their results through the subclass (`ArraySpeciesCreate`) | [exact contracts and native effects](SOURCE-MODEL.md#exact-contracts-and-native-effects) | `invalid-array-subclass` |
| A loop or an array pattern over an iterable whose iterator's type states no `return` | Leaving early or throwing calls whatever `return` the iterator owns, which an open record says nothing of | [the iterator protocol](SOURCE-ELABORATION.md#the-iterator-protocol) | — |

**Functions, calls and methods**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| Method bivariance (`Handler<Dog>` as `Handler<Animal>`), an override with narrower parameters, a narrower constructor at a construct signature | The member may be invoked with the wider argument | [method members](SOURCE-MODEL.md#method-members-are-host-relative) | `invalid-variance`, `invalid-callback-variance`, `invalid-class-variance` |
| A method as a function-typed property, method extraction (`.call`, `.apply`, `.bind` of one included), a write to a method member; a function typing `this` where a receiver-indifferent callback is expected | A method read off its host loses its receiver | [method members](SOURCE-MODEL.md#method-members-are-host-relative) | — |
| `.call`, `.apply` or `.bind` of a function value a unit receives (a parameter, a field of one, a copy, a call's result) | A received function may own a `call`, `apply` or `bind` its annotation does not constrain | [calls through `Function.prototype.call`](SOURCE-ELABORATION.md#calls-through-functionprototypecall) | `invalid-call-own-override` (Node), `invalid-apply-own-override`, `invalid-bind-own-override` |
| A call of a `Function` value | It states no signature: TypeScript calls it at `any` | [library types](SOURCE-CONTRACTS.md#library-types) | — |
| A fresh callable given a field `call`, `bind`, `name`, `length`, `caller` or `arguments` (`Object.assign(f, { name })`) | An own `call` or `bind` would replace the intrinsic the parser identifies; `name` and `length` are unwritable and `caller` and `arguments` throwing accessors | [trust surface](DESIGN.md#trust-surface) | — |
| A rest parameter typed by what is no array | TypeScript rejects it (TS2370) | [calls](SOURCE-MODEL.md#calls) | — |
| A rest parameter typed by an intersection (`...xs: T[] & (number[] \| string[])`) | Its contract is empty at an instance TypeScript admits (`T := boolean`) | [calls](SOURCE-MODEL.md#calls) | `invalid-rest-intersection` (Node) |
| A type parameter typing a rest parameter and anything else, in a module function or a generic function or constructor type | The array a call collects is fresh, so it is no value of an instance with other members (`T := string[] & { tag: string }`) | [packed binders](PROGRAM-TYPING.md#packed-binders) | `invalid-rest-pack-value` |
| An instance of a packed binder other than an array or tuple type with no other members and no holes | The array a call collects is fresh, with the elements and none of the instance's other members | [packed binders](PROGRAM-TYPING.md#packed-binders) | `invalid-class-rest-binder-instance` |
| `"use strict"` in a function with non-simple parameters (defaults, patterns, a rest) | JavaScript and TypeScript reject it | [source closures](SOURCE-ELABORATION.md#source-closures-and-their-annotations) | — |
| TypeScript's `any` in the checked module's own annotations; a contextual closure parameter TypeScript types `any` | It states no contract | [source closures](SOURCE-ELABORATION.md#source-closures-and-their-annotations) | — |
| A contract read through an unannotated declaration a type reaches (`typeof`, a member selection, a named type, a whole class, namespace or module) | Its type is inferred from code the reader does not read; the bound obligations written there would go unchecked | [types stated by annotations](SOURCE-CONTRACTS.md#types-stated-by-annotations) | `invalid-written-unannotated-call-value-import`, `invalid-written-whole-class-value-import`, `invalid-written-unannotated-field-value-import` |

**Stated effects**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| `Within<F, T>` anywhere but a written signature's result or a guard's promised type: a parameter, an element, a field, a type argument, another `Within`; a reference the declaration reader resolves to `Within` or `Footprint` elsewhere | A statement is the effect of the signature it is the result of; read as the alias it is, its effect would be dropped where another reader keeps it | [stated effects](SOURCE-ELABORATION.md#stated-effects) | `invalid-method-effect-misplaced`, `invalid-method-effect-misplaced-element` |
| A footprint written other than in place, as a type literal of `value`, `store` and `onThrow` | Every reader reads the footprint from its syntax, alike | [stated effects](SOURCE-ELABORATION.md#stated-effects) | `invalid-method-effect-alias` |
| A statement of `{value: any, store: any}`, with or without `onThrow` | It states nothing the ordinary effect does not | [stated effects](SOURCE-ELABORATION.md#stated-effects) | `invalid-method-effect-top` |
| A statement on an async definition, a constructor, a construct signature, a resolution-qualified declaration, any signature of an overloaded declaration, or a generic closure or method | Its certification has no unit to run at: an async call returns where its body throws, a construction's effect is its class's, a qualified unit claims no footprint, an imported overloaded declaration's unit is certified at one signature, the file's own overloads' units claim the footprint their code proposes, and a generic closure's code is checked at the binder bounds its claim states | [stated effects](SOURCE-ELABORATION.md#stated-effects) | `invalid-method-effect-async`, `invalid-construct-signature-effect`, `invalid-stated-overload-value-import`, `invalid-stated-one-overload-value-import`, `invalid-method-effect-overload`, `invalid-method-effect-generic` |
| A statement written outside the program's sources (a declaration file, a package, an ambient declaration), or reached from the type of a value declared there through `typeof`, an alias, an interface or an indexed access, other than a member of a class the program declares | The value's code is the environment's, which no run checks | [stated effects](SOURCE-ELABORATION.md#stated-effects) | `invalid-stated-external-value-import`, `invalid-stated-external-alias-value-import` |

**Classes**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| Narrowing `unknown` by `instanceof C`, and a member read of the result | An object gets `C`'s prototype without `C`'s constructor (`Object.create(C.prototype)`) | [`instanceof`](SOURCE-ELABORATION.md#instanceof) | — |
| `Object.create(p)`, and a class extending `Map` or `Set` | An object holding `Map.prototype` or `Set.prototype` on its chain passes `instanceof Map` or `instanceof Set` without a host collection's internal slots, or with its own iterator, where the test promises a host collection | [collections passing `instanceof`](SOURCE-CONTRACTS.md#collections-passing-instanceof) | `invalid-instanceof-map-counterfeit`, `invalid-instanceof-set-counterfeit`, `invalid-instanceof-map-shadowed` (Node) |
| A member taking an element (`set`, `add`, `get`, `has`, `delete`, `forEach`) of a value `instanceof Map` or `instanceof Set` narrowed | The test establishes no element contract: a write would break the contract of a caller holding the collection at its own type | [collections passing `instanceof`](SOURCE-CONTRACTS.md#collections-passing-instanceof) | `invalid-instanceof-map-write` (Node) |
| `instanceof` of a constructor neither declared at the file's top level nor an import of a checked class declaration, but a name whose type states `[Symbol.hasInstance]` | Nothing says which prototype it gives its instances | [`instanceof`](SOURCE-ELABORATION.md#instanceof) | `instanceof-foreign-constructor-refused` |
| `instanceof` of an import that is no checked class declaration: a class expression a constant holds, a class an ambient module or a declaration file declares, one extending such a class or a value, one whose module TypeScript reports an error in (a write of its binding among them) or suppresses an error in, one whose module uses its binding, in any expression that runs, other than as `new`'s callee, `instanceof`'s right operand, a base class's or `export default`'s expression, a member read's receiver, a type or an export (an alias, an argument, a member write); of a local constant holding an imported class | Its value may be any constructor, or one whose prototype chain holds a `[Symbol.hasInstance]` its type does not state | [imported classes](SOURCE-CONTRACTS.md#imported-classes-and-instanceof) | `invalid-instanceof-expression-value-import`, `invalid-instanceof-ambient-value-import`, `invalid-instanceof-ambient-base-value-import`, `invalid-instanceof-rebound-value-import` (Node), `invalid-instanceof-suppressed-value-import` (Node), `invalid-instanceof-hooked-value-import` (Node), `invalid-instanceof-getter-value-import` (Node), `invalid-instanceof-default-hook-value-import` (Node), `invalid-instanceof-heritage-hook-value-import` (Node), `invalid-instanceof-setter-hook-value-import` (Node), `invalid-instanceof-alias-value-import` |
| A base class declared later, imported, ambient, or an expression | Nothing in the file says what its constructor allocates (TypeScript rejects the first) | [derived classes](SOURCE-ELABORATION.md#derived-classes) | — |
| `this` before `super(...)` | TypeScript rejects it, and JavaScript throws | [derived classes](SOURCE-ELABORATION.md#derived-classes) | — |
| A class merged with an interface whose member its constructor does not give | TypeScript assumes the member on instances the constructor does not create | [classes](SOURCE-CONTRACTS.md#classes) | `invalid-merged-augmented`; `merged-class-consumer-value-import` |

**Bindings and scope**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| A read of a local above its declaration or in its own initializer; a parameter default reading a later parameter | JavaScript throws there (the temporal dead zone), and TypeScript rejects it (TS2448, TS2373) | [lexical bindings before initialization](SOURCE-ELABORATION.md#lexical-bindings-before-initialization) | `recursive-const-before-initialization-refused` |
| An assignment to a module function's binding | TypeScript rejects it (TS2630) | [module functions](SOURCE-ELABORATION.md#module-functions) | — |
| A catch binding annotated other than `unknown`, or destructured | Anything may be thrown; TypeScript's alternative is `any` | [statement forms](SOURCE-ELABORATION.md#statement-forms) | — |
| A direct `eval` call (`eval(s)`, `(eval)(s)`); a binding named `eval` or `arguments` | A direct eval may read and write any binding of the caller's scope; in sloppy code either name changes meaning | [trust surface](DESIGN.md#trust-surface) | — |

**Operators and coercion**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| `String(o)`, `Number(o)`, `Math.max(o)`, `Math.min(o)`, `String.fromCodePoint(o)`, `String.fromCharCode(o)`, `Object.getOwnPropertyDescriptor(x, o)`, `o + ""`, `new Date(o)`, `new Set(it)` or `new Map(it)` of an iterable that is no array, string or host collection, `JSON.parse` with a reviver, `JSON.stringify` with a replacer function, of an array or open record; a relational comparison with an object operand | The host runs client code (`toString`, `valueOf`, an iterator, a callback, a `toJSON`) | [library globals](SOURCE-CONTRACTS.md#library-globals) | — |
| `Reflect`'s functions but `ownKeys` and `apply` | `Reflect.get` runs [[Get]], which calls a getter no type of the object states | [library globals](SOURCE-CONTRACTS.md#library-globals) | `invalid-reflect-get-array` |
| `+` on a bigint, number–bigint arithmetic, a symbol in a concatenation; a relational comparison of a string with a number | TypeScript refuses these operations | [throws](SOURCE-MODEL.md#throws) | — |
| `==` or `!=` that may convert an object, an array included, to a primitive | Conversion may run client hooks; only a union reaches it, too rare to justify a `valueOf` restriction ([utility](DESIGN.md#principles)) | [tag tests](SOURCE-MODEL.md#tag-tests) | — |
| `key in o` on an operand with a primitive arm or `unknown` | JavaScript throws on a primitive, and TypeScript rejects both | [`in`](SOURCE-ELABORATION.md#in) | — |

**Async**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| An async return or a non-promise `await` without a stable non-thenable contract | JavaScript adopts thenables; an arbitrary record type states nothing of `then` | [async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await) | — |
| A write replacing a native promise's `constructor` or prototype members through any alias; an own `then` on an ordinary array | These violate the native promise and stable non-thenable contracts | [async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await) | — |
| A source declaration merged with the standard `Promise` interface | Native factories produce standard promises, which the merged members do not describe | [async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await) | — |
| An async return annotated with a nested promise where fresh resolution yields a non-promise payload | `Promise<A>` states the fulfillment value's type, which the payload does not meet | [async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await) | — |
| `catch` or `finally` promising to preserve an open record payload without restricting its `then`; a `finally` callback returning such a record | Resolving it again may call a hidden `then` and change the fulfillment value | [async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await) | — |
| A footprint other than `top` claimed for an async function, arrow, function expression or method | The model reads the body's throw as a throw, where JavaScript rejects the promise the call returns normally | [the checked callback contract](FOOTPRINTS.md#the-checked-callback-contract) | `invalid-async-throw-only`, `invalid-async-rejection-effect` |

**Guards**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| A use of a guard's argument that relies on the guard's `false` outcome | The promise states the `true` outcome only; TypeScript's narrowing of the `false` one is wrong for a guard answering `false` for some values of `T` | [user-defined guards](SOURCE-ELABORATION.md#user-defined-guards) | `invalid-type-guard-false-branch` (Node) |

**Library and host**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| A declaration outside the standard library merging into an interface read at a reviewed contract (`Object`, `Function`, `Array`, a primitive's wrapper, the iterators they name), at a member the overlay does not review at that contract | The merge installs nothing at run time; its member would be erased from the annotations it changes | [merged library interfaces](SOURCE-CONTRACTS.md#merged-library-interfaces) | `invalid-merged-object`, `invalid-merged-array-param`, `invalid-merged-narrowed-at`, … |
| `Object.assign` where a declaration augments `ObjectConstructor.assign` | The fragment reads `Object.assign` only as the standard intrinsic copy | [library globals](SOURCE-CONTRACTS.md#library-globals) | `invalid-augmented-object-assign`, `invalid-fake-lib-object-assign` (Node) |
| An enum of the compiler API's package read as a value where its contract does not list it (`CharacterCodes`) | The declaration and the runtime object differ (`ogham`: 5760 and 5765) | [compiler API](COMPILER-API.md) | `invalid-compiler-api-unlisted-enum` |
| `readdirSync` with `recursive: true` | The recursive walk collects entries from subdirectories and has no reviewed contract | [library modules](SOURCE-CONTRACTS.md#library-modules) | `invalid-node-readdir-recursive` (Node) |
| `RegExp.prototype.compile` | It replaces the pattern, and with it the capture shape the type states | [regular expressions](SOURCE-CONTRACTS.md#regular-expressions) | `invalid-regexp-compile` (Node) |
| `matchAll` or `replaceAll` of a regex no literal made | The host reads and converts the argument's `flags`, running an object `flags`'s `toString` | [regular expressions](SOURCE-CONTRACTS.md#regular-expressions) | `invalid-regexp-structural-matchall` (Node) |

**Modules and enums**

| Construct | Reason | Owner | Cases |
| --- | --- | --- | --- |
| An empty module (no function, no initialization code) | Accepting it would check nothing | [modules and code units](SOURCE-CONTRACTS.md#modules-and-code-units) | — |
| An enum member initializer reading a member not yet initialized, or the enum itself, a closure's read included; a call in one that can read the enum | JavaScript reads it before the emit writes it | [enums](SOURCE-CONTRACTS.md#enums) | `invalid-enum-computed-forward`, `invalid-enum-computed-call-order` |
| An enum member named `__proto__` | The emit's assignment runs the prototype's setter and creates no property | [enums](SOURCE-CONTRACTS.md#enums) | `invalid-enum-proto-member` |
| A member named `NaN` or `Infinity` in an enum with a member TypeScript computes no value for | That member's reverse mapping may be written at the name | [enums](SOURCE-CONTRACTS.md#enums) | `invalid-enum-computed-nan-name` |

### Model limits

Sound JavaScript that TypeScript accepts, refused because the model or its
representation does not state it; the paths are in
[next steps](../WORK.md#next-steps).

**Values, keys and operators**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| A source key spelling one the model keeps for itself (`"[]"`, a name in double brackets) | The model holds an array's store and an object's prototype under those keys | [values](SOURCE-MODEL.md#values) | — |
| A source property name beginning with `[!` | Computed string keys are escaped (`escapeKey`) and literal names kept, and the two would collide | [values](SOURCE-MODEL.md#values) | — |
| A literal or class member keyed by a well-known symbol other than `Symbol.iterator` and `Symbol.hasInstance` | It changes how the host treats the object, which the model does not state; a tag would let it pass for a host collection | [`instanceof`](SOURCE-ELABORATION.md#instanceof) | — |
| `===` or `!==` between two operands neither known to be a primitive or an object; narrowing by object identity | Such values may be of no kind the operator decides; a statement entry states no slot equality | [tag tests](SOURCE-MODEL.md#tag-tests) | — |
| `&`, `\|`, `<<`, `>>` or `>>>` of two bigints | The model states these operators on numbers alone | [throws](SOURCE-MODEL.md#throws) | `invalid-bitwise-bigint` |
| `\|\|=` or `&&=` on a target other than a Boolean; `??=` on a target other than a local | The lowering tests the value read as a Boolean, and saves a local's value only | [logical operators](SOURCE-ELABORATION.md#logical-operators) | — |

**Objects and writes**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| A key-adding write to an object another reference may hold: a module constant, an object a local did not allocate, a local whose object escaped, a write in a loop the allocation does not enclose | Adding a key copies the object, rebound to every local holding it; another reference would see the old object | [key-adding writes](PROGRAM-TYPING.md#key-adding-writes) | `node-process-env-write` |
| A write at a run-time string key of a value that may be an object or `null`; a key-adding write at a key that may be a string or a symbol | The key may be `__proto__`, whose setter replaces the prototype, which the copy does not | [key-adding writes](PROGRAM-TYPING.md#key-adding-writes) | — |
| A write of `__proto__`; adding a symbol key to an object whose type does not list its keys | The first runs the prototype's setter; the copy takes string keys and the object's symbol keys are not known | [key-adding writes](PROGRAM-TYPING.md#key-adding-writes) | — |
| `Object.assign` onto anything but a fresh literal or, as a statement, a local's own object; from a source that may own `__proto__`; onto an array | Its value is its target, which another reference may see; `__proto__` goes through the prototype's setter; the copy of an array is no array | [object literals](SOURCE-MODEL.md#object-literals) | — |
| An optional call of `Object.assign`, or one whose target and sources are not written as arguments | The copy is lowered from its written operands | [object literals](SOURCE-MODEL.md#object-literals) | — |
| An accessor (`get`/`set`), `__proto__`, or a computed key in a literal other than a `unique symbol` constant or a name or member read typed as one string or number literal; a computed or symbol key in a literal with a spread | The heap has data properties only, and an [open read](SOURCE-CONTRACTS.md#open-reads) preserves the modeled heap by the key audit and open-read restriction; another key is known only at run time | [object literals](SOURCE-MODEL.md#object-literals) | `object-computed-literal-key`, `invalid-open-read-getter` (Node) |
| An open read at a key outside the audited allowlist, including through erasure to `unknown`; a read after `"k" in o` of a key outside the allowlist a host family's type does not state; a write at a key an `in` test found and no type states | A family's type states its keys, and an open read's `unknown` establishes none; the write may add the key | [open reads](SOURCE-CONTRACTS.md#open-reads) | `invalid-compiler-api-open-read-erased`, `invalid-compiler-api-open-read-internal`, `invalid-compiler-api-open-read-kind` (Node), `invalid-open-read-write` |
| In a class extending `Error`, an instance member, parameter property or constructor's `this.k = e` named `message`, `stack` or `cause`; a write that may set one of them on a receiver not excluding every object with a prototype | JavaScript's instance owns them non-enumerable, which the model does not state | [reserved writes](SOURCE-ELABORATION.md#reserved-writes) | `invalid-error-subclass-assign-target`; `reserved-write-twin` |
| In a class extending `Error`, an instance member, parameter property or constructor's `this.name = e` named `name` | The model states an error's `name` on its link, where `Error.prototype` holds it; a member or own field would stand beside it | [a class extending `Error`](SOURCE-ELABORATION.md#a-class-extending-error) | `invalid-error-subclass-name-field`, `invalid-error-subclass-name-write` |

**Arrays and iteration**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| An array literal hole (`[a, , b]`); a literal with a spread claimed at a tuple of fixed positions | A hole is no location; a spread's length is known only at run time | [a literal with spreads](PROGRAM-TYPING.md#a-literal-with-spreads) | — |
| `unknown` used as an array after `Array.isArray` or `instanceof Array` | The array invariant is stated of record and dictionary members, not of `unknown` | [arrays](SOURCE-MODEL.md#arrays) | — |
| An element read past a readonly tuple arm's length | No element rule reads `undefined` beyond an exact length | [patterns](SOURCE-ELABORATION.md#patterns) | — |
| An array pattern over an array another reference may hold, with code that may change it between its steps | The lowering reads positions, which match JavaScript's finished iterator only while nothing grows the array | [patterns](SOURCE-ELABORATION.md#patterns) | `array-pattern-exhausted-refused`, `array-pattern-exhausted-rest-refused`, `array-binding-exhausted-refused`, `for-of-pattern-program-iterable-default-refused` (Node); `array-pattern-steps` |
| An array pattern over a value that may not be an array, nested or binding a `for...of` | Over another iterable the steps are the iterator's, placed only for a declaration's whole pattern | [the iterator protocol](SOURCE-ELABORATION.md#the-iterator-protocol) | `invalid-for-of-pattern-string`, `for-of-pattern-nested-iterable-refused` |
| An array pattern over a program's iterable at a module's top level or in a `for` initializer, or under an annotation; a default or nested pattern in one, its rest's included | Its steps are statements before the declaration, which only a body has; a default runs code between steps; the steps read the iterator, which an annotation does not state | [the iterator protocol](SOURCE-ELABORATION.md#the-iterator-protocol) | `annotated-pattern-program-iterable-refused` |
| A spread of a program's iterable after an operand that may run code, or not evaluated first by its statement | The iterator runs before the statement, which would reorder the operand's code | [the iterator protocol](SOURCE-ELABORATION.md#the-iterator-protocol) | `spread-program-iterable-uninitialized-refused`, `spread-program-iterable-global-getter-refused`, `spread-program-iterable-global-tdz-refused` (Node) |
| A loop or spread over a `SetIterator` or `MapIterator` no `Set` or `Map` method returned, other than a loop over a call of a `ReadonlySet`'s or `ReadonlyMap`'s `keys`, `values` or `entries` | The host's iteration is assumed of the native collection iterator alone | [loops and spreads](SOURCE-ELABORATION.md#loops-and-spreads-over-iterables) | `invalid-readonly-set-iterator-native` (Node), `spread-readonly-map-values-refused` |
| A loop or spread over a `RegExpStringIterator` no native regex's `matchAll` returned | The host's iteration is assumed of the native iterator alone | [loops and spreads](SOURCE-ELABORATION.md#loops-and-spreads-over-iterables) | — |
| A generator function (`function*`); `for await` | A body suspended at `yield` is no term of the calculus; an async iterator's steps are promises the model does not adopt | [async and iteration](SOURCE-MODEL.md#async-and-iteration) | — |

**Functions, calls and methods**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| `f.call(r)`, `f.apply(r, l)` or `f.bind(r)` of an `f` that is no known local function | A supplied function may own a `call`, `apply` or `bind` its type does not constrain | [calls through `Function.prototype.call`](SOURCE-ELABORATION.md#calls-through-functionprototypecall) | — |
| `Reflect.apply` with a missing or nullish list, a non-array array-like object, an optional-length tuple, or an array of unknown length passed to fixed parameters; an array-list application in a closed expression | Receiver application checks required tuple positions or a rest-only signature; closed expressions have no array-read operation | [library globals](SOURCE-CONTRACTS.md#library-globals) | `reflect-apply`; forged required and nullable lists |
| A rest parameter of a closure, or typed by an enclosing declaration's type parameter; a function type's rest typed by a type parameter typing no value; a rest whose bound is no array or tuple of required positions; a rest typed by a tuple with optional or rest elements | A closure's scheme has no meet row for argument lists; several lengths are several signatures | [calls](SOURCE-MODEL.md#calls) | — |
| A rest-parameter pattern | The rest binds one name | [patterns](SOURCE-ELABORATION.md#patterns) | `invalid-rest-parameter-pattern`, `invalid-closure-rest-parameter-pattern` |
| A parameter pattern one of whose bindings is assigned; an assigned parameter with a default and no annotation of a closure whose body is a block | A pattern binding's contract is the part of the annotation it reads, and each name is bound before the pattern's later defaults read it; an unannotated parameter's contract is its context's type | [patterns](SOURCE-ELABORATION.md#patterns) | `invalid-parameter-pattern-assigned`, `invalid-parameter-pattern-default-order` (Node); `invalid-parameter-default-contextual` |
| A declaration's pattern under an annotation with a default, or a `let` one with an assigned binding | A default must meet its binding's part of the annotation, and an assigned binding's contract is that part; the lowering states no type for one binding of a pattern | [patterns](SOURCE-ELABORATION.md#patterns) | `invalid-annotated-pattern-default`, `invalid-annotated-pattern-let-written` (Node) |
| A spread into an ordinary call's fixed parameters of an array that is no tuple of required positions | The positions it fills are known only at run time | [calls](SOURCE-MODEL.md#calls) | — |
| A callable object type with an optional or readonly field or an index signature | No clause of the type language combines call signatures with those members | [how the calculus represents a callable](CALLABLES.md#how-the-calculus-represents-a-callable) | — |
| A call of an intersection of a function type and a record type | An annotation's meet forms no callable with fields | [calls](SOURCE-MODEL.md#calls) | — |
| An actual that runs code after a spread into an ordinary call's fixed parameters | The lowering copies a spread where it is written only into a rest | [calls](SOURCE-MODEL.md#calls) | — |
| A spread argument in `super.m(…)`, an optional method call or a string method dispatching to a regex | These calls take their arguments as written | [calls](SOURCE-MODEL.md#calls) | — |
| A call through a union of functions carrying fields | The producer claims a call through one arrow, which such a union does not offer | [calls](SOURCE-MODEL.md#calls) | — |
| Constructing through a value of a generic constructor type | A construct scheme has no instance rule | [generic function and constructor types](SOURCE-CONTRACTS.md#generic-function-and-constructor-types) | — |
| A bounded generic function type met by a generic closure or module function | Quantified coverage does not use the bound to relate the two schemes | [generic function and constructor types](SOURCE-CONTRACTS.md#generic-function-and-constructor-types) | — |
| Explicit type arguments on an optional call | The parser reads them on plain and method calls | [explicit type arguments](SOURCE-CONTRACTS.md#explicit-type-arguments) | `explicit-type-arguments` |
| An optional call of a method read at a computed key, through a parenthesized optional chain, or as a member that is no property read of its object (a static or namespace member); one with spread arguments | The lowering saves the object and reads one named member off it | [optional chains](SOURCE-ELABORATION.md#optional-chains) | `optional-method-call`, `optional-method-call-this`, `optional-method-call-object` |
| A module function without a parameter or result annotation; an anonymous `export default function` | Its slot is its annotated signature; the lowering names each function | [modules and code units](SOURCE-CONTRACTS.md#modules-and-code-units) | — |
| Overloads of a module function stating type parameters other than its implementation's, or another number of parameters, a rest or `this` parameter, a type predicate, or an async implementation; imported generic overloads stating different type parameters | Each overload is the implementation's code checked at that overload, its parameters the implementation's, under the binders every overload and the slot share | [module functions](SOURCE-ELABORATION.md#module-functions), [overloads](SOURCE-CONTRACTS.md#imported-ambient-and-global-values) | `overloaded-function-renamed`, `ambient-generic-overloads-renamed` |
| A function declaration in a `case` clause, in a block of sloppy code, overloaded or repeated, or naming a parameter of its function | Its binding is the `switch` block's; Annex B also binds it in the enclosing function; one binding holds one closure; it replaces the parameter's binding | [function declarations in a body](SOURCE-ELABORATION.md#function-declarations-in-a-body) | `function-declaration-sloppy-block-refused` |
| A function expression that refers to its own name | It is a recursive binding, which the fragment states for constants only | [recursive constants](SOURCE-ELABORATION.md#recursive-constants) | — |
| A `this` read in sloppy code whose receiver type may hold a non-object | A sloppy call converts such a receiver, which the model has no step for | [sloppy code reading `this`](SOURCE-ELABORATION.md#sloppy-code-reading-this) | — |
| A user-defined guard that is generic, collects a rest in a closure, is about the receiver (`this is T`), is `asserts x` without a type, or promises an actual other than a name | The producer encodes no quantified promise signature; the receiver has no slot; truthiness names no type; a property may be written by the call | [user-defined guards](SOURCE-ELABORATION.md#user-defined-guards) | — |
| A promise about objects decided by tests of an `unknown` (`v is Record<string, unknown>` by `typeof v === "object"`) | The tests leave an object without call code, which may be a class instance or a host object, no dictionary | [slices of the value universe](SOURCE-MODEL.md#slices-of-the-value-universe-by-tag-tests) | `type-guard-object-refused` |
| A closure parameter without an annotation whose contextual type is a record with a method, accessor, symbol key or unusual index, a structure containing itself no declaration names, or a callable with type parameters, a receiver promise, an unusual rest, a construct signature or other members | The parser writes the contextual type as an object contract of fields and indexes, or one instantiated call signature | [source closures](SOURCE-ELABORATION.md#source-closures-and-their-annotations) | `closure-contextual-method-refused`, `closure-contextual-callable-generic-refused`, `closure-contextual-callable-members-refused` |
| A closure at a generic signature whose type parameter is bounded or defaulted, or whose parameters' contextual types name another type parameter of its spelling; an object literal's method at a generic signature; a closure whose parameter is itself a generic function type | The closure takes the signature's type parameters unbounded, read from the closure expression's type, and renames their occurrences by spelling | [source closures](SOURCE-ELABORATION.md#source-closures-and-their-annotations) | `contextual-generic-closure-bounded-refused`, `contextual-generic-closure-spelling-refused`, `contextual-generic-method-refused`, `contextual-generic-closure-nested` |

**Classes**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| An anonymous class; a class modifier other than `export` (`abstract`, `export default`) | The lowering binds a class by its name and constructs every class it declares | [classes](SOURCE-CONTRACTS.md#classes) | — |
| A library class other than `Array` and `Error` as a base (`extends Map`, `extends TypeError`) | A library constructor's instance has no construction rule | [a class extending `Error`](SOURCE-ELABORATION.md#a-class-extending-error) | — |
| A class extending a generic class other than at the base's own binders | A generic base's construction is at its binders' rows | [classes](SOURCE-CONTRACTS.md#classes) | — |
| A generic or optional method declaring `this: T`; an optional method of a nested type literal or of a class; a generic class method with a bounded binder | A scheme states no type the host must meet; an optional method takes its declaration as receiver; the binder's row is named by its bound | [class members](SOURCE-ELABORATION.md#class-members) | — |
| A constructor's rest parameter or parameter pattern; a default or statement reading `this` before the instance is complete; a constructor that returns, writes a field with an initializer or one field twice, or assigns fields outside its block and its last `if`'s arms; `super(...)` other than once, as a statement of its body | The instance is allocated at the constructor's end from one value per field | [derived classes](SOURCE-ELABORATION.md#derived-classes) | — |
| A class member with a computed key other than a method's `unique symbol` constant or a static `[Symbol.hasInstance]`; an index signature in a class; a static block reading `this` | A method is a binding and a prototype key; instances are what construction allocates; the block runs before the model allocates the class value | [classes](SOURCE-CONTRACTS.md#classes) | — |
| A private name in inheritance; `#x in o` | A derived instance's base part is a copy, which holds no private slot; the test asks for an own slot | [classes](SOURCE-CONTRACTS.md#classes) | — |
| A static member read through a class that inherits it, optionally or not; `typeof C` of such a class | The model's class value does not hold its base as prototype | [classes](SOURCE-CONTRACTS.md#classes) | — |
| Reads of a class's statics before the class value exists (an instance member reading a private static, a static initializer reading its class other than through an earlier static, a closure reading a static field); an unannotated static field no term states; a static method reading `this`; `super` in a static member; a mutable or optional static field | The model allocates the class value after every static initializer; a static method's receiver is whatever its call passes; a mutable static is module state | [classes](SOURCE-CONTRACTS.md#classes) | — |
| A generic class's instance member or constructor reading its own class | The class value is quantified over its unit's binders, and a module value is read only at ground instances | [classes](SOURCE-CONTRACTS.md#classes) | — |
| An implicit derived constructor forwarding more parameters than its `extends` keyword has characters | Each forwarded parameter needs a source site of its own | [derived classes](SOURCE-ELABORATION.md#derived-classes) | — |
| A class declared in a `case` clause, or one with a static member, a private name, a type parameter or an enclosing generic declaration; one whose name is spelled outside its block or declares something else in the file; a read of it where its binding may be uninitialized, one other than as `new`'s callee, `instanceof`'s right operand or a base, and one in its own members; one extending a top-level class | Its value is its block's and goes to no code, which could define its `[Symbol.hasInstance]`; its instance type is read as a top-level class's under its name; it has no per-evaluation inner binding; a function's body is lowered before the module's top-level code | [a class declared in a block](SOURCE-ELABORATION.md#a-class-declared-in-a-block) | `invalid-local-class-case`, `invalid-local-class-static`, `invalid-local-class-generic`, `invalid-local-class-name`, `invalid-local-class-early`, `invalid-local-class-escape`, `invalid-local-class-self`, `invalid-local-class-top-base` |

**Bindings and scope**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| A binding read before its initialization in an environment the model does not represent: an early pattern binding, a `switch` case block's, a class declaration's, a generator's, a default mentioning its own or a later parameter, a loop head's own name; an early binding without a stated type; an early `let`'s compound, update or logical assignment, or assignment in closure term code | The model's early bindings are one-name `let` and `const` cells of bodies and blocks with a stated type | [lexical bindings before initialization](SOURCE-ELABORATION.md#lexical-bindings-before-initialization) | `invalid-early-pattern-binding`, `invalid-loop-head-own-name`, `shadowed-local-before-declaration` |
| `var` (at module level or in a body); `declare let`, `declare var`; an exported module `let`; a module-level `let` pattern or unannotated module `let` | A `var` exists from entry at `undefined`; outside code may write an ambient binding; an importer reads a live binding; a module cell is a unit boundary with a written type | [module cells](SOURCE-ELABORATION.md#module-cells) | `invalid-exported-module-let`, `invalid-unannotated-module-let` |
| A written `let` pattern in a `for` head, a written `let` in a `for...of` or `for...in` head; a test of a cell holding a union of objects | Cells are lowered by block statements; a cell's known contents are primitive or `defined` | [slot or cell](SOURCE-ELABORATION.md#slot-or-cell) | — |
| An unannotated `let` of `null`, `undefined` or `[]` whose writes grow with it and whose uses expect no one type; a `let` with neither initializer nor annotation | Its contract has no fixed point, or no use states it | [slot or cell](SOURCE-ELABORATION.md#slot-or-cell) | — |
| A mention, in a closure written above it, of a local that shadows an outer binding | The renaming binds the local from its declaration on | [shadowing](SOURCE-ELABORATION.md#shadowing) | `shadowing-dead-zone` |
| A name declared in one `switch` clause and read in another | The lowering gives each clause's statements a scope of their own | [statement forms](SOURCE-ELABORATION.md#statement-forms) | — |
| A declaration after a statement that always jumps, but a function declaration; a name declared only in dead code | The lowering drops what follows a jump, and a hoisted `var` may be named by live code | [statement forms](SOURCE-ELABORATION.md#statement-forms) | `dead-code`, `dead-code-hoisted` |
| A labelled `break` or `continue`; one outside a loop the lowering supports | Loop transfers are lowered to their innermost loop or `switch` | [statement forms](SOURCE-ELABORATION.md#statement-forms) | — |
| An annotated destructuring pattern; a computed or string key in a pattern; a declaration list of several declarators, a pattern among them, at a module's top level or in a `for` initializer | A pattern's types are its value's claims; its keys are plain names; the list's declarators are declarations of their own, which a function's or a closure's body has | [patterns](SOURCE-ELABORATION.md#patterns) | — |
| An import binding no name (`import "m"`) | It runs a module for its effects alone | [default imports](SOURCE-ELABORATION.md#default-imports) | — |
| A re-export TypeScript reports an error in (`export { missing } from "m"`, a binding `m` does not export) | It binds no export of its module, and the host refuses to link it | [re-exports](SOURCE-ELABORATION.md#re-exports) | `invalid-reexport-missing-binding-value-import` |
| A namespace import mentioned other than by a member read or a qualified type name; a call `ns.f(…)` of a member stating a `this` parameter | The namespace object is no binding; the call passes it as receiver | [namespace imports](SOURCE-ELABORATION.md#namespace-imports) | — |
| A non-library global read other than through a member or a call (`const p = process`) | A global is assumed at the members and calls its references select | [imported values](SOURCE-CONTRACTS.md#imported-ambient-and-global-values) | — |

**Types**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| `keyof T`, `T[K]` over a function's own type parameter | They are functions of an instance's key set, which a parameter row does not determine | [computed types](SOURCE-CONTRACTS.md#computed-types) | — |
| A template literal type with a `${string}` hole; `keyof` with a unique-symbol key; `typeof` of a binding whose inferred type is not a record of literals and primitives, or of a class with a static method or private static | No term of the fragment states it exactly | [computed types](SOURCE-CONTRACTS.md#computed-types) | — |
| A mapped type the reader reads as written (an annotation of the file, or a declaration it imports) with an `as` clause or with members; one over `keyof` an indexed type whose value is not `X[P]`, or optional over an index signature's keys | No term states the remapped or index-modified result. A member of such a type reached through `typeof` at a union of literals and primitive families is the type TypeScript computes ([computed types](SOURCE-CONTRACTS.md#computed-types), under the trust surface's computed-types row): the mapped type is not read | [computed types](SOURCE-CONTRACTS.md#computed-types) | `invalid-mapped-type-as-clause`; through `typeof`, `invalid-written-remapped-member-value-import`, refused at a written application inside the member |
| A mapped type whose value is `X[P]` at a union, an array, a class or a type with call signatures, or over keys that are not literals (an index signature's, a unique symbol); one whose value is `X[P]` over a written key union; `-?` without `exactOptionalPropertyTypes` over an optional field whose type has a type parameter, an intersection or `unknown` among its parts, and `-?` written outside the standard library over one whose type may hold `undefined` | Over a written key union TypeScript copies none of `X`'s modifiers, a form no term states; without the option `-?` takes `undefined` from such a part's instance, which no term states, and the reader reads the option only for the standard library's mapped types | [library types](SOURCE-CONTRACTS.md#library-types) | `mapped-literal-keys-value-refused`, `mapped-required-binder-undefined-refused` |
| A mapped type whose value is `X[P]` at a named type with no outer record shape: a class, a host type, a library interface read through its overlay, one with call signatures or a method, one redeclaring a base's member or index differently, one whose shape reaches itself or is needed inside its own definition | A class's instance type holds members `keyof` does not list; a dropped signature or a method's receiver is no member of the mapped record; a redeclared member has two contracts; a cycle has no outer unfolding | [library types](SOURCE-CONTRACTS.md#library-types) | `mapped-named-class-refused`, `mapped-named-call-refused`, `mapped-named-call-refused-value-import`, `mapped-named-method-refused`, `mapped-named-conflict-refused`, `mapped-named-cycle-refused` |
| `ReturnType` of a generic function's `typeof` | TypeScript instantiates the function's type parameters at their bounds, a value type the reader does not state | [computed types](SOURCE-CONTRACTS.md#computed-types) | — |
| A default on a function's, closure's, class's or method's type parameter | The reader does not complete an omitted argument from it | [generic function and constructor types](SOURCE-CONTRACTS.md#generic-function-and-constructor-types) | — |
| An abstract constructor type | Construction is the only rule of a constructor type | [generic function and constructor types](SOURCE-CONTRACTS.md#generic-function-and-constructor-types) | — |
| An intersection with a union holding a type parameter, `(T \| null) & A`; a function type met with a record of readonly or optional fields, methods or an index | It distributes into meets known only at an instance; no clause states such a callable | [intersections of functions and records](SOURCE-CONTRACTS.md#intersections-of-functions-and-records) | — |
| A library global both constructed and read through members, or called and read through a method, other than intrinsics (`Symbol.for`); an object type with construct signatures beside members other than required properties | A class value's type states one construct signature and its static fields | [imported values](SOURCE-CONTRACTS.md#imported-ambient-and-global-values) | — |
| An imported constant initialized by a literal `as const` or holding one | The declaration reader reads it as TypeScript's inferred type, which states primitives and writable records and arrays of them; `as const` makes readonly records and tuples of literal types | [types stated by annotations](SOURCE-CONTRACTS.md#types-stated-by-annotations) | `literal-const-array-constant-value-import` |
| An imported interface its module declares more than once; an imported `const enum` read as a value | The reader resolves an import to one declaration; a `const enum` has no object | [imported values](SOURCE-CONTRACTS.md#imported-ambient-and-global-values) | — |
| A type declared in a block closing over an enclosing type parameter where a nearer one hides it, stated as a contextual type, or naming its parameters in a computed form; an associated-result alias in a block, recursive, or missing an unbounded argument | Its equation is lifted over the enclosing parameters, and the associated-result expansion reads module aliases | [block-scoped type declarations](SOURCE-CONTRACTS.md#block-scoped-type-declarations) | `block-type-hidden-binder-refused`, `block-type-computed-mapped-hidden-binder-refused` |
| `BuiltinIteratorReturn` outside ECMA-262's iterator interfaces | Another specification states those iterators' done value | [library types](SOURCE-CONTRACTS.md#library-types) | `invalid-builtin-iterator-return-value-import` |

**Library and host**

| Construct | Obstacle | Owner | Cases |
| --- | --- | --- | --- |
| Any library signature the overlays do not list (`Math.floor`, `concat`) | Not reviewed; nothing is trusted by default | [library globals](SOURCE-CONTRACTS.md#library-globals) | `invalid-host-global-unreviewed`, `invalid-node-global-unreviewed` |
| `key in o` for a string key `Object.prototype` or `Array.prototype` holds, or a key a function owns or inherits from `Function.prototype` on an operand that may be a function; a class value as `in`'s operand; `in` on an `unknown` a `typeof` test found an object | The model holds no key of the built-in prototypes, nor a function's own `name` and `prototype`, nor a class value's static methods; `typeof` gives `unknown` no narrower type | [`in`](SOURCE-ELABORATION.md#in) | `invalid-in-function-key` (Node), `invalid-open-read-inherited` |
| A regex's property (`lastIndex`, `source`, `flags`, a flag); `in` with a key a regex owns or inherits; a regex where a record stating such a key is expected | The model's regex states methods only | [regular expressions](SOURCE-CONTRACTS.md#regular-expressions) | `invalid-regexp-lastindex-view` (Node) |
| A replacement callback of a regex other than a literal of known shape written at the call; `new RegExp` of a regex pattern; a write to a match result | Not stated: the callback's arguments follow the shape, which code holding the regex may change through `lastIndex` and `compile`; a regex pattern is read through accessors; match results are readonly views | [regular expressions](SOURCE-CONTRACTS.md#regular-expressions) | `invalid-regexp-object-pattern`, `invalid-regexp-replace-shared` (Node) |
| `catch` or `finally` after a void async completion through a `Promise<void>` annotation | `void` denotes `unknown`, and its payload may hide a callable `then` | [async functions and await](SOURCE-CONTRACTS.md#async-functions-and-await) | — |
| A NaN or infinite enum member; a reverse key naming a member; an empty enum | A NaN or infinite value has no literal type; the reverse entry would replace the member; an empty object leaves no record | [enums](SOURCE-CONTRACTS.md#enums) | — |

### Opaque Node URLs

The reviewed URL view admits construction from strings and storage as an
opaque host value. Member reads and writes, URL-valued constructor bases,
and URL-valued `fileURLToPath` arguments are refused; the front end reads
URLs as strings through a host boundary
([URLs as strings](SOURCE-REWRITES.md#urls-as-strings)). External aliases may
attach own properties or alter associated search parameters; admitted uses
avoid their callbacks ([contracts](SOURCE-CONTRACTS.md#nodes-url)).
