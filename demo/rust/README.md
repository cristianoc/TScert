# Rust/Wasm declaration agreement and a Rust front end (demo)

The boundary demo catches a stale TypeScript declaration for valid Rust:
the caller promises `number`, while the compiled Rust/Wasm export returns
`bigint`. It includes an optional build and execution of the actual crossing,
with generated glue and both stages of the repair.

The Rust front end also hands a small subset of Rust to TScert's existing
producer and independent proof checker, through the same
[Fragment](../../tools/fragment.mts) the TypeScript front end writes. Its
verdict concerns that program in the JavaScript model;
[whose semantics](#whose-semantics-a-verdict-covers) states its Rust scope.

## A stale return declaration

Rust's export in [`boundary-return-mismatch/lib.rs`](examples/boundary-return-mismatch/lib.rs):

```rust
#[wasm_bindgen]
pub fn next_id() -> i64 {
    42
}
```

The stale declaration says `export function next_id(): number`. Its
[TypeScript caller](examples/boundary-return-mismatch/caller.ts) is:

```ts
import { next_id } from "./lib.js";

export function jobId(): number {
  return next_id();
}
```

TypeScript accepts this caller, and TScert verifies it assuming its import
meets the declaration. With the actual generated module, `jobId()` returns
`42n`, a `bigint`, on normal return. The declaration agreement check refuses:

```text
disagreed: lib.d.ts against lib.rs
  next_id (lib.d.ts: next_id): result: lib.d.ts states number; Rust i64 requires bigint in JavaScript
```

Updating the declaration to `bigint` exposes the caller's wrong `number`
result to TypeScript and TScert. Updating the caller to `jobId(): bigint`
makes the model/declaration checks pass and execution returns `42n` at the
promised type. This is [`boundary-return/`](examples/boundary-return).

The [parameter-mismatch example](examples/boundary-mismatch/caller.ts) is
also retained: its stale declaration lets `doubled(21)` pass `number`s to
Rust `i64` parameters. The real crossing throws
`TypeError: Cannot convert 21 to a BigInt`. The repaired bigint call returns
`42n`.

## Build and execute the real crossing

This optional command needs `make build`, Rust/Cargo, the
`wasm32-unknown-unknown` target and wasm-bindgen-cli **0.2.130**. The
[official tool and mapping](../../docs/REFERENCES.md#wasm-bindgen) define the
crate/CLI pair. Setup with `rustup target add wasm32-unknown-unknown` and
install that CLI release, for example
`cargo install wasm-bindgen-cli --version 0.2.130 --locked`. Set
`WASM_BINDGEN=/path/to/wasm-bindgen` if it is outside `PATH`.

```sh
node demo/rust/run-boundary.mts
```

It copies the Rust source into a temporary Cargo crate, compiles it in
release mode with `panic = "abort"` and `overflow-checks = false`, generates `--target web` glue and real
`.d.ts` output, and loads the resulting Wasm in Node. Each consumer's
`lib.js` re-exports that same generated module. Node executes the actual
TypeScript caller with type annotations stripped.

| Pairing | TypeScript | Model/declaration checks | Actual execution |
| --- | --- | --- | --- |
| Stale result declaration | accepts | agreement refuses `number` vs `bigint` | returns bigint `42n` under `number` |
| Fresh result declaration, old caller | rejects | caller refused; agreement passes | returns bigint `42n` |
| Fresh result declaration, repaired caller | accepts | pass | returns bigint `42n` under `bigint` |
| Stale parameter declaration | accepts | agreement refuses `number` vs `bigint` | argument-conversion `TypeError` |
| Fresh parameter declaration, old caller | rejects | caller refused; agreement passes | argument-conversion `TypeError` |
| Fresh parameter declaration, repaired caller | accepts | pass | returns bigint `42n` |

The script asserts all six outcomes. Measured on 2026-11-05 with rustc
1.91.1, wasm-bindgen 0.2.130 and the repository's pinned Node, they have
these results. The printed temporary directory retains `commands.json`,
`report.json`, `Cargo.lock`, source snapshots, generated glue/declarations
and Wasm, and the consumers. The report records versions, complete output,
and hashes of the source, manifest, lockfile, generated artifacts and
consumer files. These records describe this run's artifacts; they are not a
proof of artifact provenance in another build or deployment.

This command and all demo checks are manual. They add no CI job or dependency.

## Check the source examples

From the repository root, after `make build`:

```sh
node demo/rust/verify.mts demo/rust/examples/hello.rs
node demo/rust/verify.mts demo/rust/examples/refused.rs
node demo/rust/verify-boundary.mts demo/rust/examples/boundary
node demo/rust/verify-boundary.mts demo/rust/examples/boundary-refused
node demo/rust/verify-boundary.mts demo/rust/examples/boundary-mismatch
node demo/rust/verify-boundary.mts demo/rust/examples/boundary-return-mismatch
node demo/rust/verify-boundary.mts demo/rust/examples/boundary-return
```

- `hello.rs` is verified, each of its eight functions a unit of its own.
- `refused.rs` is refused: `fn widen(x: i32) -> i64 { x + 1 }` computes a
  `number` in the model, and its result is a `bigint`. `rustc` rejects it
  too.
- `boundary/` passes: the crate's four exports, the caller's three
  functions, and the agreement of `lib.d.ts` with `lib.rs`.
- `boundary-refused/` is refused: its caller passes a `number` to `scale`,
  whose `i64` parameter is a `bigint` in `lib.d.ts`; the verifier refuses the
  call (`tsc` refuses it too).
- `boundary-mismatch/` is refused: its `lib.d.ts` declares
  `scale(x: number, k: number): number`, its caller passes numbers, and
  `tsc` and TScert both accept the caller against that declaration; the
  agreement check refuses it, since `lib.rs` takes `i64`s.

The model/declaration command refuses a caller that imports no Rust export
through `./lib.d.ts`. Its final `passed` label means the Rust model units,
caller units and declaration agreement all pass. Each command exits 0 when
its checks pass and prints the directory
holding what each run wrote (`fragment.json`, `flow.json`, `claims.json`,
`evidence.json` and the verifier's logs).

## How it works

1. `parse.mts` tokenizes and parses the file into a small Rust tree: a
   hand-written recursive-descent parser for exactly the subset, its spans
   UTF-16 offsets of the file, the unit the Fragment counts in. (`syn` would
   need a Rust binary, a build, and a converter to JSON of about the
   parser's size.)
2. `lower.mts` maps the tree onto the Fragment, typed against
   `tools/fragment.mts`, and refuses any other construct with its line.
3. `stages.mts` runs the stages `pipeline/verify-source.mts` runs after its
   parse: `verifier --lower-control-flow`, the producer, `verifier
   --produce-units` and `verifier --check-units`, through the shared stage
   store, with 60-second process limits and a retained source snapshot.
4. `verify-boundary.mts` adds the caller's check through
   `pipeline/verify-source.mts` and the agreement of the two signatures
   ([the boundary](#the-boundary)).

## The subset and its mapping

| Rust | Fragment (the TypeScript form it stands for) |
| --- | --- |
| `fn f(x: T, …) -> R { … }`, optionally `pub` | a strict, synchronous function declaration |
| `i32`, `u32`, `f64` | `number` |
| `i64` | `bigint` |
| `bool` | `boolean` |
| `String`, `&str` | `string` |
| `struct S { a: T, … }` | the record type `{ readonly a: T; … }` |
| `let x = e;`, `let x: T = e;` | `const x = e;`, `const x: T = e;` |
| `return e;`, the body's tail expression | `return e;` |
| `if c { … } else { … }` as the body's tail, or as a statement | `if (c) { … } else { … }`, a tail arm's value returned |
| `if c { a } else { b }`, arms only expressions, as a value | `c ? a : b` |
| integer literal | a `number` literal at `i32`/`u32`, a `bigint` literal at `i64` |
| float literal, string literal (`\n \t \\ \" \'`), `true`, `false` | the same literal |
| `a + b`, `a - b`, `a * b`, `-a` on `i64` | signed wrapping after the arithmetic |
| the same operations on `i32`, `u32`, `f64` | model-number arithmetic |
| `a / b`, `a % b` on `i64` | truncating arithmetic, with zero and MIN/-1 throws |
| `a / b`, `a % b` on `f64` | `a / b`, `a % b` |
| `a + b` on strings (`String + &str`) | `a + b` |
| `<`, `<=`, `>`, `>=`; `==`, `!=` | the same comparisons; `===`, `!==` |
| `&&`, `\|\|`, `!` on `bool` | `&&`, `\|\|`, `!` |
| `&e`, `e.to_string()` of a string | `e` |
| `S { a: e, … }`; `e.a` | an object literal, fields in source order; a read of `a` |
| `f(e, …)` of a function of the file | a call |

Precedence is Rust's for these forms: postfix (calls, fields,
`.to_string()`), then unary, then `* / %`, then `+ -`, then the
comparisons, which do not chain, then `&&`, then `||`, each binary level
associating left.

**Types the front end computes.** The source-only check assumes a program
`rustc` accepts; its parser and lowering check no Rust typing rule. The
optional real-crossing command compiles its Rust snapshot with Cargo.
The front end computes each expression's Rust type for two lowerings: an
unsuffixed integer literal takes the type its context fixes (the other
operand, a `let`'s annotation, a parameter at a call, the result at a
`return` or tail, a struct field, through unary, binary and conditional
expressions), and one without such a context is refused rather than
defaulted to `i32`; and `/`, `%` and `!` are admitted only at the types
above. Integer literals are decimal, with `_` and the suffixes `i32`, `u32`,
`i64`; an `i64` literal's digits reach the `bigint` literal unrounded.

**Blocks.** A final expression without `;` is a block's tail. An expression
statement other than an `if` whose arms have no tail is refused, so nothing
is discarded and nothing turns into a return. A name bound twice in one
function (Rust's shadowing) is refused.

Refused, among others: other integer and float types, `char`, `as`, `/`
and `%` on `i32`/`u32`, bitwise and shift operators, `mut`, assignment,
loops, `match`, closures, generics, references other than `&e` and `&str`,
methods other than `to_string`, macros, `impl`, traits, `Option`,
`Result`, `?` and `unsafe`.

## Whose semantics a verdict covers

TScert's verdict is about the JavaScript-model program the Fragment
denotes: for arguments of the parameter types it returns a value of its
result type, throws, or runs forever, and never gets stuck
(`checkUnitJson_safe`, per unit, under `EnvOk` of its inputs, the module
functions it calls at their claimed signatures among them). The mapping is
trusted; the agreements and differences below delimit its correspondence
with Rust. No whole-program simulation is claimed.

- **`i64`.** The release profile has overflow checks disabled
  ([Rust's operator and profile specifications](../../docs/REFERENCES.md#rust-integer-overflow)).
  Parameters wrap to signed 64-bit integers, as the bigint adapter does.
  Addition, subtraction, multiplication and negation wrap after each operation.
  Division and remainder truncate toward zero; a zero divisor and `MIN / -1`
  (also `MIN % -1`) take an exceptional transition. Operands are evaluated
  once, in source order. The model represents a panic as a throw; exception
  identity and messages are outside the safety claim.
  [`I64.lean`](../../lean/Verification/Semantics/I64.lean) defines the bounded
  integers and proves wrapping range, identity, modular congruence, round
  trips, and equality of the emitted truncating-remainder formula with
  signed wrapping. `tdiv_range`, `tmod_range` and `divRem_exact` establish
  the exact normal arithmetic results. `adapter_result`, `adapter_effect`
  and `adapter_error` prove the pure adapter's result bound and preservation
  of normal and exceptional body effects. This adapter theorem concerns an
  integer/heap function; correspondence with core evaluation of the generated
  Fragment remains a Rust-translation premise.
- **`i32` and `u32`.** Arithmetic uses model numbers. Overflow can change
  values and branches relative to Rust; a Rust correspondence premise for
  these types requires a separate bounded translation.
- **`f64`.** Arithmetic and comparisons use the model's binary64 operations.
- **Strings.** Rust's are UTF-8, JavaScript's UTF-16. `+` and `==` agree;
  `<` orders by bytes in Rust and by code units in JavaScript, which differ
  for a character at or above U+10000 against one in U+E000–U+FFFF. `String`
  and `&str` are one type: the subset has no mutation, so ownership and
  borrowing are not observable.
- **Structs** are nominal in Rust and records in the model: two structs
  with the same fields are interchangeable in the model, and a parameter's
  guarantee covers every record of its type, Rust's values among them.
- **Typing.** For a file `rustc` rejects, a verdict is about the model
  program only. For one it accepts, Rust's typing already gives that a
  function returns a value of its result type on normal return; the
  verdict is TScert's independent check of the same body, in the model, at
  the same signature.

## The boundary

`verify-boundary.mts <dir>` reads `lib.rs` (the crate, its exports marked
`#[wasm_bindgen]`), `lib.d.ts` (the declaration shipped for it), `caller.ts`
(importing from `./lib.js`) and a strict `tsconfig.json` (Node16 resolution
takes `./lib.js` to `./lib.d.ts`). `wasm-bindgen`'s mapping, by position:

| Rust | parameter | result |
| --- | --- | --- |
| `i32`, `u32`, `f64` | `number` | `number` |
| `i64` | `bigint` | `bigint` |
| `bool` | `boolean` | `boolean` |
| `String` | `string` | `string` |
| `&str` | `string` | refused (`wasm-bindgen` returns no borrowed `str`) |
| a struct | refused (exported as a class owning wasm memory) | refused |

It establishes three results, each by its owner:

- **The Rust functions in the model**: each unit is safe at its
  signature (TScert's theorem).
- **The caller**: each unit is safe assuming each import meets the
  declaration TypeScript resolves it to in `lib.d.ts` (the same theorem,
  the import an input at its declared type).
- **Agreement**: each such declaration equals, in every field
  (parameters, result, effect, receiver, rest; spans aside), the signature
  the table gives the Rust export of its name; a generic, overloaded or
  construct declaration, a missing export, or any difference is refused.
  The success decision runs `boundary-check`, which rechecks both files' evidence,
  constructs their source-bound assembly and checks primitive graph attachments.
  The Node comparison supplies mismatch diagnostics.

**What the caller's safety rests on.** Both model checks and Lean's linked
assembly decision must pass. `boundary-check <rust-artifacts> <caller-artifacts>`
reads each directory's `fragment.json`, `claims.json` and `evidence.json`.
[`Demo.linked_safe`](../../lean/Verification/Source/Demo.lean) takes exactly
its Boolean success condition and the five runtime simulations described
below. The executable construction and proofs are owned by
[certified imports](../../docs/SOURCE-CONTRACTS.md#certified-imports).

Build the executable with `cd lean && lake build boundary-check`.
`node demo/rust/check-primitives.mts` runs standalone source-bound matching
and forged-input controls without opening the TypeScript compiler channel.

**The glue, assumed.** The module is built for `wasm32-unknown-unknown`
with `panic = "abort"` by `wasm-bindgen` with `--target web`, its
JavaScript unmodified, `TextEncoder`, `TextDecoder`, `WebAssembly` and
`BigInt` untampered, and no custom panic hook. The glue then converts a
`number` to `i32`/`u32` modulo 2³² (`NaN` and infinities to 0, fractions
truncated) and a `u32` result back by `>>> 0`; an `f64` exactly; a `bigint`
to `i64` modulo 2⁶⁴; a `boolean` to 0/1; a `string` to UTF-8 in memory it
allocates (a lone surrogate replaced by U+FFFD; allocation may fail, a
throw), and a `String` result from UTF-8. The caller's check establishes
each argument is a primitive of its type, so no conversion runs code of the
program. The value the Rust function receives may still differ from the
caller's: `1.5`, `2**32` and `NaN` reach an `i32` parameter as `1`, `0` and
`0`, which `number` cannot state and the verdict does not cover.

**Panics** trap, and the glue surfaces the trap as a thrown
`WebAssembly.RuntimeError` at the call, an outcome the caller's verdict
allows. After a trap the instance's state, its allocator's among it, is
unspecified: the argument covers calls before any trap.

**The build.** The project's build is responsible for shipping the declaration
and loaded module for its Rust source. The source-only command compares
the `.d.ts` with the Rust source; its fixture declarations are hand-written. The optional real-crossing command
builds its snapshot and executes the generated module, retaining its actual
fresh declarations beside deliberately stale consumer declarations.
The declaration's effect is the ordinary one (a call may change anything),
which over-approximates a function of primitives.

## Conditional linked safety and trust

[`Demo.linked_safe`](../../lean/Verification/Source/Demo.lean) proves
finite-observation safety for every computed caller entry and every value of
its written primitive parameter types. Its premise `input.accepted = true`
is exactly the success condition selecting exit zero in `boundary-check`.
The result of that check supplies the accepted caller, concrete closures,
capture ranks and slots, `WellLinked`, both primitive graph attachments,
signature transport, entry separation and admitted assignment. Execution
starts after initialization in the empty world and heap. The proof applies
[`LinkedRuntime.end_to_end`](../../lean/Verification/Source/LinkedRuntime.lean).
The source-bound construction and checker proofs are owned by
[certified imports](../../docs/SOURCE-CONTRACTS.md#certified-imports).

The runtime premises are simulations with progress, preservation of terminal
contracts, and deterministic target observation machines whose terminal
states have no outgoing steps. `Machine.Safe` requires every successor to
be safe through the observation bound. Each machine describes the whole
linked execution; an
observation step may group implementation steps. Their named trust is:

- `typescriptLowering`: the caller's lowering and extraction faithfully
  describe its execution, types and effects.
- `rustTranslation`: the Rust Fragment faithfully describes the admitted
  source, including wrapping bigint conversion, each bounded operation,
  evaluation order and panic behavior.
- `rustc`: the selected compiler and Wasm backend preserve that behavior
  under the recorded release profile. The `i64` examples use wrapping
  arithmetic; the broader demo's other integer types require their own
  correspondence argument.
- `wasmBindgen`: the unmodified glue preserves primitive conversion and
  result contracts, allocation and panic/trap behavior. Its state invariant
  must hold on throws, or the protocol must prevent reuse after a trap.
- `engine`: Node/JavaScript and Wasm execute according to those machines;
  module loading and artifact provenance connect the retained source,
  declarations, glue, Wasm and entry to the actual deployment.

Each named premise is a `Demo.Started` simulation with its related initial
state. Runtime machines and these witnesses are implementation premises.
Initialization is complete, exports remain fixed, and callable dependencies
are acyclic. The checker admits fixed synchronous functions, singleton units,
primitive entry parameters and imports through `./lib.d.ts`. Module
initialization code, external captures, generic bodies and array built-ins
are refused. Mutual recursion across units, live-binding writes, re-exports
and cyclic initialization are outside this scope.

`node demo/rust/check-i64.mts` compiles the primitive examples with explicit
release arithmetic flags and checks an overflowing product, MIN negation,
signed division/remainder, and all four panic cases. These are observations
of the installed native rustc, rather than a proof about its Wasm backend.
The pipeline's `rust-i64-identity`, `rust-i64-overflow`, `rust-i64-division`
and `rust-i64-calls` cases run Rust source through Fragment lowering,
production and Lean acceptance. The source/evidence controls in
`demo/rust/controls.mts` bypass Node comparison and forge signatures, bodies,
captured function associations and call targets. They check existing
source/evidence consistency. Standalone serialized-assembly controls exercise wrong targets, ranks,
external classification and attachment rows against the structural checkers.
`check-primitives.mts` exercises the source-bound CLI with same-module captures
and the boundary's arithmetic helpers, an independently accepted stale return
declaration, forged export signatures and capture associations, and missing
export evidence.

`node demo/rust/run-boundary.mts --i64-only` builds the real Wasm module and
observes out-of-range bigint conversions, overflowing products, signed
negation, division and remainder, and panic cases. Each observation loads a
fresh instance. The default command also checks the declaration/caller
scenarios. Node signature diagnostics are reported alongside acceptance;
`passed` requires both acceptance checks and Lean's source-bound assembly.
Generated arithmetic nodes have distinct, nonempty intervals within the Rust
source, each containing the source character that prompted its generation.
The producer's and verifier's identity and span checks apply to them.
