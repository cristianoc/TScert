# Python proof-checking demo

The same proof checker can expose a Python bug accepted by five Python type
checkers: a dictionary write through an alias invalidates an earlier type
check. The demo translates a restricted Python subset into TScert's
[Fragment](../../tools/fragment.mts). Its OCaml producer and Lean verifier
check that program using the existing typing rules.

## Tensor rank contracts

The tensor mode extends the existing [external-value contracts](../../docs/SOURCE-CONTRACTS.md#modeling-a-library)
and readonly record types. Native operators are imported callable contracts;
the OCaml producer selects their overloads and Lean checks each application
and the function's result. The proof checker has no tensor-specific rule.

A common batch-size-one failure is [`batch_squeeze.py`](examples/tensors/batch_squeeze.py):

```python
from rank_contracts import Column, Vector

def predict_vector(predictions: Column) -> Vector:
    return predictions.squeeze()
```

`Column` states rank 2 with last dimension 1; `Vector` states rank 1.
With input shape `[1, 1]`, `squeeze()` removes both singleton axes and
returns a scalar. [`fixed_squeeze.py`](examples/tensors/fixed_squeeze.py)
uses `squeeze(-1)`, which removes the last axis and preserves the batch axis.
The contracts follow [PyTorch's documented operations](../../docs/REFERENCES.md#pytorch-tensor-operations).

After `make build`, these commands need Python's parser but no PyTorch installation:

```sh
node demo/python/verify.mts --tensors demo/python/examples/tensors/batch_squeeze.py
node demo/python/verify.mts --tensors demo/python/examples/tensors/fixed_squeeze.py
node demo/python/test-tensors.mts
```

The first command exits 1 with the actual return obligation:

```text
unverified predict_vector@48
  obligation: predictions.squeeze() may return rank 0 (scalar) or rank 1 (vector). This return requires rank 1 (vector).
  line 5: return predictions.squeeze()
```

The repair exits 0 and reports `verified`. The rank explanation is read from
the checker's diagnostic table; it does not decide the verdict.

| Source | Contract and result | TScert |
| --- | --- | --- |
| `batch_squeeze.py` | `Column` → `Vector`; `squeeze()` may return a scalar | `unverified` |
| `fixed_squeeze.py` | `Column` → `Vector`; `squeeze(-1)` preserves the batch axis | `verified` |
| `unchecked_squeeze.py` | `Matrix` → `Vector`; its last dimension need not be 1 | `unverified` |
| `bad_errors.py` | `Column - Vector` has rank 2; a per-example `Vector` is required | `unverified` |
| `fixed_errors.py` | squeeze the column's last axis before subtracting | `verified` |
| `scalar_loss.py`, `fixed_loss.py` | both expressions return `Scalar` | both `verified` |

The broadcasting counterexample uses predictions `[[1.0], [2.0]]` and
targets `[1.0, 2.0]`. The predictions match the targets, but the broadcast
subtraction yields a `[2, 2]` error matrix and loss `0.5`; the repaired loss
is `0.0`. A scalar return contract alone permits both results. The
per-example result contract exposes the wrong rank before reduction.

### Native contract and proof scope

[`rank_contracts.py`](examples/tensors/rank_contracts.py) gives Python callers
`Annotated[Tensor, …]` aliases: `Scalar` (rank 0), `Vector` (rank 1), `Matrix`
(rank 2), and `Column` (rank 2, last dimension 1). These are rank contracts;
they state no equality between different tensors' batch lengths. Other tensor
annotations, general imports, in-place operations, output parameters and
other methods are refused. Function bodies contain return statements only;
tensor truthiness and control flow are outside this subset. The imported contract names cannot be rebound.

The model projects tensor metadata onto readonly fields. `ndim` is the
rank; the internal `%lastDimension%` field is the last extent. The external
operator contracts in `tensors.mts` state, on normal return:

- column-minus-vector returns a matrix; vector-minus-vector returns a vector;
- `square()` preserves rank 1 or 2;
- column `squeeze()` returns a scalar or vector; column `squeeze(-1)` returns a vector;
- whole-tensor `mean()` returns a scalar;
- these out-of-place calls preserve the inputs' represented metadata.

These contracts assume exact ordinary CPU strided PyTorch tensors, standard
operators, sequential execution and no custom dispatch or hooks. The runtime
controls exercise float32 tensors without autograd. Squeezed tensors share
numerical storage; the model describes metadata, and the source subset
admits no tensor data mutation. The contracts and Python projection are
reviewed assumptions. Lean proves the translated program safe relative to
them. Tensor dimensions, dtype, device compatibility, numerical values,
gradients, exception freedom and correctness of the learning objective have
no proved contract in this demo.

### Tensor validation and comparison

With PyTorch 2.15.0 installed:

```sh
python -B demo/python/tensor_runtime.py
```

The runtime executes the source fixtures and checks four batch sizes
(including 0 and 1) and sixteen pairs of tensor lengths against the assumed
operator rank contracts. It checks input values and metadata remain unchanged.
The optional model tests also forge a producer claim that `squeeze()` returns `Vector`: evidence
search and final checking refuse it.

Measured on 2026-11-05, the same five pinned Python checker releases listed
below accept all six tensor comparison fixtures, including the three rank
bugs; each rejects an ordinary non-Tensor return. They interpret the
`Annotated` aliases as `Tensor` and do not enforce this rank metadata.
Reproduce with `uv` and real PyTorch declarations available to every checker:

```sh
uv run --no-project --python 3.13 --with torch==2.15.0 --with mypy==2.4.1 --with pyright==1.1.414 --with basedpyright==1.40.2 --with ty==0.0.98 --with pyrefly==1.4.1 python demo/python/compare-tensors.py
```

The printed temporary directory retains commands, versions, source hashes
and complete outputs. This comparison concerns the listed releases and the
rank contract; it is no claim about shape-aware runtime checkers.

## Mutable aliasing

[`aliased_arguments.py`](examples/aliased_arguments.py):

```python
from typing import TypedDict

class Payload(TypedDict):
    title: str | int

def display_title(payload: Payload, pending: Payload) -> str:
    if isinstance(payload["title"], str):
        pending["title"] = 0
        return payload["title"]
    return "untitled"
```

The caller may pass the same dictionary twice. With `payload = {"title":
"Quarterly report"}`, `display_title(payload, payload)` returns integer `0`.
A caller using the promised string's `.upper()` raises `AttributeError`.
Every argument and write meets the stated contract; writing `pending` can
invalidate a narrowing of `payload`. Distinct objects produce the promised
string. [`stale_title.py`](examples/stale_title.py) makes the alias explicit
with `alias = payload` inside the function.

The comparison includes both preserving a saved value and establishing a
fresh fact after mutation:

| Program | Value returned | TScert |
| --- | --- | --- |
| [Aliased parameters](examples/aliased_arguments.py) | integer `0` for the same-object call | `unverified` at the return |
| [Local alias](examples/stale_title.py) | integer `0` after the aliased write | `unverified` at the return |
| [Snapshot](examples/snapshot_title.py) | saved string across mutation | `verified` |
| [Fresh check](examples/rechecked_title.py) | string replacement or fallback after testing the current field | `verified` |
| [Fresh check of aliased parameters](examples/rechecked_arguments.py) | current string or fallback, for same or distinct objects | `verified` |

The stale read's diagnostic states `string | bigint` where the return
requires `string`; `bigint` represents Python's `int`. The snapshot repair
saves `title = payload["title"]`, tests `isinstance(title, str)` and returns
`title`. The fresh-check repair tests the dictionary field after its write.
Its tests cover string and integer replacements and a return expression
using the freshly checked field.

## Run it

From the repository root, with Python 3.10+ and after `make build`:

```sh
python3 -I -B demo/python/runtime.py
node demo/python/verify.mts demo/python/examples/stale_title.py
node demo/python/verify.mts demo/python/examples/aliased_arguments.py
node demo/python/verify.mts demo/python/examples/snapshot_title.py
node demo/python/verify.mts demo/python/examples/rechecked_title.py
node demo/python/verify.mts demo/python/examples/rechecked_arguments.py
node demo/python/test.mts
```

The first two verdicts are `unverified` (exit 1); all three repair files are
`verified` (exit 0). `runtime.py` executes both counterexamples and checks the repair
with empty strings, astral Unicode and large integers, string and integer
replacements, and same and distinct parameter objects.
`test.mts` checks these verdicts, the original primitive examples, source
restrictions and diagnostic locations across Unicode and CRLF.

The verifier command retains a source snapshot, Python syntax tree,
`fragment.json`, `flow.json`, `claims.json`, `evidence.json` and the search
and checking logs in the printed temporary directory. Only complete,
independently checked unit verdicts produce `verified`. The backend stages
use the repository's stage store and 60-second limits.

## Python type checker comparison

Measured on 2026-11-05, all five releases below accept both aliasing
counterexamples, the snapshot repair and the fresh-check repair with zero
reported errors. Each
also rejects the control `def ordinary_error() -> str: return 0`.

| Checker | Release | Configuration |
| --- | --- | --- |
| mypy | 2.4.1 | `--strict` |
| Pyright | 1.1.414 | `typeCheckingMode: strict` |
| basedpyright | 1.40.2 | `typeCheckingMode: strict` |
| ty | 0.0.98 | `check` defaults |
| Pyrefly | 1.4.1 | `--preset strict` |

Reproduce the comparison with `uv` installed (downloads the pinned releases):

```sh
node demo/python/compare.mts
```

The printed temporary directory holds `report.json`: exact commands,
versions, source hashes, exit statuses and full output, including the
ordinary-error controls. These are results for those releases and settings;
other checkers and future releases require their own measurements.

## What this demonstrates

The interesting obligation is the relation between a heap read, an aliasing
write and a later read. TScert's existing record contracts and heap rules
handle it for a Python-origin Fragment, including possible aliasing between
parameters. The snapshot and fresh checks succeed through those same stages. The front end
recognizes Python syntax and supplies contracts; it contains no rule that
recognizes or rejects this example's mutation pattern.

The theorem proves safety of the translated calculus program. A theorem
relating Python execution to that program is a separate obligation. For
these aliasing examples, the correspondence assumes exact built-in
`dict`, `str` and `int` values satisfying all required fields; built-in
`isinstance` and `str`; and sequential execution without concurrent mutation.
Dictionary reads and writes denote the same required string-keyed locations,
local bindings preserve aliases, `isinstance(value, str)` tests the string
arm, and a saved string value survives a dictionary write. Subclasses with
custom behavior are outside this correspondence. These assumptions are
review obligations for the Python demo; TypeScript's trust surface is
unchanged. The broader demo's differences are stated in [Limits](#limits).

## How it works

1. `py_ast.py` parses the file with Python's own `ast` module and prints the
   tree as JSON, each node's span in UTF-16 offsets of the file, the unit the
   Fragment counts in.
2. `lower.mts` maps that tree onto the Fragment, typed against
   `tools/fragment.mts`, and refuses any other construct with its line.
3. `verify.mts` writes `fragment.json` and runs the stages
   `pipeline/verify-source.mts` runs after its parse: `verifier
   --lower-control-flow`, the producer, `verifier --produce-units` and
   `verifier --check-units`.

## The subset and its mapping

| Python | Fragment (the TypeScript form it stands for) |
| --- | --- |
| module-level `def f(x: T, …) -> T:` | a function declaration, strict and synchronous |
| annotation `int` | `bigint` |
| annotation `str` | `string` |
| annotation `bool` | `boolean` |
| union annotation | the union of both contracts |
| total `TypedDict` with required annotated fields | a mutable record contract, every field retained |
| `value["key"]`, `value["key"] = e` | record field read and write |
| outer-block `name = e`, once per name | immutable local binding, preserving object identity |
| `isinstance(e, str)` | a string-shape test |
| `return e` | `return e` |
| `if c: … elif …: … else: …` | `if (c) {…} else {…}`, an `elif` a nested `if` |
| `a if c else b` | `c ? a : b` |
| integer, string, `True`, `False` literals | `bigint`, string, Boolean literals |
| `a + b`, `a - b`, `-a` | `a + b`, `a - b`, `-a` |
| `<`, `<=`, `>`, `>=` | the same relational operators |
| `==`, `!=` | `===`, `!==` |
| `and`, `or`, `not` | `&&`, `\|\|`, `!` |

Each parameter and result has a supported annotation. The only import is
an initial `from typing import TypedDict`; a record annotation refers to a
preceding declaration. Locals bind once in a function's outer block;
parameters and locals cannot shadow the built-ins used by the translation.

Other forms are refused with a source line: optional or readonly fields,
unsupported field annotations, dictionary construction, computed keys,
rebound locals, branch-local bindings, loops, general calls, defaults,
`*args`, decorators, `async def`, generic declarations and other module code.
The primitive examples are [`hello.py`](examples/hello.py) and
[`refused.py`](examples/refused.py).

## Limits

What a verified unit means is TScert's guarantee for the JavaScript-model
program its Fragment denotes: for arguments of the annotated types, it does
not get stuck and does not return a value outside its result type. It may
throw or run forever. That the Python function behaves as that program does
is the demo's mapping, trusted, reviewed only against the points below.

- **`int` as `bigint`.** Both are arbitrary-precision integers, and `+`, `-`,
  unary `-` and the comparisons agree on two of them.
- **`bool` is not an `int` in the model.** In Python `bool` is a subclass of
  `int`: `True + 1 == 2` and `inc(True)` is a valid call. In the model a
  Boolean is no `bigint`: `b + 1` with `b: bool` is refused, and the
  guarantee for an `int` parameter covers integer arguments, not `True` or
  `False`. Likewise `1 == True` is `True` in Python, and `1n === true` is
  `false`.
- **Mixed `+` follows JavaScript.** JavaScript converts a `bigint` to a
  string where one operand is a string, and Python raises `TypeError`. So
  `def f(s: str, n: int) -> str: return s + n` is verified: its model returns
  `"a1"` for `("a", 1)`, and Python throws. Python's outcome here, a throw,
  is one the guarantee allows, but the verdict was derived from the model's
  value, not from Python's error. The refusal of
  `refused.py` likewise comes from the model's result type, `string`.
- **Strings.** A Python `str` is a sequence of code points, a JavaScript
  string one of UTF-16 code units. `+` agrees; `<` orders two strings
  differently where they hold characters outside the Basic Multilingual
  Plane. Values differ there, types do not.
- **Dictionary equality.** Python compares dictionaries by their contents;
  the model compares object identity. The aliasing examples use string-shape
  tests and perform no dictionary equality comparison.
- **Truthiness.** `if`, `and`, `or`, `not` and the conditional expression
  test truthiness, which agrees on these three types: `0`, `""` and `False`
  are falsy in Python, as `0n`, `""` and `false` are in JavaScript; `and` and
  `or` return an operand in both.
- **Falling off the end.** A Python function that reaches its end returns
  `None`, and the model's `undefined`; neither is an `int`, `str` or `bool`,
  so such a function is refused.
- **Annotations are assumptions.** Python does not check annotations at run
  time; the guarantee assumes each caller passes values of the annotated
  types, as TScert assumes of a TypeScript caller.
