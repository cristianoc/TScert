# Python aliasing demo

The same proof checker can expose a Python bug accepted by five Python type
checkers: a dictionary write through an alias invalidates an earlier type
check. The demo translates a restricted Python subset into TScert's
[Fragment](../../tools/fragment.mts). Its OCaml producer and Lean verifier
check that program using the existing typing rules.

## The example

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
restrictions and diagnostic locations across Unicode and CRLF. CI runs it.

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
