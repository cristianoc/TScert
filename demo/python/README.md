# A Python front end for TScert (demo)

A minimal front end that reads a small subset of Python and hands it to
TScert's own back end: the Lean verifier's control-flow lowering, the OCaml
producer's claims, the Lean evidence search and the Lean check. The producer
and the verifier run unchanged; the front end writes the same Fragment
document (`tools/fragment.mts`) that the TypeScript front end writes.

It is a demonstration of the wire, not a verifier for Python: TScert's
calculus models JavaScript, and the demo gives each Python form the meaning of
the JavaScript form it is mapped to. [Limits](#limits) states where the two
differ.

## Run it

From the repository root, after `make build`:

```sh
node demo/python/verify.mts demo/python/examples/hello.py
node demo/python/verify.mts demo/python/examples/refused.py
```

`hello.py` is verified, each of its five functions a unit of its own.
`refused.py` is refused: under the JavaScript model, `x + "a"` with `x` an
`int` is a string, and the function's result annotation is `int`:

```text
unverified: demo/python/examples/refused.py
  unverified inc@4
    reject: source expression obligation at [35,42): evidence search failed: no derivation of its return-contract claim
    obligation: The available claim for x + "a" is string. This return requires bigint.
    line 2: return x + "a"
```

The command exits 0 when every unit is verified, and prints the directory
holding what the run wrote: the Python syntax tree, `fragment.json`,
`flow.json`, `claims.json`, `evidence.json` and the verifier's logs.

## How it works

1. `py_ast.py` parses the file with Python's own `ast` module and prints the
   tree as JSON, each node's span in UTF-16 offsets of the file, the unit the
   Fragment counts in.
2. `lower.mts` maps that tree onto the Fragment, typed against
   `tools/fragment.mts`, and refuses any other construct with its line.
3. `verify.mts` writes `fragment.json` and runs the stages
   `pipeline/verify-source.mts` runs after its parse: `verifier
   --lower-control-flow`, the producer, `verifier --produce-units` and
   `verifier --check-units`. It calls them directly, without the stage store.

## The subset and its mapping

| Python | Fragment (the TypeScript form it stands for) |
| --- | --- |
| module-level `def f(x: T, …) -> T:` | a function declaration, strict and synchronous |
| annotation `int` | `bigint` |
| annotation `str` | `string` |
| annotation `bool` | `boolean` |
| `return e` | `return e` |
| `if c: … elif …: … else: …` | `if (c) {…} else {…}`, an `elif` a nested `if` |
| `a if c else b` | `c ? a : b` |
| integer, string, `True`, `False` literals | `bigint`, string, Boolean literals |
| `a + b`, `a - b`, `-a` | `a + b`, `a - b`, `-a` |
| `<`, `<=`, `>`, `>=` | the same relational operators |
| `==`, `!=` | `===`, `!==` |
| `and`, `or`, `not` | `&&`, `\|\|`, `!` |

Each parameter and the result must be annotated with `int`, `str` or `bool`.
Anything else is refused by the front end: other statements (assignment,
loops, calls, `pass`), other operators (`*`, `/`, `//`, `%`, `**`), chained
comparisons, other annotations, defaults, `*args`, decorators, `async def`,
and module-level code other than `def`.

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
