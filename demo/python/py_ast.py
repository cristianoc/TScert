"""Print the syntax tree of a Python source file as JSON, using Python's own
`ast` module.

Each node is an object with `_type` (the node's class name), `span` (its
start and end offsets in UTF-16 code units of the whole file, the unit the
Fragment's spans count in) when the node has a position, and one entry per
field of the node. An `int` constant is written as `{"int": "<digits>"}`, so
its digits pass through JSON unrounded; a constant of another kind than
`bool`, `int`, `str` or `None` is written as `{"other": "<class name>"}`.

Usage: python3 -I py_ast.py <file.py>
"""

import ast
import json
import re
import sys


def utf16_length(text):
    return len(text.encode("utf-16-le")) // 2


def main(path):
    with open(path, "rb") as handle:
        data = handle.read()
    source = data.decode("utf-8")
    tree = ast.parse(source, filename=path)

    # Each line's bytes and its start offset, in UTF-16 code units. The
    # tokenizer ends a line at \r\n, \r or \n.
    lines = re.split(rb"(?<=\r\n)|(?<=\r)(?!\n)|(?<=\n)", data)
    starts = []
    offset = 0
    for line in lines:
        starts.append(offset)
        offset += utf16_length(line.decode("utf-8"))

    def at(lineno, col_bytes):
        prefix = lines[lineno - 1][:col_bytes].decode("utf-8")
        return starts[lineno - 1] + utf16_length(prefix)

    def constant(value):
        if value is None or isinstance(value, (bool, str)):
            return value
        if isinstance(value, int):
            return {"int": str(value)}
        return {"other": type(value).__name__}

    def node(n):
        out = {"_type": type(n).__name__}
        if getattr(n, "end_lineno", None) is not None:
            out["span"] = [at(n.lineno, n.col_offset), at(n.end_lineno, n.end_col_offset)]
        for name, value in ast.iter_fields(n):
            if name == "value" and isinstance(n, ast.Constant):
                out[name] = constant(value)
            else:
                out[name] = convert(value)
        return out

    def convert(value):
        if isinstance(value, ast.AST):
            return node(value)
        if isinstance(value, list):
            return [convert(v) for v in value]
        return constant(value)

    out = node(tree)
    out["source"] = source
    json.dump(out, sys.stdout)


if __name__ == "__main__":
    main(sys.argv[1])
