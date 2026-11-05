"""Execute the alias counterexamples and the snapshot repair under CPython."""

import importlib.util
from pathlib import Path


def load(name):
    path = Path(__file__).parent / "examples" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.display_title


def main():
    stale = load("stale_title")
    arguments = load("aliased_arguments")
    snapshot = load("snapshot_title")
    for name, call in [("stale_title", lambda p: stale(p)),
                       ("aliased_arguments", lambda p: arguments(p, p))]:
        payload = {"title": "Quarterly report"}
        result = call(payload)
        assert type(result) is int and result == 0, (name, result)
        try:
            result.upper()
        except AttributeError:
            print(f"{name}: promised str, returned {result!r} (int); .upper() raises AttributeError")
        else:
            raise AssertionError(f"{name}: expected the concrete caller failure")
    for value in ["Quarterly report", "", "🦉", 0, -1, 2**100]:
        payload = {"title": value}
        result = snapshot(payload)
        expected = value if type(value) is str else "untitled"
        assert type(result) is str and result == expected
        assert payload["title"] == (0 if type(value) is str else value)
    # Distinct inputs also satisfy the two-parameter contract. Its unsafe
    # execution specifically requires the permitted same-object inputs.
    assert arguments({"title": "Report"}, {"title": "Other"}) == "Report"
    print("snapshot_title: returns the saved string across the aliased write (6 inputs)")


if __name__ == "__main__":
    main()
