def greet(name: str) -> str:
    return "hello " + name


def inc(x: int) -> int:
    return x + 1


def sign(x: int) -> int:
    if x < 0:
        return -1
    elif x == 0:
        return 0
    else:
        return 1


def nonempty(s: str) -> bool:
    return not (s == "")


def pick(flag: bool, a: str, b: str) -> str:
    return a if flag else b
