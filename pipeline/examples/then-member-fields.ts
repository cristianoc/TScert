// An object the program makes may own a `then` member, an ordinary field or
// method: a statement's branches (`then: Stmt[]`), a conditional's arm
// (`then: Expr`), a class's method, each read or called directly. No such
// object meets `Promise<T>`, whose prototype holds `Symbol.toStringTag`, and
// one with a callable `then` stays refused where a value is resolved.
type Expr =
  | { k: "num"; value: number }
  | { k: "cond"; test: Expr; then: Expr; else: Expr };
type Stmt =
  | { k: "expr"; e: Expr }
  | { k: "if"; test: Expr; then: Stmt[]; else: Stmt[] };

export function branch(test: Expr, body: Stmt[]): Stmt {
  return { k: "if", test, then: body, else: [] };
}

export function arm(test: Expr, yes: Expr, no: Expr): Expr {
  return { k: "cond", test, then: yes, else: no };
}

export function thenCount(s: Stmt): number {
  return s.k === "if" ? s.then.length : 0;
}

export function value(e: Expr): number {
  return e.k === "num" ? e.value : value(e.then);
}

class Step {
  then(n: number): number {
    return n + 1;
  }
}

export function stepped(n: number): number {
  return new Step().then(n);
}

export function callback(n: number): number {
  const handlers = { then: (x: number) => x * 2 };
  return handlers.then(n);
}
