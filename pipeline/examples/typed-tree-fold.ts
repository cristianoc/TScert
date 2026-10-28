// A fold over a tree read through one typed children function: each node's
// kind decides its parts by an exhaustive switch, so every member read is
// of a known record (the pattern of `namesRead`, `fragment-parts.mts`).
type Expr =
  | { k: "id"; name: string }
  | { k: "lit"; value: number }
  | { k: "not"; e: Expr }
  | { k: "bin"; l: Expr; r: Expr }
  | { k: "call"; callee: Expr; args: Expr[] };

function parts(e: Expr): Expr[] {
  switch (e.k) {
    case "id":
    case "lit":
      return [];
    case "not":
      return [e.e];
    case "bin":
      return [e.l, e.r];
    case "call":
      return [e.callee, ...e.args];
  }
}

function namesRead(e: Expr): string[] {
  const own: string[] = e.k === "id" ? [e.name] : [];
  return [...own, ...parts(e).flatMap(namesRead)];
}
