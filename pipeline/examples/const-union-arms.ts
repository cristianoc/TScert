// An unannotated constant of a named union is held at its arms, as an
// annotated one and a parameter are: tag tests keep and drop each arm,
// test after test.
type U =
  | { kind: "profile"; name: string }
  | { kind: "settings"; theme: string }
  | { kind: "activity"; count: number };
type M = { kind: "user"; u: U; id: string } | { kind: "text"; content: string };

export function describe(m: M): string {
  if (m.kind === "user") {
    const u = m.u;
    if (u.kind === "profile") {
      return u.name;
    } else if (u.kind === "settings") {
      return u.theme;
    }
    return "activity";
  }
  return m.content;
}
