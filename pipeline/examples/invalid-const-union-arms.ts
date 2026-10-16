// Past the first test the constant is not a profile: its `kind` may be any
// other arm's.
type U =
  | { kind: "profile"; name: string }
  | { kind: "settings"; theme: string };
type M = { kind: "user"; u: U } | { kind: "text"; content: string };

export function kindOf(m: M): "settings" {
  if (m.kind === "user") {
    const u = m.u;
    if (u.kind === "profile") {
      return "settings";
    }
    return u.kind;
  }
  return "settings";
}
export function wrong(m: M): "profile" {
  if (m.kind === "user") {
    const u = m.u;
    if (u.kind === "profile") {
      return "profile";
    }
    return u.kind;
  }
  return "profile";
}
