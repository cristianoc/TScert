// A type guard stating the empty footprint at its promise's type while it
// pushes onto the array it is handed: its own unit is refused at its
// statement.
export interface Circle {
  kind: "circle";
  radius: number;
}
export interface Square {
  kind: "square";
  side: number;
}

export function isLogged(
  s: Circle | Square,
  log: string[],
): s is Within<{ value: "keep"; store: "keep" }, Circle> {
  log.push(s.kind);
  return s.kind === "circle";
}
