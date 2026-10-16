// A constant declared at a named union holds, from its initialization, the
// arms its object literal may be of, as TypeScript narrows a declared union
// on assignment: `none` is only `{ kind: "none" }`, so it meets a
// parameter whose other arm is wider. A record at a discriminated union
// infers the binder of the arm it selects: `some` gives `T := number`.
type Option<T> = { kind: "some"; value: T } | { kind: "none" };

function isNone<T>(option: Option<T>): boolean {
  return option.kind === "none";
}

function valueOr<T>(option: Option<T>, fallback: T): T {
  if (option.kind === "some") {
    return option.value;
  }
  return fallback;
}

export function use(): number {
  const none: Option<number> = { kind: "none" };
  const some: Option<number> = { kind: "some", value: 1 };
  const absent: boolean = isNone(none);
  return absent ? valueOr(some, 0) : 0;
}
