// Parameters with no annotation whose defaults are parenthesized literals:
// parentheses are transparent, so each default states the literal's type
// widened, as TypeScript's `isolatedDeclarations` declares it, exactly as
// written without them (`literal-default-parameters`).
export function flags(
  // prettier-ignore
  singleLine = (false),
  // prettier-ignore
  strict = (true),
): boolean {
  return singleLine && strict;
}

export function numbers(
  // prettier-ignore
  n = (3),
  // prettier-ignore
  negative = (-1),
): number {
  return n + negative;
}

export function strings(
  // prettier-ignore
  s = ("a"),
  // prettier-ignore
  t = (`b`),
): string {
  return s + t;
}

export function calls(): boolean {
  return (
    flags() &&
    numbers() === 2 &&
    strings() === "ab" &&
    flags(true, false) === false
  );
}
