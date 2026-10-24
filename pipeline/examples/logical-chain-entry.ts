// A chain whose middle operand is a test, read right-nested: the first
// operand's read is typed where the chain starts, before any operand
// answered, in a conditional and in a statement, for `&&` and `||`, and
// after a comma's effect.
interface B {
  readonly kind: number;
  readonly dot: string | undefined;
}

export function inConditional(rest: B | undefined): B | null {
  return rest && rest.kind === 1 && rest.dot ? rest : null;
}

export function inStatement(rest: B | undefined): string {
  if (rest && rest.kind === 1 && rest.dot) return rest.dot;
  return "";
}

export function orChain(rest: B | undefined, other: B): B {
  return rest || other.kind === 1 || other.dot ? other : other;
}

export function afterComma(rest: B | undefined): number {
  let seen = 0;
  return ((seen = seen + 1), rest) && rest.kind === 1 && rest.dot ? seen : 0;
}
