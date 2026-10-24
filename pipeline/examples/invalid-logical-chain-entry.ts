// Where `rest && rest.kind === 1 && rest.dot` fails, `rest` may still be
// `undefined`: its first operand answered alone.
interface B {
  readonly kind: number;
  readonly dot: string | undefined;
}

export function falsyArm(rest: B | undefined): B {
  if (rest && rest.kind === 1 && rest.dot) return rest;
  return rest;
}
