// A closure written above a `const` it updates: the constant is an early
// binding, and its update throws a TypeError in JavaScript (run under
// Node), a throw the model does not state, so the write is refused.
export function test(): number {
  // @ts-expect-error: TypeScript refuses the update of a constant.
  const bump = (): number => ++x;
  const x: number = 0;
  return bump();
}
