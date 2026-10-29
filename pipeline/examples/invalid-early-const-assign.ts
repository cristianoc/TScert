// A closure written above a `const` it assigns: the constant is an early
// binding, and the assignment throws a TypeError in JavaScript (run under
// Node), a throw the model does not state, so the write is refused.
export function test(): number {
  const set = (): number => {
    // @ts-expect-error: TypeScript refuses the assignment of a constant.
    x = 1;
    return x;
  };
  const x: number = 0;
  return set();
}
