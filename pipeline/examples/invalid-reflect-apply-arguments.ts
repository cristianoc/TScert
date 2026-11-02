// Reflect's broad overload permits the call; Node returns 7 at string.
export function wrong(): string {
  const identity = (x: string): string => x;
  return Reflect.apply(identity, undefined, [7]);
}
