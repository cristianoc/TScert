// Reflect's broad overload permits the call; Node returns 7 at string.
export function wrong(): string {
  const read = function (this: { value: string }): string {
    return this.value;
  };
  return Reflect.apply(read, { value: 7 }, []);
}
