// An unsupported generic method must never become an unknown-valued field.
interface Witness {
  choose<T, U extends T>(x: U): U;
}
export function wrong(): Witness {
  return { choose: 42 };
}
