// A static block's statements are checked as any closure body's: here a
// call passing a number where a string is expected.
declare function register(name: string, size: number): void;

class Registry {
  static readonly size: number = 3;
  static {
    // @ts-expect-error a number is not a string
    register(Registry.size, Registry.size);
  }
}

export function make(): Registry {
  return new Registry();
}
