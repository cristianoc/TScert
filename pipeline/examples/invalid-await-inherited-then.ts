// `await` of an instance whose `then` it inherits from its base class: the
// lookup finds it on the prototype chain and JavaScript calls it (run under
// Node: the await settles to 42), so the await is refused.
class Base {
  then(resolve: (value: number) => void): void {
    resolve(42);
  }
}
class Derived extends Base {}

export async function inherited(): Promise<unknown> {
  return await new Derived();
}
