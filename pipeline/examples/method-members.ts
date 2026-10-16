// Methods are host-relative members: a class instance meets an interface it
// structurally matches, and a method result widens covariantly.
interface Getter {
  get(): number;
}
interface WideGetter {
  get(): number | string;
}
class Impl {
  get(): number {
    return 1;
  }
}
class Wide {
  get(): number | string {
    return "one";
  }
}
export function asInterface(x: Impl): Getter {
  return x;
}
export function widenInterface(x: Getter): WideGetter {
  return x;
}
export function widenClass(x: Impl): Wide {
  return x;
}
export function call(x: Getter): number {
  return x.get();
}
