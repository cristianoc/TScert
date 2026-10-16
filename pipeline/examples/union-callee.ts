// A call of a union of callables is a call of whichever the value is: each
// arm takes the actuals, and the call's value is the union of their results.
type Render = ((x: number) => string) | ((y: number) => boolean);
function show(n: number): string {
  return "" + n;
}
function renderEither(f: Render): string | boolean {
  return f(1);
}
function renderShow(): string | boolean {
  const f: Render = show;
  return f(2);
}
// Overloads stating one parameter alike: the actual is built at it, and the
// first overload it matches is the call's.
type Animal = { name: string };
type Dog = { name: string; breed: string };
type Adopt = ((a: Animal) => Dog) & ((a: Animal) => Animal);
function adoptDog(_a: Animal): Dog {
  return { name: "Fido", breed: "Lab" };
}
function adopted(): Dog {
  const adopt: Adopt = adoptDog;
  return adopt({ name: "Rex" });
}
// A binder's value is called at its bound.
function callBound<F extends (x: number) => string>(f: F, n: number): string {
  return f(n);
}
// A method of a union of objects: each alternative's member, bound to the
// value and called, dispatched on the value.
class Left {
  l: number = 1;
  size(): number {
    return this.l;
  }
}
class Right {
  r: number = 2;
  size(): number {
    return this.r;
  }
}
function classSize(s: Left | Right): number {
  return s.size();
}
interface Circle {
  kind: "circle";
  area(): number;
}
interface Square {
  kind: "square";
  area(): number;
}
function shapeArea(sh: Circle | Square): number {
  return sh.area();
}
