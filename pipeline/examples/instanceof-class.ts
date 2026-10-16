// `x instanceof C` of a class the file declares: C's prototype object owns a
// key no other object does, and the test looks for it along x's prototype
// chain. A derived class's prototype links to its base's, so a derived
// instance is an instance of its base; an unrelated class's is not, nor a
// primitive. A passed test drops the primitive arms of a union.
class Shape {
  name: string;
  constructor(name: string) {
    this.name = name;
  }
  describe(): string {
    return "shape " + this.name;
  }
}
class Circle extends Shape {
  r: number;
  constructor(r: number) {
    super("circle");
    this.r = r;
  }
}
class Unrelated {
  name: string = "other";
}
class Box<T> {
  v: T;
  constructor(v: T) {
    this.v = v;
  }
}
export function isShape(x: unknown): boolean {
  return x instanceof Shape;
}
export function radius(x: Circle | string | number): number {
  if (x instanceof Circle) {
    return x.r;
  }
  return 0;
}
export function boxed(x: Box<number> | string): number {
  if (!(x instanceof Box)) {
    return 0;
  }
  return x.v;
}
export function tests(): boolean {
  const c = new Circle(2);
  const s = new Shape("s");
  const u = new Unrelated();
  return (
    c instanceof Shape &&
    c instanceof Circle &&
    !(s instanceof Circle) &&
    !(u instanceof Shape) &&
    !isShape(1) &&
    isShape(c)
  );
}
export function total(): number {
  const c = new Circle(2);
  return radius(c) + boxed(new Box<number>(3)) + c.describe().length;
}
const atStart: boolean = new Circle(1) instanceof Shape;
