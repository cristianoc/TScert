// `x instanceof Point` does not narrow `unknown` to `Point`: an object gets
// Point's prototype without Point's constructor running
// (`Object.create(Point.prototype)`, `Object.setPrototypeOf`,
// `Reflect.construct` with Point as the new target), so the prototype on its
// chain is no evidence of Point's fields, and the model assumes it of no
// value a unit receives.
class Point {
  x: number = 0;
}
export function px(p: unknown): number {
  if (p instanceof Point) {
    return p.x;
  }
  return 0;
}
