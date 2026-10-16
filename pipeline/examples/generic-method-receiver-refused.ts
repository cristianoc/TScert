// A generic method declaring `this: T`: its member is a scheme the member
// bound to its host meets at every receiver, which states no type the host
// must meet. Refused where the class is read.
class Ctx {
  value: number = 1;
}
class Holder {
  m<U>(this: Ctx, u: U): U {
    return u;
  }
}
export function call(h: Holder & Ctx): number {
  return h.m(1);
}
