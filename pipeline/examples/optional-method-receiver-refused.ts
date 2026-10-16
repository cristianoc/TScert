// An optional method declaring `this: T`: an optional method is an optional
// field, whose function takes its declaration as receiver. Refused where the
// interface is read.
interface Ctx {
  value: number;
}
interface Optional {
  m?(this: Ctx, x: number): number;
}
export function call(o: Ctx & Optional): number {
  return o.m ? o.m(1) : 0;
}
