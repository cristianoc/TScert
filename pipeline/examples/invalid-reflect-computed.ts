// A function of `Reflect` read by a computed key: refused at the read.
export function computed(record: { a: number }): (string | symbol)[] {
  return Reflect["ownKeys"](record);
}
