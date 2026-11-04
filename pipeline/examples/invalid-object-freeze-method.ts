// A method of a frozen literal writing its receiver's field: TypeScript
// types `this` as the literal's writable type, and the write throws (run
// under Node: TypeError, "Cannot assign to read only property"). Only
// named fields are admitted.
export function f(): number {
  const o = Object.freeze({
    x: 0,
    bump(): void {
      this.x = this.x + 1;
    },
  });
  o.bump();
  return o.x;
}
