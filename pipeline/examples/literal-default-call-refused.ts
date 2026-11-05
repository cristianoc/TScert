// A parameter with no annotation whose default is not a literal: it states
// no type (TypeScript's `isolatedDeclarations` refuses it too, TS9011), so
// the unit's boundary is not written.
function zero(): number {
  return 0;
}

export function start(offset = zero()): number {
  return offset;
}
