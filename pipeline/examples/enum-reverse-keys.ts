// A numeric enum's object holds, at each value's key, the name of a member
// with that value (TypeScript's emit adds the reverse mapping): for a closed
// enum the last member's, and for one with a member known only at run time,
// at each value TypeScript computes, a member's name, whichever member wrote
// it last, so a string. A read at a key of the enum's values is a string.
enum Closed {
  A = 1,
  B = 2,
  C = 4,
}
function three(): number {
  return 3;
}
function one(): number {
  return 1;
}
enum Open {
  A = 1,
  B = three(),
  C = 7,
  D = 7,
  // At run time 1: its name replaces `A`'s at the key "1".
  E = one(),
}
function closedName(k: Closed): string {
  return Closed[k];
}
function openName(k: Open.A | Open.C): string {
  return Open[k];
}
function openLiteral(): string {
  return Open[7];
}
function openObject(): typeof Open {
  return Open;
}
function objectName(o: typeof Open): string {
  return o[1];
}
function suffixed(k: Closed.A | Closed.C): boolean {
  return Closed[k].endsWith("A");
}
