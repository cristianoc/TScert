// A compound assignment of `stack`: the same reserved write (run under
// Node), refused at the write.
export function traced(o: { stack: string }): string[] {
  o.stack += "s";
  return Object.keys(o);
}
