// A closure writing `stack` of a captured parameter: its body is lowered
// apart, through the same write emission (run under Node), refused at the
// write.
export function traced(o: { stack: string }): string[] {
  const set = (v: string): void => {
    o.stack = v;
  };
  set("s");
  return Object.keys(o);
}
