// A factory returning a closure that pops the array it captured: the
// closure's footprint changes a store, so the factory's claim states none
// for it, and a call of the closure drops the loop's bound. The read at `i`
// after the call is refused. Run under Node, it reads `undefined`.

export function popper(xs: string[]): () => number {
  return () => {
    xs.pop();
    return xs.length;
  };
}

export function lastRead(texts: string[]): string {
  const pop = popper(texts);
  let read = "";
  for (let i = 0; i < texts.length; i++) {
    pop();
    read = texts[i]!;
  }
  return read;
}
