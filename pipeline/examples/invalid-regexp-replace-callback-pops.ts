// A `replace` callback popping the array the caller's loop reads: the
// callback changes a store, so the call states no footprint, and the read
// below the loop's bound after it is refused. Run under Node, it reads
// `undefined`.

export function popping(font: string, texts: string[]): string {
  return font.replace(/x/g, (item: string) => {
    texts.pop();
    return item;
  });
}

export function lastRead(texts: string[]): string {
  let read = "";
  for (let i = 0; i < texts.length; i++) {
    popping("x", texts);
    read = texts[i]!;
  }
  return read;
}
