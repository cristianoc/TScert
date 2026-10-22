// A call between the test and the read writes the tested name: what the
// test established of it no longer holds.
type Node = { k: "d"; t: number } | { k: "e"; u: string };

export function wrong(start: Node | undefined, reset: Node | undefined): Node {
  let b = start;
  const clear = (): void => {
    b = reset;
  };
  if (b?.k === "d") {
    clear();
    return b;
  }
  return { k: "e", u: "" };
}
