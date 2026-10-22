// A global the file only declares may be an accessor of the global object,
// which answers each read anew: the chain's test says nothing of a later
// read of it.
type Node = { k: "d"; t: number } | { k: "e"; u: string };
declare const current: Node | undefined;

export function wrong(): number {
  return current?.k === "d" ? current.t : 0;
}
