type Box = { k: "union" | "intersection" };

export function negatedStale(b: Box, f: () => void): "union" {
  if (!(b.k === "union" && (f(), true))) return "union";
  return b.k;
}
