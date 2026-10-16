// A write at a key a dictionary may lack adds it; the caller holds the
// dictionary and would see its keys change, so the write is refused.
export function add(d: { [k: string]: number }): void {
  d["fresh"] = 1;
}
