// Distributed, each arm holds `extra` at `boolean`: the read is no `true`.
export function extra(
  x: (number[] | { name: string }) & { extra: boolean },
): true {
  return x.extra;
}
