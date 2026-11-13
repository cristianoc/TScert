// A module whose function reads two module cells, each filled at its first
// use: its unit assumes the two cells are two locations, as the
// initialization allocates each fresh (`moduleCellSeparation`).
let runs: Uint8Array | null = null;
let remaps: Uint8Array | null = null;

export function classCount(): number {
  const r = (runs ??= new Uint8Array(4));
  remaps ??= new Uint8Array(2);
  return r.length + remaps.length;
}
