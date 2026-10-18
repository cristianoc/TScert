// A module-level `let` the module does not export is a module cell: the
// initialization unit allocates it at its entry, holding the uninitialized
// marker, and every unit reads and writes it through a checked access at
// its one contract (SOURCE-MODEL.md, "Module cells").
let count: number = 0;
let cache: string | null = null;

export function bump(): number {
  count = count + 1;
  return count;
}

export function cached(): string {
  if (cache === null) cache = "computed";
  return cache;
}

// A closure the initialization creates before the declaration it reads.
const later = (): number => limit;
let limit: number = 3;

export function limited(): number {
  return later() + limit;
}
