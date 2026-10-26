// A module writing its own class's binding, which TypeScript rejects
// (TS2629): `instanceof` of the import would test whichever class the
// binding holds then (`invalid-instanceof-rebound-value-import`, run under
// Node).
export class Rebound {
  readonly v: number = 1;
}

export function swap(): void {
  Rebound = class {
    readonly v: number = 2;
  };
}
