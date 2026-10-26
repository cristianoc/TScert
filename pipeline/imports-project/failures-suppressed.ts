// A module writing its class's binding where a comment suppresses
// TypeScript's error (`invalid-instanceof-suppressed-value-import`, run
// under Node).
export class Suppressed {
  readonly v: number = 1;
}

export function swap(): void {
  // @ts-expect-error TS2629: the class's binding is written
  Suppressed = class {
    readonly v: number = 2;
  };
}
