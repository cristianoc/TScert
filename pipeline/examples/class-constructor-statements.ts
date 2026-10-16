// A constructor runs statements that do not read `this` before its instance
// is allocated: the values evaluated before each (field initializers,
// parameter properties, earlier assignments) are bound first, in source
// order. A last `if` that assigns fields ends each arm with its own
// allocation.
function seed(): number {
  return 4;
}
function log(): void {}
class Sized {
  base: number = seed();
  size: number;
  label: string;
  constructor(
    public tag: string,
    size?: number,
  ) {
    log();
    const fallback = 0;
    if (size === undefined) {
      this.size = fallback;
      this.label = "none";
    } else {
      log();
      this.size = size;
      this.label = "some";
    }
  }
}
class Effect {
  constructor(run: () => void) {
    run();
  }
}
export function make(): number {
  const sized = new Sized("t", 2);
  const effect = new Effect(log);
  return sized.base + sized.size + new Sized("u").size;
}
