// A class has no plain call: it is not a function type, and calling it
// without `new` throws.
class Flag {
  on: boolean;
  constructor(on: boolean) {
    this.on = on;
  }
}
function run(f: (on: boolean) => Flag): Flag {
  return f(true);
}
export function go(): Flag {
  return run(Flag);
}
