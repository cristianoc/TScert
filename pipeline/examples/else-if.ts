// `else if` and unbraced arms: each arm is the one statement a block would
// hold, in functions, closures and a constructor's last `if`.
function sign(n: 0 | 1 | 2): boolean {
  if (n === 0) return false;
  else if (n === 1) return true;
  else return false;
}

function pick(a: boolean, b: boolean): number {
  if (a) {
    return 1;
  } else if (b) {
    return 2;
  }
  return 3;
}

function classify(a: boolean, b: boolean): number {
  let r: number = 0;
  if (a) r = 1;
  else if (b) r = 2;
  else r = 3;
  return r;
}

function narrowed(x: number | null, y: boolean): number {
  if (y) return 1;
  else if (x === null) return 2;
  else return x;
}

const choose = (a: boolean, b: boolean): number => {
  if (a) return 1;
  else if (b) return 2;
  else return 3;
};

class Level {
  level: number;
  constructor(a: boolean, b: boolean) {
    if (a) this.level = 1;
    else if (b) this.level = 2;
    else this.level = 3;
  }
}

function level(a: boolean, b: boolean): number {
  return new Level(a, b).level + choose(a, b);
}
