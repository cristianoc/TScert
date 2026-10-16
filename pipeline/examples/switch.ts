// `switch` as a breakable block: the discriminant once, a chain of `===`
// tests over groups of labels sharing a body, `default` last wherever it is
// written, and `break` leaving the block.
function classify(k: number): number {
  switch (k) {
    case 1:
      return 100;
    case 2:
    case 3:
      return 200;
    default:
      return 300;
  }
}

function dayKind(day: number): boolean {
  let weekend: boolean = false;
  switch (day) {
    case 0:
    case 6:
      weekend = true;
      break;
    default:
      weekend = false;
  }
  return weekend;
}

function defaultFirst(x: number): number {
  switch (x) {
    default:
      return 0;
    case 1:
      return 1;
  }
}

function midBreak(x: number, c: boolean): number {
  let y: number = 0;
  switch (x) {
    case 1:
      if (c) {
        break;
      }
      y = 2;
      break;
    case 2:
      y = 3;
  }
  return y;
}

function inLoop(x: number, c: boolean): number {
  let y: number = 0;
  while (c) {
    switch (x) {
      case 1:
        y = 1;
        continue;
      case 2:
        break;
    }
    y = 2;
    break;
  }
  return y;
}

// A discriminant other than a name is evaluated once, before the tests.
function computed(x: number): number {
  switch (x * 2) {
    case 2:
      return 1;
    case 4:
      return 2;
  }
  return 0;
}

function empty(x: number): number {
  switch (x) {
  }
  return x;
}
