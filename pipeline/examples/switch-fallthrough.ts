// A clause that completes runs on into the next clause's statements: case 1
// adds both, and `y` is a number after either.
function fallThrough(x: number): number {
  let y: number = 0;
  switch (x) {
    case 1:
      y = 1;
    case 2:
      y = y + 2;
      break;
    default:
      y = 5;
  }
  return y;
}

// Empty clauses fall through too: 0 and 6 share a body, and `default`, first
// in the source, is taken only after every label failed.
function weekend(day: number): boolean {
  switch (day) {
    default:
      return false;
    case 0:
    case 6:
      return true;
  }
}
