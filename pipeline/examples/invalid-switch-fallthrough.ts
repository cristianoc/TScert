// Case 1 falls through into case 2, where `y` may still be null.
function fallThrough(x: number): number {
  let y: number | null = null;
  switch (x) {
    case 1:
      y = null;
    case 2:
      if (y === null) {
        return 0;
      }
      y = 2;
    case 3:
      const z: number = y;
      return z;
  }
  return 1;
}
