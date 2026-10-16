// An increment's value is any number, not the target's literal type.
function step(): number {
  let x: 0 | 1 = 0;
  x++;
  return x;
}
