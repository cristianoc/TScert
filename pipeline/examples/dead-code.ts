// Statements after one that always jumps are never reached: they are dropped
// unread, here a declaration no live statement names and a second return.
function afterReturn(x: number): number {
  return x;
  const y = x + 1;
  return y;
}

function afterBranches(flag: boolean): boolean {
  if (flag) {
    return true;
  } else {
    return false;
  }
  flag = !flag;
}

function afterBreak(flag: boolean): boolean {
  while (flag) {
    break;
    flag = false;
  }
  return flag;
}

const inClosure = (x: number): number => {
  return x;
  x + 1;
};
