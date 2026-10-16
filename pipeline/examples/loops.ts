function loopInvariant(flag: boolean): boolean {
  let value: boolean = false;
  while (flag) {
    value = true;
    break;
  }
  return value;
}
function loopBackEdge(flag: boolean, skip: boolean): boolean {
  while (flag) {
    if (skip) {
      continue;
    }
    break;
  }
  return flag;
}
