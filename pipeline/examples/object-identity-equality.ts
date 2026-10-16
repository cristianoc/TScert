// Objects compare by identity, with or without fields: functions, records of
// optional fields only, and a function against a record.
function sameFunction(left: () => number, right: () => number): boolean {
  return left === right;
}

function differentFunction(left: () => number, right: () => number): boolean {
  return left !== right;
}

function looseFunction(left: () => void, right: () => void): boolean {
  return left == right;
}

function looseDifferentFunction(left: () => void, right: () => void): boolean {
  return left != right;
}

function sameOptionalRecord(
  left: { value?: number },
  right: { value?: number },
): boolean {
  return left === right;
}

function functionOrRecord(
  left: (() => void) | { value?: number },
  right: () => void,
): boolean {
  return left == right;
}
