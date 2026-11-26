export function simple(): A.NumberType {
  return 1;
}

export function nested(): A.Inner.T {
  return 2;
}

export function other(): B.Inner.T {
  return "a string";
}

export function defaulted(): A.Inner.Box {
  return { value: 3, label: "another string" };
}
