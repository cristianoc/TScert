// `+42` is 42, not 43.
export function bad(): 43 {
  return +42;
}
