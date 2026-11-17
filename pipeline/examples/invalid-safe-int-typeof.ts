// `typeof` of a binding declared `SafeInt`: TypeScript computes it at
// `number`, which would erase the safe integers from the result contract,
// so the form is refused at the source boundary.
const k: SafeInt = 1;

export function bad(): typeof k {
  return 0.5;
}
