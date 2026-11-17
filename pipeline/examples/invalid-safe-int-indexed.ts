// An indexed access reading `SafeInt`: TypeScript computes it at `number`,
// which would erase the safe integers from the result contract (`0.5`
// would pass), so the form is refused at the source boundary.
export function bad(): { value: SafeInt }["value"] {
  return 0.5;
}
