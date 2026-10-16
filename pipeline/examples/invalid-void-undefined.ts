export function forgetResult(value: () => void): undefined {
  return value();
}
