// `1e309` is the infinity, not the largest finite literal below it.
export function bad(): 1e308 {
  return 1e309;
}
