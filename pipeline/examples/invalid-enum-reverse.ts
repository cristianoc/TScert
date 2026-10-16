// The reverse mapping holds the last member with a value: Same[0] is "B".
enum Same {
  A = 0,
  B = 0,
}
function first(): "A" {
  // @ts-expect-error TypeScript reads Same[0] as string
  return Same[0];
}
