// A key is a string, even over an object whose keys TypeScript names: an
// object may carry more keys than its type states.
function narrow(o: { a: number }): "a" {
  for (const k in o) {
    const key: "a" = k;
    return key;
  }
  return "a";
}
