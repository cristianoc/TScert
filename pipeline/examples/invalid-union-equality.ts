// Two operands of several singletons that differ may still each be any of
// theirs: `!==` narrows neither.
function unequal(x: "a" | "b", y: "b" | "c"): "a" {
  if (x !== y) {
    const a: "a" = x;
    return a;
  }
  return "a";
}
