// `compile` replaces a regex's pattern, and with it the shape its type states:
// `/(a)(b)/` compiled to "c" has no group. It is not in the model's regex.
export function recompiled(): RegExp {
  const re = /(a)(b)/;
  return re.compile("c");
}
