// `default` runs only when every label failed: it never sees a label's value.
function defaultIsNotALabel(x: 1 | 2 | 3): number {
  switch (x) {
    case 1:
      return 1;
    default: {
      const one: 1 = x;
      return one;
    }
  }
}
