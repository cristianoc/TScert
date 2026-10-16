// Each case of a switch is a `===` test of the discriminant, so a clause sees
// the discriminant narrowed to its labels, `default` sees the rest, and a
// switch whose cases cover the discriminant's type never falls off its end.
function caseNarrows(x: 1 | 2): number {
  switch (x) {
    case 1: {
      const one: 1 = x;
      return one;
    }
    case 2: {
      const two: 2 = x;
      return two;
    }
  }
}

function defaultIsTheRest(x: "a" | "b" | "c"): string {
  switch (x) {
    case "a":
      return "first";
    default: {
      const rest: "b" | "c" = x;
      return rest;
    }
  }
}

function bothBooleans(b: boolean): number {
  switch (b) {
    case true:
      return 1;
    case false:
      return 0;
  }
}

function joinsTheClauses(x: 1 | 2, b: "b", c: "c"): "b" | "c" {
  let y: "a" | "b" | "c" = "a";
  switch (x) {
    case 1:
      y = b;
      break;
    case 2:
      y = c;
      break;
  }
  return y;
}
