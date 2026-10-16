// A `switch` in a closure: labeled blocks and `break`s, as in a function body.
export function namer(): (k: number) => string {
  return (k: number): string => {
    let name: string = "other";
    switch (k) {
      case 0:
        name = "zero";
        break;
      case 1:
        name = "one";
        break;
    }
    return name;
  };
}
