// Past the test, the parameter is `false`, whatever the constant of its name.
const b: number = 1;
export function bad(b: boolean): true {
  if (b) {
    throw new Error("maybe");
  }
  return b;
}
