// A class whose method states the empty footprint and pops the array it is
// handed, and which no code calls: the method's code is checked at its
// statement, and the class's construction checks the prototype's method
// against the instance type's member, which states it too (a control drops
// the first check and shows the second).
export class Bump {
  bump(xs: number[], x: number): Modifies<{}, number> {
    xs.pop();
    return x;
  }
}
