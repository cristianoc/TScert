// A constant whose function literal reads the constant: the body reads the
// closure's self entry, the invoked object (SOURCE-MODEL.md, "Recursive
// constants"). Local and module-level, an arrow and a function expression, a
// nested closure capturing the self entry, a default reading it, a body
// writing a captured array, an annotated constant, a bound wrapper.
export function depth(n: number): number {
  const visit = (k: number): number => (k <= 0 ? 0 : 1 + visit(k - 1));
  return visit(n);
}
export function nested(n: number): number {
  const visit = (k: number): number => {
    const again = (j: number): number => visit(j);
    return k <= 0 ? 0 : 1 + again(k - 1);
  };
  return visit(n);
}
export function expression(n: number): number {
  const visit = function (k: number): number {
    return k <= 0 ? 0 : 1 + visit(k - 1);
  };
  return visit(n);
}
export function defaulted(n: number): number {
  const visit = (k: number, d: number = k > 100 ? visit(0) : 0): number =>
    k <= 0 ? d : visit(k - 1);
  return visit(n);
}
export function writes(n: number): number[] {
  const out: number[] = [];
  const visit = (k: number): void => {
    out.push(k);
    if (k > 0) visit(k - 1);
  };
  visit(n);
  return out;
}
export function annotated(n: number): number {
  const visit: (k: number) => number = (k) => (k <= 0 ? 0 : 1 + visit(k - 1));
  return visit(n);
}
export function bound(n: number): number {
  const visit = (k: number): number => (k <= 0 ? 0 : 1 + visit(k - 1));
  const b = visit.bind(null, n);
  return b();
}
const fact = (n: number): number => (n <= 1 ? 1 : n * fact(n - 1));
export function main(): number {
  return (
    fact(5) +
    depth(3) +
    nested(3) +
    expression(3) +
    defaulted(3) +
    writes(3).length +
    annotated(3) +
    bound(3)
  );
}
