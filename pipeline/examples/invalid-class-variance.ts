// TypeScript accepts viewing a Box as Loose through method-parameter
// bivariance; Box.set does not accept null, so the view is refused.
class Box {
  value: boolean = true;
  set(v: boolean): null {
    this.value = v;
    return null;
  }
}
interface Loose {
  set(v: boolean | null): null;
}
export function misuse(b: Box): null {
  const l: Loose = b;
  return l.set(null);
}
