// A method result is covariant, never widened into a narrower result.
interface WideGetter {
  get(): number | string;
}
interface Getter {
  get(): number;
}
export function narrow(x: WideGetter): Getter {
  return x;
}
