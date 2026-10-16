// A readonly optional field is a view that may be absent: it reads at its type
// or undefined. A field, a view, an optional field or another readonly
// optional field of the same key covers it when its type is within; it covers
// a readonly optional field of a wider type.
interface Config {
  readonly limit?: number;
  readonly name: string;
}
function limitOf(config: Config): number | undefined {
  return config.limit;
}
export function passed(config: Config): number | undefined {
  return limitOf(config);
}
export function fromField(value: {
  limit: number;
  name: string;
}): number | undefined {
  return limitOf(value);
}
export function fromView(value: {
  readonly limit: 1 | 2;
  readonly name: string;
}): number | undefined {
  return limitOf(value);
}
export function fromOptional(value: {
  limit?: number;
  name: string;
}): number | undefined {
  return limitOf(value);
}
export function fromNarrower(value: {
  readonly limit?: 1 | 2;
  name: string;
}): number | undefined {
  return limitOf(value);
}
export function widened(config: Config): { readonly limit?: number | string } {
  return config;
}
class Fixed implements Config {
  readonly name: string = "fixed";
  limit: number = 3;
}
export function fromClass(): number | undefined {
  return limitOf(new Fixed());
}
