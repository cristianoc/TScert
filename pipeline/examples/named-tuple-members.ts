// A tuple member's name is a label with no runtime meaning: each named form
// reads as its unnamed one, keeping its optionality and rest.
type Span = [start: number, end: number];
export function width(span: Span): number {
  return span[1] - span[0];
}
export function make(start: number, end: number): Span {
  return [start, end];
}
export function plain(span: Span): [number, number] {
  return span;
}
type Point = readonly [x: number, y: number];
export function point(p: Point): readonly number[] {
  return p;
}
type Labelled = [name: string, weight?: number];
export function label(name: string): Labelled {
  return [name];
}
export function unnamed(l: Labelled): [string, number?] {
  return l;
}
type Row = [id: number, ...cells: string[]];
export function id(row: Row): number {
  return row[0];
}
export function row(): Row {
  return [1, "a", "b"];
}
export function rowView(r: Row): readonly [number, ...string[]] {
  return r;
}
export function call(...args: [count: number, name: string]): string {
  return args[1];
}
