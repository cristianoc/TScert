// The standard library's `Function`: a value with call or construct code, of
// which no signature is known. Functions and classes meet it.
class Point {
  x: number = 0;
}

function fromArrow(f: (n: number) => string): Function {
  return f;
}

function fromClass(): Function {
  return Point;
}

function fromConstructor(c: new () => Point): Function {
  return c;
}

function keep(f: Function): Function {
  return f;
}

function both(): Function[] {
  return [keep(fromClass()), fromArrow((n: number): string => "")];
}
