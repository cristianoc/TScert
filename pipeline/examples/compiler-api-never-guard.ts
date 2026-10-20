import * as ts from "typescript/unstable/ast";

// A guard's refinement of a member path read after a call of a function
// declared to return `never` on the guard's other edge, alone, in a
// disjunction and in a callback, as `protocolPattern` reads an array
// pattern's elements.
function fail(message: string): never {
  throw new Error(message);
}

export function direct(el: ts.BindingElement): string {
  if (!el.name) return "";
  if (!ts.isIdentifier(el.name)) fail("nested");
  return el.name.text;
}

export function disjunction(el: ts.BindingElement): string {
  if (!el.name) return "";
  if (
    el.initializer ||
    !el.name ||
    !ts.isIdentifier(el.name) ||
    el.dotDotDotToken
  )
    fail("nested");
  return el.name.text;
}

export function callback(pattern: ts.ArrayBindingPattern): string[] {
  const named: string[] = [];
  pattern.elements.forEach((el) => {
    if (!ts.isBindingElement(el) || !el.name) return;
    if (
      el.initializer ||
      !el.name ||
      !ts.isIdentifier(el.name) ||
      el.dotDotDotToken
    )
      fail("nested");
    named.push(el.name.text);
  });
  return named;
}
