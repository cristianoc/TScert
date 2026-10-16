// A type and a function of one name: the type in a type position, the
// function in a value position.
type Pair = { first: number; second: number };
function Pair(first: number, second: number): Pair {
  return { first, second };
}
interface Named {
  name: string;
}
function Named(name: string): Named {
  return { name };
}
function sum(): number {
  const p: Pair = Pair(1, 2);
  const n: Named = Named("n");
  return p.first + p.second + n.name.length;
}
