// Where `!(a || b)` fails, one of the tests held: the field is what they
// test, not what their failure leaves.
type Name = { name: "a" | "b" | "c" | "d" };

export function wrong(k: Name): "c" | "d" {
  if (!(k.name === "a" || k.name === "b")) return "c";
  // @ts-expect-error k.name is "a" | "b" here
  return k.name;
}
