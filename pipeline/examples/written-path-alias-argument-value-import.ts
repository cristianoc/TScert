// A computed alias applied to an owner of synthesised members.
export function f(
  x: keyof {
    z: import("@fixture/whole").Keys<typeof import("@fixture/whole").keyed>;
  },
): "z" {
  return x;
}
