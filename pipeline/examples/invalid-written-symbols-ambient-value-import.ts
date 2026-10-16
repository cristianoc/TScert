// An ambient namespace's members are exported: swept, `B<any>` refused.
export function f(
  x: keyof { z: typeof import("@fixture/whole").Ambient },
): "z" {
  return x;
}
