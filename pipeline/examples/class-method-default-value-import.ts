// An imported class's method may be called without its defaulted parameter,
// and a field at the type of a function declared elsewhere is read with the
// library types that function's parameters name.
import { Counts, Scaler, Seen } from "@fixture/lib";

export function scaled(s: Scaler): number {
  return s.scale(1) + s.scale(1, 2);
}

export function seen(s: Seen): number {
  return s.n;
}

export function counted(c: Counts): number {
  return c.counts.size;
}
