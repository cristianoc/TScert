// An indexed access at an optional method of a type alias's record or of an
// interface: the method's function, received by the declaration, or
// undefined. The other members keep their reading, beside a generic method
// as well. The function is called once a Table holds it as its member.
type Scope = { size: number; record?(key: string): number };
interface Table {
  size: number;
  record?(key: string): number;
}
type Generic = { g<T>(x: T): T; size: number };

export function pick(s: Scope): Scope["record"] {
  return s.record;
}

function present(get: Scope["record"]): boolean {
  return get !== undefined;
}

export function has(s: Scope): boolean {
  return present(s.record);
}

export function size(n: Scope["size"]): number {
  return n;
}

export function genericSize(n: Generic["size"]): number {
  return n;
}

export function pickTable(t: Table): Table["record"] {
  return t.record;
}

export function run(get: Table["record"], key: string): number {
  if (get === undefined) return 0;
  const t: Table = { size: 1, record: get };
  return t.record?.(key) ?? 0;
}
