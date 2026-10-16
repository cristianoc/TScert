// `id!: number` promises TypeScript the field is assigned, but this
// constructor never assigns it: every instance holds `undefined` there.
// (TypeScript accepts this.)
class Late {
  id!: number;
  constructor(id: number) {}
}
export function idOf(): number {
  return new Late(1).id;
}
