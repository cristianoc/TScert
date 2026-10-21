// An enum a program module declares, imported directly and through a
// re-export: TypeScript's emit builds its object with the reverse mapping,
// so a read at a key of its values is a string, through `typeof` too. The
// project checks indexed reads, so TypeScript adds `undefined`.
import { Grade } from "@fixture/grades";
import { Mark } from "@fixture/grades-relay";

export function gradeName(g: Grade): string {
  const name: string = Grade[g] ?? "";
  return name;
}

export function markName(): string {
  const name: string = Mark[Mark.High] ?? "";
  return name;
}

export function objectName(o: typeof Mark): string {
  const name: string = o[1] ?? "";
  return name;
}
