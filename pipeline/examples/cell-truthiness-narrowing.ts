// A `let` holding an object or `undefined`, held in a cell (a closure reads
// it, or `??=` writes it): a truthiness test of it, alone, as `&&`'s left
// operand or through an optional chain, leaves its contents neither null nor
// undefined on the truthy edge, so its member is read at the object.
type Section = { name: string; block: string[] };

export function named(lines: string[], s: Section): string {
  let current: Section | undefined;
  const peek = (): Section | undefined => current;
  if (lines.length) current = s;
  if (current) return current.name + String(peek() === current);
  return "";
}

export function blocks(lines: string[], s: Section): number {
  let current: Section | undefined;
  let count = 0;
  for (const line of lines) {
    (current ??= s).block.push(line);
    if (current?.block.length) count += current.block.length;
    else if (current && !current.name) current = undefined;
  }
  return count;
}
