// An enum with a member known only at run time states reverse keys at the
// values TypeScript computes; at a literal outside them the read may be
// undefined (here it is), which TypeScript types as `string`.
function measured(): number {
  return 3;
}
enum Open {
  A = 1,
  B = measured(),
}
function outside(): number {
  return Open[5].length;
}
