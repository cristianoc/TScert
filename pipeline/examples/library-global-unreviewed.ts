// `Math.random` is not in the reviewed overlay of library globals: a global
// the standard library declares is read only through an entry that states it.
function roll(): number {
  return Math.random();
}
