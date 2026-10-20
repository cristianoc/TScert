// What Node loads for `./compiler-api-guard-mismatch-reexport.js`: a function
// answering `true` of every node, where TypeScript reads the re-export of
// the `.ts` module beside it.
export function isIdentifier(node) {
  return true;
}
