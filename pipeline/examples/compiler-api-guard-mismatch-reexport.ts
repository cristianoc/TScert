// A module of the program re-exporting a listed guard as TypeScript reads it;
// Node, asked for `./compiler-api-guard-mismatch-reexport.js`, loads the
// JavaScript file beside it, which exports other code
// (`invalid-compiler-api-guard-reexport-mismatch`).
export { isIdentifier } from "typescript/unstable/ast";
