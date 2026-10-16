// A module re-exporting a library value under another name: the examples
// import the re-export beside the original.
export { brand as relayedBrand } from "@fixture/lib";

// Re-exports a client selects members of through the module's namespace
// (`invalid-written-reexport-value-import`).
export { selected, selected as renamed } from "@fixture/lib";
