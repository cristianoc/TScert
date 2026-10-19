// A global augmentation adding an overload to the standard library's
// `parseInt`, as another module of a project may declare it: an overload no
// reviewed entry lists.
declare global {
  function parseInt(value: boolean): number;
}
export {};
