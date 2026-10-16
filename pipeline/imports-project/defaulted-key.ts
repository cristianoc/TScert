// A module whose default export is an object literal with a computed key
// (`invalid-written-default-key-value-import`). Nothing runs it.
type B<T extends string> = T;
const key: keyof { a: B<any> } = "a";
export default { [key]: 1 };
