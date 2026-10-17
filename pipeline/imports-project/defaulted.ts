// A module whose default export is an expression asserted to a type
// (`invalid-written-symbols-default-value-import`). Nothing runs it.
type B<T extends string> = T;
export default "a" as keyof { a: B<any> };
