// A module with no function is still checked: its initialization reads past
// the end of an array, `undefined`, which the annotation `number` excludes,
// though TypeScript accepts it.
const values: number[] = [1, 2];
const third: number = values[2];
