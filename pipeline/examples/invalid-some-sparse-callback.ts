// A present element does not make some's third callback argument dense.
export function run(): boolean {
  const labels = [1, 2];
  const mapped = labels.map((value) => {
    labels.pop();
    return value;
  });
  return mapped.some((value, index, array) => array[1].toFixed() === "2");
}
