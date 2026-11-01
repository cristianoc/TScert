// A visited element does not establish presence at another index.
export function run(): number[] {
  const xs = [1, 2];
  const mapped = xs.map((value) => {
    xs.pop();
    return value;
  });
  return mapped.filter((value, index, array) => array[1].toFixed() === "2");
}
