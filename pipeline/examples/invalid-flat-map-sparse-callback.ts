export function run(): string[] {
  const labels = [1, 2];
  const arms = labels.map((value) => {
    labels.pop();
    return value;
  });
  return arms.flatMap((value, index, array) => [array[1].toFixed()]);
}
