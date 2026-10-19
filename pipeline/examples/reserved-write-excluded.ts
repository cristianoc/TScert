// A write of `message` onto a record whose `name` is a number: no instance of
// the `Error` family, whose `name` is a string, has that type, so the write
// is an ordinary field write.
type Entry = { name: number; message: string };

export function relabel(entry: Entry): string {
  entry.message = `#${entry.name}`;
  return entry.message;
}
