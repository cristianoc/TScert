// A write of `message` onto a record whose `name` is a number: no instance of
// the `Error` family has that type, but the record's claim bounds none of its
// keys, so it does not exclude an object holding a prototype. The rule reads
// only that exclusion: refused at the write.
type Entry = { name: number; message: string };

export function relabel(entry: Entry): string {
  entry.message = `#${entry.name}`;
  return entry.message;
}
