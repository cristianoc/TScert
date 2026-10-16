// A reviver is client code the host calls on every member, whose results
// replace them: `JSON.parse` is read with the text only.
function decode(text: string): unknown {
  return JSON.parse(text, (key: string, value: unknown) => value);
}
