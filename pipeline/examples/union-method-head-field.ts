// A method call on a union of a host of the method and a record holding a
// function-valued field of its name, whose actual runs code: the saved head
// is a read of the key, which no rule types for the host's member.
interface Host {
  tag: "host";
  name(n: number): string;
}
interface Field {
  tag: "field";
  name: (n: number) => string;
}

function argument(): number {
  return 1;
}

export function name(o: Host | Field): string {
  return o.name(argument());
}
