// Names the gate lowers specially are recognised by what TypeScript binds
// them to, not by spelling: a local `Math` or a parameter `JSON` shadows the
// global, and an object's own `call` member is no `Function.prototype.call`.
const Math = { max: (a: number, b: number): string => `local ${a + b}` };

export function localMax(): string {
  return Math.max(1, 2);
}

export function parameterJson(JSON: {
  stringify: (n: number) => number;
}): number {
  return JSON.stringify(3);
}

const doubler = { call: (n: number): number => n * 2 };

export function ownCall(): number {
  return doubler.call(4);
}
