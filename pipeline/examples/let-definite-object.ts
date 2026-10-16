// `let x: T;` holds `undefined` until assigned, so its cell's contract
// admits it. A write of a value that is no `undefined`, an object here,
// leaves a fact that the cell holds some other value; a read where every
// path wrote one is at the contract less `undefined`.
interface Point {
  x: number;
  y: number;
}

export function ifElse(flag: boolean): Point {
  let p: Point;
  if (flag) {
    p = { x: 1, y: 2 };
  } else {
    p = { x: 0, y: 0 };
  }
  return p;
}

export function nested(input: number | string): Point {
  let p: Point;
  if (typeof input === "number") {
    if (input > 0) p = { x: input, y: 0 };
    else p = { x: 0, y: input };
  } else {
    p = { x: input.length, y: 0 };
  }
  return p;
}

export function switched(k: "a" | "b"): Point {
  let p: Point;
  switch (k) {
    case "a":
      p = { x: 1, y: 1 };
      break;
    case "b":
      p = { x: 2, y: 2 };
      break;
  }
  return p;
}

export function readField(flag: boolean): number {
  let p: Point;
  if (flag) p = { x: 1, y: 2 };
  else p = { x: 3, y: 4 };
  return p.x + p.y;
}
