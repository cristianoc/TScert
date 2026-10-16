// `throw` leaves the function with any value; the result type says what a
// returned value is, never that nothing is thrown. A function or a closure
// whose body ends in a throw needs no return.
function check(x: number): number {
  if (x < 0) {
    throw "negative";
  }
  return x;
}

function fail(message: string): number {
  throw message;
}

function either(flag: boolean, x: number): number {
  if (flag) {
    return x;
  } else {
    throw { reason: "flag" };
  }
}

const reject = (s: string): number => {
  throw s;
};

const guarded = (x: number | null): number => {
  if (x === null) {
    throw x;
  }
  return x;
};
