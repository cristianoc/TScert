"use strict";
/*
 * Receivers. The directive above makes this code strict, which is the receiver
 * rule the verifier models: a call passes its receiver unchanged, and a plain
 * call passes `undefined`. Each function returns what a reader can predict from
 * the receiver it names; tests/methods.mts runs them and checks each against
 * the value the wrong receiver would give.
 */

/** A property call passes its object, parenthesized or not; a copied method
 * is a value, and a plain call of it passes `undefined`. */
function propertyCall(seed: boolean): boolean {
  const owner = {
    value: seed,
    get(this: { value: boolean }): boolean {
      return this.value;
    },
    constant(): boolean {
      return true;
    },
  };
  const copied = owner.constant;
  const direct = owner.get();
  // The parentheses are the point: a formatter would drop them.
  // prettier-ignore
  const grouped = (owner.get)();
  const constant = copied();
  return constant ? (direct ? grouped : !grouped) : false;
}

/** `.call` rebinds an ordinary function. The arrow it returns keeps the
 * receiver of the call that created it: `this` in an arrow is a capture. */
function callRebinds(seed: boolean): boolean {
  const first = { value: seed };
  const second = { value: !seed };
  const reader = function (this: { value: boolean }): () => boolean {
    return (): boolean => this.value;
  };
  const kept = reader.call(first);
  const rebound = reader.call(second);
  return kept() ? !rebound() : rebound();
}

/** The method is read and saved before the actuals run: an actual that
 * replaces the field changes the next call, not this one. */
function savedCallee(seed: boolean): boolean {
  const owner: {
    value: boolean;
    pick: (this: { value: boolean }, x: boolean) => boolean;
  } = {
    value: seed,
    pick(this: { value: boolean }, x: boolean): boolean {
      return this.value;
    },
  };
  const flip = function (this: { value: boolean }, x: boolean): boolean {
    return !this.value;
  };
  const replace = (): boolean => {
    owner.pick = flip;
    return true;
  };
  const first = owner.pick(replace());
  const second = owner.pick(true);
  return first ? !second : second;
}

/** The receiver is the object, not a copy of its fields: an actual that
 * writes a field runs before the body reads it. */
function receiverFieldWrite(seed: boolean): boolean {
  const owner = {
    value: seed,
    get(this: { value: boolean }, x: boolean): boolean {
      return this.value;
    },
  };
  return owner.get((owner.value = !seed));
}

/** A method writes through its receiver, which needs the write capability of
 * the field it names. */
function receiverWrite(seed: boolean): boolean {
  const owner = {
    value: seed,
    flip(this: { value: boolean }): boolean {
      this.value = !this.value;
      return this.value;
    },
  };
  owner.flip();
  return owner.value;
}

/** `.bind` saves its target, receiver and prefix, not the receiver's fields:
 * a later write is seen. A second `.bind` cannot replace the saved receiver. */
function bindRebind(seed: boolean): boolean {
  const owner = { value: seed };
  const other = { value: seed };
  const read = function (this: { value: boolean }, flip: boolean): boolean {
    return flip ? !this.value : this.value;
  };
  const bound = read.bind(owner, false);
  owner.value = !seed;
  const rebound = bound.bind(other);
  return rebound();
}

/** `.call` on a bound function passes a receiver the bound function drops. */
function boundCall(seed: boolean): boolean {
  const owner = { value: seed };
  const other = { value: !seed };
  const read = function (this: { value: boolean }): boolean {
    return this.value;
  };
  const bound = read.bind(owner);
  return bound.call(other);
}
/** A variadic method: the fixed actual, then every further one at its element
 * contract, including a spread, with the object as the receiver. */
function variadicMethod(seed: boolean): boolean {
  const owner = {
    value: seed,
    any(this: { value: boolean }, first: boolean, ...rest: boolean[]): boolean {
      return first ? this.value : !this.value;
    },
  };
  const extra: [boolean, boolean] = [seed, !seed];
  const spread = owner.any(false, ...extra);
  return owner.any(true, false, true) ? !spread : spread;
}

/** A tuple spread into a method's fixed parameters, read after the method. */
function tupleSpreadMethod(seed: boolean): boolean {
  const owner = {
    value: seed,
    pick(this: { value: boolean }, a: boolean, b: boolean): boolean {
      return a ? this.value : b;
    },
  };
  const both: [boolean, boolean] = [seed, !seed];
  return owner.pick(...both);
}

/** A method read from an array element: the array is the receiver. */
function elementMethod(seed: boolean): boolean {
  const read = function (): boolean {
    return seed;
  };
  const table: [() => boolean] = [read];
  return table[0]();
}

/** Binding a variadic function takes its first fixed positions, then its
 * element contract; the bound function keeps the rest of the signature. */
function bindVariadic(seed: boolean): boolean {
  const owner = { value: seed };
  const pick = function (
    this: { value: boolean },
    first: boolean,
    ...rest: boolean[]
  ): boolean {
    return first ? this.value : !this.value;
  };
  const within = pick.bind(owner, true);
  const past = pick.bind(owner, false, true);
  return within(false, true) ? past() : !past(true);
}

/** A declaration is the entry point: its `this` parameter is an input assumed
 * at its annotation, and an arrow inside captures it. */
function declaredReceiver(this: { value: boolean }, flip: boolean): boolean {
  const read = (): boolean => this.value;
  return flip ? !read() : this.value;
}
