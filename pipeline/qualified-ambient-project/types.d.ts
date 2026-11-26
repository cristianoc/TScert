declare namespace A {
  type NumberType = number;
  namespace Inner {
    type T = NumberType;
    interface Box<T = A.NumberType> {
      readonly value: T;
      readonly label: B.Inner.T;
    }
  }
}

declare namespace B {
  namespace Inner {
    type T = string;
  }
}
