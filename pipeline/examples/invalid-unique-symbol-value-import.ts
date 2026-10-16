// Another imported unique symbol is another symbol: it is no value of `typeof brand`.
import { brand, other } from "@fixture/lib";

const held: typeof brand = other;
