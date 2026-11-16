/-! # View formats

The numeric storage formats a typed array's view spine admits (the note
*Tolerant frames*, §6, View-Write; docs/drafts/parity-interfaces.md, I3):
unsigned 8- and 16-bit integers, signed 32-bit integers and binary64
numbers. A view spine's role carries its format with its fixed length; the
conversion of a written number and the representations a format stores are
defined with the primitive view operations. Additional formats need their
own representation and conversion. -/
namespace Verification

/-- The admitted numeric storage formats of a view spine. -/
inductive ViewFormat where
  | uint8
  | uint16
  | int32
  | float64
  deriving DecidableEq, Repr

end Verification
