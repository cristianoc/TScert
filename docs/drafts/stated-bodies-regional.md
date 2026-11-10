# Draft: fresh stable fields, open question

The design is stated in [fresh array storage](../FOOTPRINTS.md#fresh-array-storage)
and [stated effects](../SOURCE-ELABORATION.md#stated-effects). One question
stays open.

## Open questions

1. Whether fresh cells become the fresh-field table at the cell key, kept
   by frames that keep values (`keepsValues`) where the field is not
   `@stable`, so that one table serves both. `CellFresh` requires a present
   field holding a `FreshValue`; `FieldFresh` permits absence and requires
   `FreshIfStore`.
