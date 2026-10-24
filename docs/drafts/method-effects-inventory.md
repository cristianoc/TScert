# Method effects: the inventory of `expr`'s contract closure

The functions of `tools/` that `expr` (the gate's lowering of an expression)
and the gate's `TermScope` object reach, one entry each, as the scan of
[§12](method-effects.md#12-exprs-contract-closure) finds them. A body
reaches a function it refers to by binding: a module binding, an import, a
`Gate` member or method field read off `this` or `gate`, or a `TermScope`
member read off `scope` or `inner` (the entry `Gate.termScope`, whose object
implements `TermScope`). Each entry gives:

- its statement: the footprint its result's `Within<F, T>` states, or
  "states nothing";
- its basis: certified where its own census slice verifies; otherwise not
  certified, with the scan's audit of its body: the store-shrinking
  operations (`pop`, `shift`, `splice`, `sort`, `reverse`, `fill`,
  `copyWithin`, `delete`, `clear`, a `length` write) and the
  `JSON.stringify` calls it holds, and the functions it calls that state
  nothing;
- the functions of this list it calls.

A caller verifying relative to a statement does not certify it (§12).

The operations the audit lists act within `{value: any, store: grow}`:
`enumEntries`' and `enumMembersTerm`'s `sort` acts on the array `filter`
just returned, and `Gate.closureParamType`'s `JSON.stringify` serializes an
array of two strings and a span, a JSON value. Of the functions stating
nothing, `fail` and `refuseReceiverForm` return `never` and
`functionLikeNode` and `isNode` are type predicates.

Measured on 2026-10-24 at commit 129e9dd, with each census stage limited to
300 s: of 183 functions, 61 are certified, 75 have a slice that does not
verify, 22 top-level functions have no slice of their own (the census
slices function declarations), and 25 are `Gate` members, which the census
does not slice.

### tools/declaration-graph.mts

- `libraryArguments`: {value: any, store: grow}; certified (its slice verifies).
- `libraryTerm`: {value: any, store: grow}; certified (its slice verifies); calls `expandMapped`, `substitute`.

### tools/fragment-classes.mts

- `enumEntries`: {value: any, store: grow}; not certified (its slice is unverified); audited: its operations `all.filter((e) => index(e.key)).sort` are listed below; calls `Gate.fail`, `enumMembers`.
- `enumMembers`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`.
- `enumObjectTerm`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `enumEntries`, `enumMembers`, `enumOpen`, `enumMembersTerm`, `literalTerm`.
- `enumOpen`: {value: any, store: grow}; certified (its slice verifies); calls `enumMembers`.
- `enumRead`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`, `Gate.local`, `Gate.span`, `enumMemberName`, `literalExpr`.
- `enumTerm`: {value: any, store: grow}; certified (its slice verifies); calls `enumMembers`, `literalTerm`.
- `identityKey`: {value: any, store: grow}; certified (its slice verifies).
- `memberKey`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`, `Gate.span`.
- `ownClass`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`, `Gate.span`, `selfName`.
- `readsClass`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.span`.
- `selfConstruction`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `staticInitOf`, `freshName`, `selfConstructs`.
- `staticInitOf`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `staticPrivate`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `staticName`, `isStatic`, `nameOf`.

### tools/fragment-expressions.mts

- `binary`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.intrinsic`, `Gate.local`, `Gate.span`, `Gate.text`, `memberKey`, `ownClass`, `staticPrivate`, `chainComparison`, `expr`, `hasInstanceAlong`, `hasInstanceClass`, `staticHasInstance`, `update`, `assignedSteps`, `steppedPattern`, `classKey`, `inKey`, `prototypeName`, `skipParentheses`, `staticName`.
- `chainComparison`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.span`, `chainReceiver`, `inertRead`, `skipParentheses`.
- `chainLink`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.spreadOperand`, `Gate.typeOf`, `memberKey`, `staticPrivate`, `expr`, `assignedNames`, `readCannotThrow`.
- `chainReceiver`: {value: any, store: grow}; certified (its slice verifies); calls `skipParentheses`.
- `confined`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `resolve`, `nameOf`.
- `expr`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.awaitExpr`, `Gate.fail`, `Gate.intrinsic`, `Gate.libraryName`, `Gate.local`, `Gate.namespaceMember`, `Gate.span`, `Gate.spreadOperand`, `Gate.typeOf`, `enumRead`, `memberKey`, `ownClass`, `readsClass`, `selfConstruction`, `staticInitOf`, `staticPrivate`, `binary`, `knownLocal`, `lambda`, `objectFields`, `optionalChain`, `refuseReceiverForm`, `template`, `update`, `assignedNames`, `collect`, `readCannotThrow`, `callableAssign`, `literalExpr`, `staticFieldOf`, `staticMethodOf`, `staticName`, `bigintText`, `numericLexeme`.
- `hasInstanceAlong`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `hasInstanceClass`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `hasInstanceAlong`.
- `inertRead`: {value: any, store: grow}; certified (its slice verifies); calls `resolve`.
- `knownLocal`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `confined`, `localArrow`.
- `lambda`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.asyncCompletion`, `Gate.closureParamType`, `Gate.enterTypeParams`, `Gate.fail`, `Gate.intrinsic`, `Gate.leaveTypeParams`, `Gate.local`, `Gate.optionalTypeOf`, `Gate.restType`, `Gate.span`, `Gate.statedResult`, `Gate.typeOf`, `Gate.useStrict`, `expr`, `guardOf`, `guardResult`, `initializedBefore`, `pattern`, `statements`, `booleanForm`, `booleanReturn`, `completes`, `firstOptional`, `parameterName`, `propertyKeyText`, `optionalTerm`.
- `letWrites`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `localArrow`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.libraryName`, `localValues`, `memberMayBeWritten`, `memberOf`, `moduleFunction`, `resolve`.
- `localValues`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `letWrites`, `resolve`.
- `memberMayBeWritten`: {value: any, store: grow}; certified (its slice verifies).
- `memberOf`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `localArrow`, `localValues`.
- `moduleFunction`: {value: any, store: grow}; certified (its slice verifies); calls `memberMayBeWritten`, `resolve`, `nameOf`.
- `objectFields`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `Gate.writtenSymbol`, `expr`, `lambda`, `literalTerm`, `numericKey`.
- `optionalChain`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `chainLink`, `expr`.
- `refuseReceiverForm`: states nothing (never returns); certified (its slice verifies); calls `Gate.fail`, `Gate.span`.
- `resolve`: {value: any, store: grow}; certified (its slice verifies); calls `bindingScope`, `nameOf`.
- `staticHasInstance`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.span`.
- `template`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.span`, `expr`.
- `update`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `expr`.

### tools/fragment-guards.mts

- `guardOf`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.span`, `promiseOf`.
- `guardResult`: {value: any, store: grow}; certified (its slice verifies).

### tools/fragment-statements.mts

- `abrupt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `assignedNames`: {value: any, store: grow}; certified (its slice verifies).
- `assignedSteps`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation.
- `bindsName`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `block`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `statements`.
- `closeStatements`: {value: any, store: grow}; certified (its slice verifies).
- `collect`: {value: any, store: grow}; certified (its slice verifies); calls `expr`, `collectStep`, `protocolStart`.
- `collectStep`: {value: any, store: grow}; certified (its slice verifies); calls `protocolStep`.
- `controlStmt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`, `Gate.span`, `expr`, `block`, `forInStmt`, `forOfPattern`, `forStmt`, `neverAssigned`, `protocolForOf`, `statements`, `switchStmt`, `tryStmt`.
- `declarations`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`, `Gate.optionalTypeOf`, `Gate.span`, `Gate.typeOf`, `expr`, `neverAssigned`, `patternStmt`.
- `forInStmt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.intrinsic`, `Gate.local`, `Gate.span`, `expr`, `block`, `neverAssigned`, `token`, `forInEntryReads`.
- `forOfPattern`: {value: any, store: grow}; certified (its slice verifies); calls `initializedBefore`, `pattern`.
- `forStmt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `expr`, `block`, `collect`, `declarations`, `token`.
- `functionLikeNode`: states nothing (a type predicate); not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `hoisting`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `hoistTarget`, `letPattern`, `sites`, `stmt`.
- `hoistTarget`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.span`, `assignedNames`, `readCannotThrow`.
- `importedNames`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `inert`: {value: keep, store: keep}; certified (its slice verifies).
- `initializedBefore`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`, `namesRead`, `patternNames`.
- `letPattern`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `expr`, `initializedBefore`, `neverAssigned`, `pattern`, `skipParentheses`.
- `markEarly`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`.
- `neverAssigned`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.local`, `bindingScope`.
- `pattern`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`, `Gate.local`, `Gate.span`, `expr`, `patternDefaults`, `steppedPattern`.
- `patternDefaults`: {value: keep, store: keep}; certified (its slice verifies).
- `patternStmt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`, `expr`, `initializedBefore`, `pattern`, `protocolPattern`, `skipParentheses`.
- `protocolForOf`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`, `Gate.span`, `expr`, `block`, `closeStatements`, `forOfPattern`, `token`.
- `protocolPattern`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.termScope`, `expr`, `closeStatements`, `collectStep`, `pattern`, `protocolStart`, `protocolStep`, `statements`.
- `protocolStart`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`.
- `protocolStep`: {value: any, store: grow}; certified (its slice verifies).
- `readCannotThrow`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.span`, `bindsName`, `functionLikeNode`, `importedNames`, `statements`, `within`.
- `sites`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `within`, `freeOffsets`.
- `statements`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `abrupt`, `hoisting`, `markEarly`, `typeStatement`.
- `steppedPattern`: {value: any, store: keep}; certified (its slice verifies); calls `Gate.fail`, `inert`.
- `stmt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.intrinsic`, `Gate.span`, `expr`, `controlStmt`, `declarations`, `booleanForm`, `booleanReturn`, `jumpTarget`, `switchLabel`.
- `switchStmt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`, `Gate.span`, `expr`, `collect`, `statements`, `token`, `switchLabel`.
- `token`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.fail`.
- `tryStmt`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.local`, `Gate.span`, `statements`.
- `typeStatement`: {value: any, store: grow}; certified (its slice verifies).
- `within`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.

### tools/fragment-support.mts

- `bindingScope`: {value: any, store: grow}; certified (its slice verifies).
- `booleanForm`: {value: any, store: grow}; certified (its slice verifies).
- `booleanReturn`: {value: any, store: grow}; certified (its slice verifies).
- `callableAssign`: {value: any, store: grow}; certified (its slice verifies).
- `classKey`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `completes`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `enumMemberName`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `firstOptional`: {value: any, store: grow}; certified (its slice verifies).
- `forInEntryReads`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `runsCodeOrWrites`, `writesName`, `writtenElement`.
- `freeOffsets`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation.
- `freshName`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `inKey`: {value: any, store: grow}; certified (its slice verifies).
- `jumpTarget`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `literalExpr`: {value: any, store: grow}; certified (its slice verifies); calls `numberText`.
- `namesRead`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation.
- `parameterName`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `patternNames`: {value: any, store: grow}; certified (its slice verifies).
- `propertyKeyText`: {value: keep, store: keep}; certified (its slice verifies).
- `prototypeName`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `runsCode`: {value: any, store: grow}; certified (its slice verifies).
- `runsCodeOrWrites`: {value: any, store: grow}; certified (its slice verifies).
- `selfConstructs`: {value: any, store: grow}; certified (its slice verifies); calls `runsCode`, `isStatic`.
- `selfName`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `skipParentheses`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `staticFieldOf`: {value: any, store: grow}; certified (its slice verifies).
- `staticMethodOf`: {value: any, store: grow}; certified (its slice verifies).
- `staticName`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `switchLabel`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `writesName`: {value: any, store: grow}; certified (its slice verifies).
- `writtenElement`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.

### Gate (tools/fragment-parse.mts)

- `asyncCompletion`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.intrinsic`, `Gate.span`.
- `awaitExpr`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.intrinsic`, `Gate.span`, `expr`.
- `blockTypeAt`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.span`.
- `closureParamType`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: its operations `JSON.stringify([target.module, target.span, target.name])` are listed below; calls `Gate.fail`, `Gate.hasTypeParam`, `Gate.optionalTypeOf`, `Gate.span`, `Gate.typeOf`, `visitType`.
- `declaredReference`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`.
- `enterTypeParams`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.qualificationBound`, `Gate.typeOf`, `resolutionSlots`.
- `fail`: states nothing (never returns); not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation.
- `hasTypeParam`: {value: keep, store: keep}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.termScope`.
- `intrinsic`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation.
- `leaveTypeParams`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation.
- `libraryName`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.span`.
- `local`: {value: keep, store: keep}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation.
- `namespaceMember`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.span`.
- `optionalTypeOf`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.span`, `Gate.typeOf`, `optionalTerm`.
- `qualificationBound`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.blockTypeAt`, `Gate.hasTypeParam`.
- `restType`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.typeOf`, `restPositions`, `restRefusal`, `restTerm`.
- `span`: {value: keep, store: keep}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation.
- `spreadOperand`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.intrinsic`, `Gate.span`, `expr`, `collect`.
- `statedResult`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `statedResult`.
- `termScope`: {value: any, store: grow} (each function member of the `TermScope` interface, which the object this method makes implements); not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.blockTypeAt`, `Gate.declaredReference`, `Gate.fail`, `Gate.hasTypeParam`, `Gate.namespaceMember`, `Gate.span`, `Gate.typeParamName`, `libraryArguments`, `libraryTerm`, `enumMembers`, `enumObjectTerm`, `enumTerm`, `identityKey`, `enumMembersTerm`, `literalTerm`, `resolutionSlots`, `substitute`.
- `text`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation.
- `typeOf`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `typeTerm`.
- `typeParamName`: {value: any, store: keep}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.termScope`.
- `useStrict`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation.
- `writtenSymbol`: {value: any, store: grow}; not certified (a `Gate` member, which the census does not slice); audited: no store-shrinking or serializing operation; calls `Gate.fail`, `Gate.span`.

### tools/intrinsics.mts

- `enumMembersTerm`: {value: any, store: grow}; not certified (its slice is unverified); audited: its operations `keyed.filter(f => index(f.key)).sort` are listed below; calls `literalTerm`.
- `literalTerm`: {value: any, store: grow}; certified (its slice verifies); calls `numberText`.
- `numberText`: {value: any, store: grow}; certified (its slice verifies).

### tools/syntax.mts

- `childOf`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `isNode`.
- `childrenOf`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `isNode`.
- `isNode`: states nothing (a type predicate); not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `isStatic`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation; calls `childrenOf`.
- `nameOf`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation; calls `childOf`.

### tools/type-graph.mts

- `footprintEffect`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `promiseEffect`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.

### tools/type-term.mts

- `bigintText`: {value: any, store: grow}; certified (its slice verifies).
- `computedForm`: {value: any, store: grow}; certified (its slice verifies); calls `intersectionOperands`.
- `constructorForms`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `quantified`, `signatures`.
- `emptyObject`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `expandMapped`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `emptyObject`, `numericKey`.
- `hostReceiver`: {value: any, store: grow}; certified (its slice verifies).
- `indexKinds`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `typeTerm`.
- `intersection`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `computedForm`, `intersectionOperands`, `typeTerm`.
- `intersectionOperands`: {value: any, store: grow}; certified (its slice verifies); calls `unwrap`.
- `mapped`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `members`, `typeTerm`.
- `members`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `constructorForms`, `hostReceiver`, `indexKinds`, `oneTerm`, `propertyKey`, `quantified`, `sameIndex`, `signatures`, `spanOf`, `typeTerm`.
- `numericKey`: {value: any, store: grow}; certified (its slice verifies).
- `numericLexeme`: {value: any, store: grow}; certified (its slice verifies).
- `oneTerm`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `optionalTerm`: {value: any, store: grow}; certified (its slice verifies).
- `ownedSlots`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `promiseOf`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `promiseEffect`, `spanOf`, `typeTerm`.
- `propertyKey`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.termScope`, `numericKey`.
- `quantified`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `resolutionSlots`, `signatures`, `spanOf`, `typeTerm`.
- `readTypeTerm`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `bigintText`, `computedForm`, `constructorForms`, `emptyObject`, `expandMapped`, `intersection`, `mapped`, `members`, `numericLexeme`, `oneTerm`, `quantified`, `signatures`, `spanOf`, `tuple`, `typeTerm`, `unwrap`.
- `resolutionSlots`: {value: any, store: grow}; certified (its slice verifies).
- `restPositions`: {value: any, store: grow}; certified (its slice verifies).
- `restRefusal`: {value: any, store: grow}; not certified (its slice is unverified); audited: no store-shrinking or serializing operation.
- `restTerm`: {value: any, store: grow}; certified (its slice verifies); calls `Gate.termScope`.
- `sameData`: {value: keep, store: keep}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation.
- `sameIndex`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `sameData`.
- `signatures`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `optionalTerm`, `promiseOf`, `restPositions`, `restRefusal`, `restTerm`, `spanOf`, `statedEffect`, `statedResult`, `typeTerm`.
- `spanOf`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation; calls `Gate.termScope`.
- `statedEffect`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation; calls `footprintEffect`.
- `statedResult`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `statementOf`, `unwrap`.
- `statementOf`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `unwrap`.
- `substitute`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation.
- `tuple`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `tupleMember`, `typeTerm`.
- `tupleMember`: {value: any, store: grow}; certified (its slice verifies).
- `typeTerm`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `Gate.termScope`, `readTypeTerm`, `validateAnnotation`.
- `unwrap`: {value: any, store: grow}; not certified (no slice of its own); audited: no store-shrinking or serializing operation.
- `validateAnnotation`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `visitType`.
- `visitType`: {value: any, store: grow}; not certified (its slice is unsupported); audited: no store-shrinking or serializing operation; calls `ownedSlots`.
