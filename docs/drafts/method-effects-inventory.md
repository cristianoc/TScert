# Method effects: the inventory of `expr`'s contract closure

The functions `expr` reaches through `Gate`'s fields and members and by
direct call, with the functions the gate's `TermScope` object calls, as
listed by the scan of [§10](method-effects.md#10-measurement), one entry
each: its statement (the footprint its result's `Within<F, T>` states, or
"states nothing"), its basis, and the functions of this list its body names.
A function is certified where its own census slice verifies; a caller
verifying relative to a statement does not certify it
([§12](method-effects.md#12-exprs-contract-closure)).

Measured on 2026-10-24 at commit 7441c7b, with each census stage limited to
300 s: of 178 functions, 58 are certified, 73 have a slice that does not
verify, 22 top-level functions have no slice of their own, and 25 are `Gate`
members, which the census does not slice.

### Gate (tools/fragment-parse.mts)

- `asyncCompletion`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.intrinsic`, `Gate.span`, `block`, `statements`.
- `awaitExpr`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.intrinsic`, `Gate.span`, `expr`.
- `blockTypeAt`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.span`.
- `closureParamType`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.fail`, `Gate.hasTypeParam`, `Gate.optionalTypeOf`, `Gate.span`, `Gate.typeOf`, `visitType`.
- `declaredReference`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.fail`, `Gate.span`.
- `enterTypeParams`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.fail`, `Gate.local`, `Gate.qualificationBound`, `Gate.text`, `Gate.typeOf`, `resolutionSlots`.
- `fail`: states nothing (never); a `Gate` member, not certified (the census slices top-level functions only).
- `hasTypeParam`: {value: keep, store: keep}; a `Gate` member, not certified (the census slices top-level functions only).
- `intrinsic`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only).
- `leaveTypeParams`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only).
- `libraryName`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.span`.
- `local`: {value: keep, store: keep}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.text`.
- `namespaceMember`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.local`, `Gate.span`.
- `optionalTypeOf`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.span`, `Gate.typeOf`, `optionalTerm`.
- `qualificationBound`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.blockTypeAt`, `Gate.hasTypeParam`, `Gate.text`.
- `restType`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.fail`, `Gate.typeOf`, `restPositions`, `restRefusal`, `restTerm`.
- `span`: {value: keep, store: keep}; a `Gate` member, not certified (the census slices top-level functions only).
- `spreadOperand`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.fail`, `Gate.intrinsic`, `Gate.span`, `expr`, `collect`.
- `statedResult`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `statedResult`.
- `termScope`: states nothing; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.blockTypeAt`, `Gate.declaredReference`, `Gate.fail`, `Gate.hasTypeParam`, `Gate.namespaceMember`, `Gate.span`, `Gate.text`, `Gate.typeParamName`, `enumMembers`, `enumObjectTerm`, `enumTerm`, `block`, `enumMembersTerm`, `literalTerm`, `members`, `resolutionSlots`, `substitute`.
- `text`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only).
- `typeOf`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `typeTerm`.
- `typeParamName`: {value: any, store: keep}; a `Gate` member, not certified (the census slices top-level functions only).
- `useStrict`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `statements`.
- `writtenSymbol`: {value: any, store: grow}; a `Gate` member, not certified (the census slices top-level functions only); calls `Gate.fail`, `Gate.span`.

### tools/fragment-classes.mts

- `enumEntries`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `enumMembers`, `members`.
- `enumMembers`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `members`.
- `enumObjectTerm`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`, `enumEntries`, `enumMembers`, `enumOpen`, `enumMembersTerm`, `literalTerm`.
- `enumOpen`: {value: any, store: grow}; certified: its slice verifies; calls `enumMembers`.
- `enumRead`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `Gate.local`, `Gate.span`, `enumMemberName`, `literalExpr`, `members`.
- `enumTerm`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`, `enumMembers`, `literalTerm`.
- `memberKey`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `Gate.span`, `Gate.text`.
- `ownClass`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `Gate.span`, `selfName`.
- `readsClass`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`.
- `selfConstruction`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `Gate.text`, `staticInitOf`, `statements`, `freshName`, `selfConstructs`.
- `staticInitOf`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.text`.
- `staticPrivate`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `Gate.text`, `statements`, `staticName`, `isStatic`, `nameOf`, `members`.

### tools/fragment-expressions.mts

- `binary`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.intrinsic`, `Gate.local`, `Gate.span`, `Gate.text`, `memberKey`, `ownClass`, `staticPrivate`, `chainComparison`, `expr`, `hasInstanceAlong`, `hasInstanceClass`, `staticHasInstance`, `update`, `assignedSteps`, `steppedPattern`, `classKey`, `inKey`, `prototypeName`, `skipParentheses`, `staticName`, `unwrap`.
- `chainComparison`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`, `chainReceiver`, `inertRead`, `skipParentheses`.
- `chainLink`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.spreadOperand`, `Gate.text`, `Gate.typeOf`, `memberKey`, `staticPrivate`, `expr`, `assignedNames`, `readCannotThrow`.
- `chainReceiver`: {value: any, store: grow}; certified: its slice verifies; calls `skipParentheses`.
- `confined`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.text`, `resolve`, `collect`, `nameOf`.
- `expr`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.awaitExpr`, `Gate.fail`, `Gate.intrinsic`, `Gate.libraryName`, `Gate.local`, `Gate.namespaceMember`, `Gate.span`, `Gate.spreadOperand`, `Gate.text`, `Gate.typeOf`, `enumRead`, `memberKey`, `ownClass`, `readsClass`, `selfConstruction`, `staticInitOf`, `staticPrivate`, `binary`, `knownLocal`, `lambda`, `objectFields`, `optionalChain`, `refuseReceiverForm`, `template`, `update`, `assignedNames`, `collect`, `readCannotThrow`, `callableAssign`, `literalExpr`, `staticFieldOf`, `staticMethodOf`, `staticName`, `fn`, `isStatic`, `bigintText`, `numericLexeme`.
- `hasInstanceAlong`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.text`, `statements`, `token`, `members`.
- `hasInstanceClass`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.text`, `hasInstanceAlong`.
- `inertRead`: {value: any, store: grow}; certified: its slice verifies; calls `resolve`.
- `knownLocal`: {value: any, store: grow}; not certified: its slice is unverified; calls `confined`, `localArrow`.
- `lambda`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.asyncCompletion`, `Gate.closureParamType`, `Gate.enterTypeParams`, `Gate.fail`, `Gate.intrinsic`, `Gate.leaveTypeParams`, `Gate.local`, `Gate.optionalTypeOf`, `Gate.restType`, `Gate.span`, `Gate.statedResult`, `Gate.text`, `Gate.typeOf`, `Gate.useStrict`, `expr`, `guardOf`, `guardResult`, `initializedBefore`, `pattern`, `statements`, `booleanForm`, `booleanReturn`, `completes`, `firstOptional`, `parameterName`, `optionalTerm`, `statedResult`.
- `letWrites`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.text`, `block`.
- `localArrow`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.libraryName`, `Gate.text`, `localValues`, `memberMayBeWritten`, `memberOf`, `moduleFunction`, `resolve`.
- `localValues`: {value: any, store: grow}; not certified: its slice is unverified; calls `letWrites`, `resolve`.
- `memberMayBeWritten`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`.
- `memberOf`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.text`, `localArrow`, `localValues`.
- `moduleFunction`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `memberMayBeWritten`, `resolve`, `statements`, `nameOf`.
- `objectFields`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `Gate.text`, `Gate.writtenSymbol`, `expr`, `lambda`, `literalTerm`, `numericKey`.
- `optionalChain`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `chainLink`, `expr`.
- `refuseReceiverForm`: states nothing (never); certified: its slice verifies; calls `Gate.fail`, `Gate.span`, `Gate.text`.
- `resolve`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `bindingScope`, `nameOf`.
- `staticHasInstance`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`.
- `template`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`, `Gate.text`, `expr`.
- `update`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `expr`, `token`.

### tools/fragment-guards.mts

- `guardOf`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.span`, `Gate.text`, `promiseOf`.
- `guardResult`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`.

### tools/fragment-statements.mts

- `abrupt`: {value: any, store: grow}; not certified: its slice is unverified; calls `block`, `statements`.
- `assignedNames`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`.
- `assignedSteps`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.text`.
- `bindsName`: {value: any, store: grow}; not certified: no slice of its own; calls `Gate.text`.
- `block`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `statements`.
- `closeStatements`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`.
- `collect`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`, `expr`, `update`, `collectStep`, `protocolStart`.
- `collectStep`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`, `protocolStep`.
- `controlStmt`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.text`, `expr`, `update`, `block`, `declarations`, `forInStmt`, `forOfPattern`, `forStmt`, `neverAssigned`, `protocolForOf`, `statements`, `switchStmt`, `tryStmt`.
- `declarations`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.optionalTypeOf`, `Gate.span`, `Gate.text`, `Gate.typeOf`, `expr`, `neverAssigned`, `patternStmt`.
- `forInStmt`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.intrinsic`, `Gate.local`, `Gate.span`, `Gate.text`, `expr`, `block`, `declarations`, `neverAssigned`, `token`, `forInEntryReads`.
- `forOfPattern`: {value: any, store: grow}; certified: its slice verifies; calls `initializedBefore`, `pattern`.
- `forStmt`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `Gate.text`, `expr`, `update`, `block`, `collect`, `declarations`, `token`.
- `functionLikeNode`: states nothing (type predicate); not certified: no slice of its own.
- `hoistTarget`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`, `Gate.text`, `assignedNames`, `declarations`, `readCannotThrow`.
- `hoisting`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`, `hoistTarget`, `letPattern`, `sites`, `stmt`.
- `importedNames`: {value: any, store: grow}; not certified: no slice of its own; calls `Gate.text`.
- `inert`: {value: keep, store: keep}; certified: its slice verifies.
- `initializedBefore`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `namesRead`, `patternNames`.
- `letPattern`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `expr`, `declarations`, `initializedBefore`, `neverAssigned`, `pattern`, `skipParentheses`.
- `markEarly`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.text`, `declarations`.
- `neverAssigned`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.local`, `declarations`, `bindingScope`.
- `pattern`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.text`, `expr`, `patternDefaults`, `steppedPattern`.
- `patternDefaults`: {value: keep, store: keep}; certified: its slice verifies.
- `patternStmt`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `expr`, `declarations`, `initializedBefore`, `pattern`, `protocolPattern`, `skipParentheses`.
- `protocolForOf`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.span`, `expr`, `update`, `block`, `closeStatements`, `declarations`, `forOfPattern`, `token`.
- `protocolPattern`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.text`, `expr`, `update`, `closeStatements`, `collectStep`, `pattern`, `protocolStart`, `protocolStep`, `statements`, `stmt`.
- `protocolStart`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `Gate.span`.
- `protocolStep`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`.
- `readCannotThrow`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`, `Gate.text`, `bindsName`, `block`, `declarations`, `functionLikeNode`, `importedNames`, `statements`, `within`.
- `sites`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.span`, `Gate.text`, `within`, `freeOffsets`.
- `statements`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.text`, `abrupt`, `declarations`, `hoisting`, `markEarly`, `typeStatement`.
- `steppedPattern`: {value: any, store: keep}; certified: its slice verifies; calls `Gate.fail`, `inert`.
- `stmt`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.intrinsic`, `Gate.span`, `expr`, `controlStmt`, `declarations`, `booleanForm`, `booleanReturn`, `jumpTarget`, `switchLabel`.
- `switchStmt`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.text`, `expr`, `collect`, `declarations`, `statements`, `token`, `switchLabel`, `unwrap`.
- `token`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.fail`, `Gate.text`.
- `tryStmt`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.fail`, `Gate.local`, `Gate.span`, `Gate.text`, `block`, `statements`.
- `typeStatement`: {value: any, store: grow}; certified: its slice verifies.
- `within`: {value: any, store: grow}; not certified: no slice of its own.

### tools/fragment-support.mts

- `bindingScope`: {value: any, store: grow}; certified: its slice verifies; calls `block`.
- `booleanForm`: {value: any, store: grow}; certified: its slice verifies.
- `booleanReturn`: {value: any, store: grow}; certified: its slice verifies.
- `callableAssign`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `fn`.
- `classKey`: {value: any, store: grow}; not certified: no slice of its own.
- `completes`: {value: any, store: grow}; not certified: its slice is unverified.
- `enumMemberName`: {value: any, store: grow}; not certified: no slice of its own.
- `firstOptional`: {value: any, store: grow}; certified: its slice verifies.
- `forInEntryReads`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.text`, `collect`, `declarations`, `statements`, `runsCodeOrWrites`, `writesName`, `writtenElement`.
- `freeOffsets`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.text`, `within`.
- `freshName`: {value: any, store: grow}; not certified: no slice of its own.
- `inKey`: {value: any, store: grow}; certified: its slice verifies.
- `jumpTarget`: {value: any, store: grow}; not certified: its slice is unverified.
- `literalExpr`: {value: any, store: grow}; certified: its slice verifies; calls `numberText`.
- `namesRead`: {value: any, store: grow}; not certified: its slice is unsupported.
- `parameterName`: {value: any, store: grow}; not certified: no slice of its own.
- `patternNames`: {value: any, store: grow}; certified: its slice verifies.
- `prototypeName`: {value: any, store: grow}; not certified: no slice of its own.
- `runsCode`: {value: any, store: grow}; certified: its slice verifies.
- `runsCodeOrWrites`: {value: any, store: grow}; certified: its slice verifies.
- `selfConstructs`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `token`, `runsCode`, `isStatic`, `members`.
- `selfName`: {value: any, store: grow}; not certified: no slice of its own.
- `skipParentheses`: {value: any, store: grow}; not certified: no slice of its own.
- `staticFieldOf`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `statements`, `members`.
- `staticMethodOf`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `statements`, `members`.
- `staticName`: {value: any, store: grow}; not certified: no slice of its own.
- `switchLabel`: {value: any, store: grow}; not certified: no slice of its own.
- `writesName`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `within`.
- `writtenElement`: {value: any, store: grow}; not certified: its slice is unverified.

### tools/intrinsics.mts

- `atom`: {value: any, store: grow}; not certified: no slice of its own; calls `Gate.span`.
- `enumMembersTerm`: states nothing; certified: its slice verifies; calls `Gate.span`, `literalTerm`, `members`.
- `fn`: {value: any, store: grow}; not certified: no slice of its own; calls `Gate.span`.
- `literalTerm`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`, `Gate.text`, `numberText`.
- `numberText`: {value: any, store: grow}; certified: its slice verifies.

### tools/syntax.mts

- `childOf`: {value: any, store: grow}; not certified: its slice is unsupported; calls `isNode`.
- `childrenOf`: {value: any, store: grow}; not certified: its slice is unsupported; calls `isNode`.
- `isNode`: states nothing (type predicate); not certified: no slice of its own.
- `isStatic`: {value: any, store: grow}; not certified: no slice of its own; calls `childrenOf`.
- `nameOf`: {value: any, store: grow}; not certified: no slice of its own; calls `childOf`.

### tools/type-term.mts

- `bigintText`: {value: any, store: grow}; certified: its slice verifies.
- `computedForm`: {value: any, store: grow}; certified: its slice verifies; calls `intersectionOperands`.
- `constructorForms`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `quantified`, `signatures`.
- `emptyObject`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`.
- `expandMapped`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `Gate.text`, `atom`, `emptyObject`, `members`, `numericKey`.
- `hostReceiver`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`.
- `indexKinds`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `typeTerm`.
- `intersection`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.span`, `computedForm`, `intersectionOperands`, `typeTerm`.
- `intersectionOperands`: {value: any, store: grow}; certified: its slice verifies; calls `unwrap`.
- `mapped`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.text`, `token`, `members`, `typeTerm`.
- `members`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `Gate.text`, `constructorForms`, `hostReceiver`, `indexKinds`, `oneTerm`, `propertyKey`, `quantified`, `sameIndex`, `signatures`, `spanOf`, `typeTerm`.
- `numericKey`: {value: any, store: grow}; certified: its slice verifies.
- `numericLexeme`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`.
- `oneTerm`: {value: any, store: grow}; not certified: its slice is unverified; calls `Gate.span`.
- `optionalTerm`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.span`.
- `ownedSlots`: {value: any, store: grow}; not certified: no slice of its own.
- `promiseOf`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `Gate.text`, `parameterName`, `spanOf`, `typeTerm`.
- `propertyKey`: {value: any, store: grow}; certified: its slice verifies; calls `Gate.text`, `numericKey`.
- `quantified`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `Gate.text`, `resolutionSlots`, `signatures`, `spanOf`, `typeTerm`.
- `readTypeTerm`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `Gate.text`, `atom`, `bigintText`, `computedForm`, `constructorForms`, `emptyObject`, `expandMapped`, `intersection`, `mapped`, `members`, `numericLexeme`, `oneTerm`, `quantified`, `signatures`, `spanOf`, `tuple`, `typeTerm`, `unwrap`.
- `resolutionSlots`: states nothing; certified: its slice verifies.
- `restPositions`: {value: any, store: grow}; certified: its slice verifies.
- `restRefusal`: {value: any, store: grow}; not certified: its slice is unverified.
- `restTerm`: {value: any, store: grow}; certified: its slice verifies.
- `sameIndex`: {value: any, store: grow}; not certified: its slice is unverified.
- `signatures`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `Gate.statedResult`, `Gate.text`, `pattern`, `firstOptional`, `optionalTerm`, `promiseOf`, `restPositions`, `restRefusal`, `restTerm`, `spanOf`, `statedEffect`, `statedResult`, `typeTerm`.
- `spanOf`: {value: any, store: grow}; not certified: no slice of its own.
- `statedEffect`: {value: any, store: grow}; not certified: no slice of its own.
- `statedResult`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `statementOf`, `unwrap`.
- `statementOf`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.text`, `members`, `unwrap`.
- `substitute`: {value: any, store: grow}; not certified: its slice is unsupported; calls `fn`, `signatures`.
- `tuple`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `tupleMember`, `typeTerm`.
- `tupleMember`: {value: any, store: grow}; certified: its slice verifies.
- `typeTerm`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `readTypeTerm`, `validateAnnotation`.
- `unwrap`: {value: any, store: grow}; not certified: no slice of its own.
- `validateAnnotation`: {value: any, store: grow}; not certified: its slice is unsupported; calls `Gate.fail`, `Gate.span`, `visitType`.
- `visitType`: {value: any, store: grow}; not certified: its slice is unsupported; calls `ownedSlots`, `signatures`.
