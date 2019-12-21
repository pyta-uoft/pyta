# Async checker

- yield-inside-async-function (E1700): disabled
- not-async-context-manager (E1701): disabled

# Basic checker

- init-is-generator (E0100): disabled
- return-in-init (E0101): improve message
- function-redefined (E0102): improve message
- not-in-loop (E0103): improve message
- return-outside-function (E0104): improve message
- yield-outside-function (E0105): disabled
- return-arg-in-generator (E0106): disabled
- nonexistent-operator (E0107): good
- duplicate-argument-name (E0108): improve message (argument -> parameter)
- abstract-class-instantiated (E0110): disabled (though could enable if we used `abc.ABCMeta`)
- bad-reversed-sequence (E0111): *create*
- too-many-star-expressions (E0112): disabled
- invalid-star-assignment-target (E0113): disabled
- star-needs-assignment-target (E0114): disabled
- nonlocal-and-global (E0115): disabled
- continue-in-finally (E0116): disabled
- nonlocal-without-binding (E0117): disabled
- used-prior-global-declaration (E0118): disabled
- misplaced-format-function (E0119): *create*
- unreachable (W0101): improve message
- dangerous-default-value (W0102): improve message
- pointless-statement (W0104): improve message
- pointless-string-statement (W0105): *create*
- expression-not-assigned (W0106): improve message
- unnecessary-pass (W0107): improve message
- unnecessary-lambda (W0108): *create*
- duplicate-key (W0109): improve message
- assign-to-new-keyword (W0111): disabled
- useless-else-on-loop (W0120): disabled
- eval-used (W0123): *create*
- exec-used (W0122): *create*
- confusing-with-statement (W0124): *create*
- using-constant-test (W0125): disabled (superceded by E9902)
- missing-parentheses-for-call-in-test (W0126): *create*
- self-assigning-variable (W0127): *create*
- redeclared-assigned-name (W0128): *create*
- comparison-with-callable (W0143): *create*
- lost-exception (W0150): disabled
- assert-on-tuple (W0199): improve message
- literal-comparison (R0123): improve message
- comparison-with-itself (R0124): *create*
- blacklisted-name (C0102): improve message
- invalid-name (C0103): improve message
- empty-docstring (C0112): good
- missing-module-docstring (C0114): *create*
- missing-function-docstring (C0116): *create*
- missing-class-docstring (C0115): *create*
- singleton-comparison (C0121): good
- misplaced-comparison-constant (C0122): disabled
- unidiomatic-typecheck (C0123):

## Classes checker

- access-member-before-definition (E0203): improve message (member -> attribute)
- method-hidden (E0202): good
- no-method-argument (E0211): improve message
- no-self-argument (E0213): improve message
- invalid-slots-object (E0236): disabled
- assigning-non-slot (E0237): disabled
- invalid-slots (E0238): disabled
- inherit-non-class (E0239): good
- inconsistent-mro (E0240): disabled
- duplicate-bases (E0241): improve message
- class-variable-slots-conflict (E0242): disabled
- non-iterator-returned (E0301): *create*
- unexpected-special-method-signature (E0302): improve message
- invalid-length-returned (E0303): *create*
- invalid-bool-returned (E0304): *create*
- invalid-index-returned (E0305): disabled
- invalid-repr-returned (E0306): *create*
- invalid-str-returned (E0307): *create*
- invalid-bytes-returned (E0308): disabled
- invalid-hash-returned (E0309): disabled
- invalid-length-hint-returned (E0310): disabled
- invalid-format-returned (E0311): disabled
- invalid-getnewargs-returned (E0312): disabled
- invalid-getnewargs-ex-returned (E0313): disabled
- attribute-defined-outside-init (W0201): good
- bad-staticmethod-argument (W0211): create
- protected-access (W0212): improve message
- no-init (W0232): disabled
- arguments-differ (W0221): improve message
- signature-differs (W0222): improve message
- abstract-method (W0223): improve message
- super-init-not-called (W0231): *create* (maybe? if not, add to disable)
- non-parent-init-called (W0233): improve message
- useless-super-delegation (W0235): disabled
- invalid-overridden-method (W0236): disabled
- no-self-use (R0201): improve message
- no-classmethod-decorator (R0202): disabled
- no-staticmethod-decorator (R0203): disabled
- useless-object-inheritance (R0205): *create*
- property-with-parameters (R0206): disabled
- bad-classmethod-argument (C0202): disabled
- bad-mcs-method-argument (C0203): disabled
- bad-mcs-classmethod-argument (C0204): disabled
- single-string-used-for-slots (C0205): disabled
- method-check-failed (F0202): disabled

## Design checker

- too-many-ancestors (R0901): disabled
- too-many-instance-attributes (R0902): good
- too-few-public-methods (R0903): disabled
- too-many-public-methods (R0904): disabled
- too-many-return-statements (R0911): disabled
- too-many-branches (R0912): *create*
- too-many-arguments (R0913): improve message (arguments -> parameter)
- too-many-locals (R0914): improve message
- too-many-statements (R0915): improve message
- too-many-boolean-expressions (R0916): *create*

## Exceptions checker

- bad-except-order (E0701): improve message
- raising-bad-type (E0702): improve message
- bad-exception-context (E0703): disabled
- misplaced-bare-raise (E0704): improve message
- raising-non-exception (E0710): improve message
- notimplemented-raised (E0711): improve message
- catching-non-exception (E0712): improve message
- bare-except (W0702): improve message
- broad-except (W0703): improve message
- duplicate-except (W0705): improve message
- try-except-raise (W0706): *create*
- binary-op-exception (W0711): improve message
- raising-format-tuple (W0715): *create*
- wrong-exception-operation (W0716): *create*

## Format checker

- unnecessary-semicolon (W0301): improve message
- bad-indentation (W0311): good
- mixed-indentation (W0312): improve message
- line-too-long (C0301): improve message
- too-many-lines (C0302): improve message
- trailing-whitespace (C0303): improve message
- missing-final-newline (C0304): improve message
- multiple-statements (C0321): improve message
- superfluous-parens (C0325): good
- bad-whitespace (C0326): good
- mixed-line-endings (C0327): disabled
- unexpected-line-ending-format (C0328): disabled
- bad-continuation (C0330): improve message

## Imports checker

- import-error (E0401): improve message
- relative-beyond-top-level (E0402): disabled
- wildcard-import (W0401): improve message
- deprecated-module (W0402): disabled
- reimported (W0404): improve message
- import-self (W0406): good
- preferred-module (W0407): disabled
- misplaced-future (W0410): *create*
- cyclic-import (R0401): *create*
- multiple-imports (C0410): improve message
- wrong-import-order (C0411): good
- ungrouped-imports (C0412): good
- wrong-import-position (C0413): good
- useless-import-alias (C0414): *create*
- import-outside-toplevel (C0415): *create*

## Logging checker

- logging-unsupported-format (E1200): disabled
- logging-format-truncated (E1201): disabled
- logging-too-many-args (E1205): disabled
- logging-too-few-args (E1206): disabled
- logging-not-lazy (W1201): disabled
- logging-format-interpolation (W1202): disabled

## Miscellaneous checker

- fixme (W0511): *create*
- use-symbolic-message-instead (I0023): disabled

## Newstyle checker

- bad-super-call (E1003): *create*

## Refactoring checker

- consider-merging-isinstance (R1701): *create*
- too-many-nested-blocks (R1702): improve message
- simplifiable-if-statement (R1703): disabled
- redefined-argument-from-local (R1704): improve message (argument -> parameter)
- no-else-return (R1705): *create*
- consider-using-ternary (R1706): disabled
- trailing-comma-tuple (R1707): improve message
- stop-iteration-return (R1708): disabled
- simplify-boolean-expression (R1709): disabled
- inconsistent-return-statements (R1710): good
- useless-return (R1711): disabled
- consider-swap-variables (R1712): *create*
- consider-using-join (R1713): *create*
- consider-using-in (R1714): *create*
- consider-using-get (R1715): *create*
- chained-comparison (R1716): *create*
- consider-using-dict-comprehension (R1717): disabled
- consider-using-set-comprehension (R1718): disabled
- simplifiable-if-expression (R1719): disabled
- consider-using-sys-exit (R1722): disabled
- no-else-raise (R1720): *create*
- unnecessary-comprehension (R1721): *create*
- no-else-break (R1723): *create*
- no-else-continue (R1724): *create*
- unneeded-not (C0113): improve message
- consider-using-enumerate (C0200): *create*
- consider-iterating-dictionary (C0201): improve message
- len-as-condition (C1801): *create*

## Stdlib checker

- invalid-envvar-value (E1507): disabled
- bad-open-mode (W1501): *create*
- boolean-datetime (W1502): disabled
- redundant-unittest-assert (W1503): disabled
- deprecated-method (W1505): disabled
- bad-thread-instantiation (W1506): disabled
- shallow-copy-environ (W1507): disabled
- invalid-envvar-default (W1508): disabled
- subprocess-popen-preexec-fn (W1509): disabled
- subprocess-run-check (W1510): disabled

## String checker

- bad-format-character (E1300): disabled
- truncated-format-string (E1301): disabled
- mixed-format-string (E1302): disabled
- format-needs-mapping (E1303): disabled
- missing-format-string-key (E1304): disabled
- too-many-format-args (E1305): good
- too-few-format-args (E1306): good
- bad-string-format-type (E1307): *create*
- bad-str-strip-call (E1310): improve message
- bad-format-string-key (W1300): disabled
- unused-format-string-key (W1301): *create*
- bad-format-string (W1302): disabled
- missing-format-argument-key (W1303): good
- unused-format-string-argument (W1304): *create*
- missing-format-attribute (W1306): disabled
- invalid-format-index (W1307): disabled
- f-string-without-interpolation (W1309): *create*
- implicit-str-concat (W1404): *create*
- format-combined-specification (W1305): good
- duplicate-string-formatting-argument (W1308): *create*
- anomalous-backslash-in-string (W1401): improve message
- anomalous-unicode-escape-in-string (W1402): *create*

# Typecheck checker

- no-member (E1101): improve message
- not-callable (E1102): improve message
- assignment-from-no-return (E1111): good
- no-value-for-parameter (E1120): good
- too-many-function-args (E1121): good
- unexpected-keyword-arg (E1123): good
- redundant-keyword-arg (E1124): disabled
- missing-kwoa (E1125): disabled
- invalid-sequence-index (E1126): improve message
- invalid-slice-index (E1127): improve message
- assignment-from-none (E1128): good
- not-context-manager (E1129): *create*
- invalid-unary-operand-type (E1130): improve message (note: message missing in Pylint docs, could submit PR)
- unsupported-binary-operation (E1131): improve message (same note as previous)unsupported-assignment-operation (E1137): good
- repeated-keyword (E1132): disabled
- not-an-iterable (E1133): improve message
- not-a-mapping (E1134): *create*
- unsupported-membership-test (E1135): good
- unsubscriptable-object (E1136): improve message
- unsupported-delete-operation (E1138): good
- invalid-metaclass (E1139): disabled
- unhashable-dict-key (E1140): *create*
- dict-iter-missing-items (E1141): *create*
- keyword-arg-before-vararg (W1113): disabled
- arguments-out-of-order (W1114): *create*
- non-str-assignment-to-dunder-name (W1115): disabled
- c-extension-no-member (I1101): disabled

## Variables checker

- used-before-assignment (E0601): improve message
- undefined-variable (E0602): good
- undefined-all-variable (E0603): disabled
- invalid-all-object (E0604): disabled
- no-name-in-module (E0611): improve message
- unpacking-non-sequence (E0633): improve message
- global-variable-undefined (W0601): disabled
- global-variable-not-assigned (W0602): disabled
- global-statement (W0603): *create*
- global-at-module-level (W0604): *create*
- unused-import (W0611): improve message
- unused-variable (W0612): improve message
- unused-argument (W0613): improve message
- unused-wildcard-import (W0614): disabled
- redefined-outer-name (W0621): improve message
- redefined-builtin (W0622): improve message
- redefine-in-handler (W0623): *create*
- undefined-loop-variable (W0631): improve message
- unbalanced-tuple-unpacking (W0632): *create*
- cell-var-from-loop (W0640): disabled
- possibly-unused-variable (W0641): *create* (but investigate relationship with E9969)
- self-cls-assignment (W0642): *create*
