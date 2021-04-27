# Async checker

- yield-inside-async-function (E1700): disabled
- not-async-context-manager (E1701): disabled

# Basic checker

- init-is-generator (E0100): disabled
- return-in-init (E0101): good
- function-redefined (E0102): good
- not-in-loop (E0103): good
- return-outside-function (E0104): good
- yield-outside-function (E0105): disabled
- return-arg-in-generator (E0106): disabled
- nonexistent-operator (E0107): good
- duplicate-argument-name (E0108): good
- abstract-class-instantiated (E0110): disabled (though could enable if we used `abc.ABCMeta`)
- bad-reversed-sequence (E0111): good
- too-many-star-expressions (E0112): disabled
- invalid-star-assignment-target (E0113): disabled
- star-needs-assignment-target (E0114): disabled
- nonlocal-and-global (E0115): disabled
- continue-in-finally (E0116): disabled
- nonlocal-without-binding (E0117): disabled
- used-prior-global-declaration (E0118): disabled
- misplaced-format-function (E0119): improve message
- unreachable (W0101): good
- dangerous-default-value (W0102): good
- pointless-statement (W0104): good
- pointless-string-statement (W0105): *create*
- expression-not-assigned (W0106): good
- unnecessary-pass (W0107): good
- unnecessary-lambda (W0108): good
- duplicate-key (W0109): good
- assign-to-new-keyword (W0111): disabled
- useless-else-on-loop (W0120): disabled
- eval-used (W0123): good
- exec-used (W0122): good
- confusing-with-statement (W0124): good
- using-constant-test (W0125): disabled (superceded by E9902)
- missing-parentheses-for-call-in-test (W0126): good
- self-assigning-variable (W0127): good
- redeclared-assigned-name (W0128): *create*
- comparison-with-callable (W0143): improve message
- lost-exception (W0150): disabled
- nan-comparison (W0177): disabled
- assert-on-tuple (W0199): good
- literal-comparison (R0123): good
- comparison-with-itself (R0124): good
- invalid-name (C0103): good
- disallowed-name (C0104): good  (renamed from blacklisted-name in Pylint 2.8)
- empty-docstring (C0112): good
- missing-module-docstring (C0114): good
- missing-function-docstring (C0116): good
- missing-class-docstring (C0115): good
- singleton-comparison (C0121): good
- misplaced-comparison-constant (C0122): disabled
- unidiomatic-typecheck (C0123): good

## Classes checker

- access-member-before-definition (E0203): good
- method-hidden (E0202): good
- no-method-argument (E0211): good
- no-self-argument (E0213): good
- invalid-slots-object (E0236): disabled
- assigning-non-slot (E0237): disabled
- invalid-slots (E0238): disabled
- inherit-non-class (E0239): good
- inconsistent-mro (E0240): disabled
- duplicate-bases (E0241): good
- class-variable-slots-conflict (E0242): disabled
- non-iterator-returned (E0301): good
- unexpected-special-method-signature (E0302): good
- invalid-length-returned (E0303): good
- invalid-bool-returned (E0304): good
- invalid-index-returned (E0305): disabled
- invalid-repr-returned (E0306): good
- invalid-str-returned (E0307): good
- invalid-bytes-returned (E0308): disabled
- invalid-hash-returned (E0309): disabled
- invalid-length-hint-returned (E0310): disabled
- invalid-format-returned (E0311): disabled
- invalid-getnewargs-returned (E0312): disabled
- invalid-getnewargs-ex-returned (E0313): disabled
- attribute-defined-outside-init (W0201): good
- bad-staticmethod-argument (W0211): good
- protected-access (W0212): good
- no-init (W0232): disabled
- arguments-differ (W0221): good
- signature-differs (W0222): good
- abstract-method (W0223): good
- super-init-not-called (W0231): good
- non-parent-init-called (W0233): good
- useless-super-delegation (W0235): disabled
- invalid-overridden-method (W0236): disabled
- no-self-use (R0201): good
- no-classmethod-decorator (R0202): disabled
- no-staticmethod-decorator (R0203): disabled
- useless-object-inheritance (R0205): good
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
- too-many-branches (R0912): good
- too-many-arguments (R0913): good
- too-many-locals (R0914): good
- too-many-statements (R0915): good
- too-many-boolean-expressions (R0916): good

## Exceptions checker

- bad-except-order (E0701): good
- raising-bad-type (E0702): good
- bad-exception-context (E0703): disabled
- misplaced-bare-raise (E0704): good
- raise-missing-from (W0707): disabled
- raising-non-exception (E0710): good
- notimplemented-raised (E0711): good
- catching-non-exception (E0712): good
- bare-except (W0702): good
- broad-except (W0703): good
- duplicate-except (W0705): good
- try-except-raise (W0706): good
- binary-op-exception (W0711): good
- raising-format-tuple (W0715): good
- wrong-exception-operation (W0716): good

## Format checker

- unnecessary-semicolon (W0301): good
- bad-indentation (W0311): good
- ~~mixed-indentation (W0312): good~~ (removed in pylint 2.6)
- line-too-long (C0301): good
- too-many-lines (C0302): *create*
- trailing-whitespace (C0303): good
- missing-final-newline (C0304): good
- multiple-statements (C0321): good
- superfluous-parens (C0325): good
- ~~bad-whitespace (C0326): good~~ (removed in pylint 2.6)
- mixed-line-endings (C0327): disabled
- unexpected-line-ending-format (C0328): disabled
- ~~bad-continuation (C0330): good~~ (removed in pylint 2.6)

## Imports checker

- import-error (E0401): good
- relative-beyond-top-level (E0402): disabled
- wildcard-import (W0401): good
- deprecated-module (W0402): disabled
- reimported (W0404): good
- import-self (W0406): good
- preferred-module (W0407): disabled
- misplaced-future (W0410): good
- cyclic-import (R0401): *create*
- multiple-imports (C0410): good
- wrong-import-order (C0411): good
- ungrouped-imports (C0412): good
- wrong-import-position (C0413): good
- useless-import-alias (C0414): good
- import-outside-toplevel (C0415): *create*

## Logging checker

- logging-unsupported-format (E1200): disabled
- logging-format-truncated (E1201): disabled
- logging-too-many-args (E1205): disabled
- logging-too-few-args (E1206): disabled
- logging-not-lazy (W1201): disabled
- logging-format-interpolation (W1202): disabled

## Miscellaneous checker

- fixme (W0511): good
- use-symbolic-message-instead (I0023): disabled

## Newstyle checker

- bad-super-call (E1003): good

## Refactoring checker

- consider-merging-isinstance (R1701): good
- too-many-nested-blocks (R1702): good
- simplifiable-if-statement (R1703): disabled
- redefined-argument-from-local (R1704): good
- no-else-return (R1705): good
- consider-using-ternary (R1706): disabled
- trailing-comma-tuple (R1707): good
- stop-iteration-return (R1708): disabled
- simplify-boolean-expression (R1709): disabled
- inconsistent-return-statements (R1710): good
- useless-return (R1711): disabled
- consider-swap-variables (R1712): good
- consider-using-join (R1713): good
- consider-using-in (R1714): good
- consider-using-get (R1715): good
- chained-comparison (R1716): good
- consider-using-dict-comprehension (R1717): disabled
- consider-using-set-comprehension (R1718): disabled
- simplifiable-if-expression (R1719): disabled
- consider-using-sys-exit (R1722): disabled
- no-else-raise (R1720): good
- unnecessary-comprehension (R1721): improve message
- no-else-break (R1723): good
- no-else-continue (R1724): good
- super-with-arguments (R1725): *create*
- simplifiable-condition (R1726): *create*
- condition-evals-to-constant (R1727): *create*
- consider-using-generator (R1728): disabled
- consider-using-min-builtin (R1730): disabled
- consider-using-max-builtin (R1731): disabled
- consider-using-with (R1732): *create*
- unneeded-not (C0113): good
- consider-using-enumerate (C0200): good
- consider-iterating-dictionary (C0201): good
- len-as-condition (C1801): good

## Stdlib checker

- invalid-envvar-value (E1507): disabled
- bad-open-mode (W1501): good
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
- bad-string-format-type (E1307): good
- bad-str-strip-call (E1310): good
- bad-format-string-key (W1300): disabled
- unused-format-string-key (W1301): *create*
- bad-format-string (W1302): disabled
- missing-format-argument-key (W1303): good
- unused-format-string-argument (W1304): good
- missing-format-attribute (W1306): disabled
- invalid-format-index (W1307): disabled
- f-string-without-interpolation (W1309): good
- implicit-str-concat (W1404): good
- format-combined-specification (W1305): good
- duplicate-string-formatting-argument (W1308): good
- anomalous-backslash-in-string (W1401): good
- anomalous-unicode-escape-in-string (W1402): good

# Typecheck checker

- no-member (E1101): good
- not-callable (E1102): good
- assignment-from-no-return (E1111): good
- no-value-for-parameter (E1120): good
- too-many-function-args (E1121): good
- unexpected-keyword-arg (E1123): good
- redundant-keyword-arg (E1124): disabled
- missing-kwoa (E1125): disabled
- invalid-sequence-index (E1126): good
- invalid-slice-index (E1127): good
- assignment-from-none (E1128): good
- not-context-manager (E1129): good
- invalid-unary-operand-type (E1130): good (note: message missing in Pylint docs, could submit PR)
- unsupported-binary-operation (E1131): good (same note as previous)
- unsupported-assignment-operation (E1137): good
- repeated-keyword (E1132): disabled
- not-an-iterable (E1133): good
- not-a-mapping (E1134): *create*
- unsupported-membership-test (E1135): good
- unsubscriptable-object (E1136): good
- unsupported-delete-operation (E1138): good
- invalid-metaclass (E1139): disabled
- unhashable-dict-key (E1140): good
- dict-iter-missing-items (E1141): good
- keyword-arg-before-vararg (W1113): disabled
- arguments-out-of-order (W1114): good
- non-str-assignment-to-dunder-name (W1115): disabled
- c-extension-no-member (I1101): disabled

## Variables checker

- used-before-assignment (E0601): good
- undefined-variable (E0602): good
- undefined-all-variable (E0603): disabled
- invalid-all-object (E0604): disabled
- no-name-in-module (E0611): good
- unpacking-non-sequence (E0633): good
- global-variable-undefined (W0601): disabled
- global-variable-not-assigned (W0602): disabled
- global-statement (W0603): good
- global-at-module-level (W0604): good
- unused-import (W0611): good
- unused-variable (W0612): good
- unused-argument (W0613): good
- unused-wildcard-import (W0614): disabled
- redefined-outer-name (W0621): good
- redefined-builtin (W0622): good
- redefine-in-handler (W0623): *create*
- undefined-loop-variable (W0631): good
- unbalanced-tuple-unpacking (W0632): good
- cell-var-from-loop (W0640): disabled
- possibly-unused-variable (W0641): improve message (but investigate relationship with E9969)
- self-cls-assignment (W0642): good
