; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (mccarthy@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "language/parse-yul-file")

;; The files under "yulOptimizerTests" initially came from
;;   https://github.com/ethereum/solidity/tree/develop/test/libyul/yulOptimizerTests/
;; which contains 542 .yul files.
;; (as of branch: develop; commit: c3b4292d1).
;; Then some files were removed, due to i32 type:
;;   conditionalSimplifier/add_correct_type_wasm.yul
;;   expressionSplitter/typed.yul
;; and due to Yul object notation:
;;   commonSubexpressionEliminator/object_access.yul
;;   expressionSplitter/object_access.yul
;; Leaving 538 files.
;; Also removed all :bool and :u256 type annotations, since type annotations are
;; not currently in the officially documented Yul grammar.
;; Then ran awk to extract the "after optimization" expected yul programs
;; into *.yul.expected as in this command:
;;   cd yulOptimizerTests ; awk -f ../uncomment-expected.awk */*.yul
;; for a total of 538 * 2 = 1076 files.

;; Of those processed files, 80 files in 5 directories are checked in
;; here under yulOptimizerTests/ :
;;   deadCodeEliminator
;;   disambiguator
;;   forLoopInitRewriter
;;   functionGrouper
;;   functionHoister
;; Note, we can check in a few more as needed for optimizer verification work,
;; but we probably do not want to eagerly check much more in here,
;; since it would be better to resolve the type issue and yul object notation
;; and to drive the tests directly from the solidity repo.
