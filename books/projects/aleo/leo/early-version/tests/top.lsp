; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "projects/aleo/leo/portcullis" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)
(include-book "std/util/defconsts" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)

; 2022-10-16 EricM: this file doesn't work now because it talks about
; canonicalization.  Temporarily remove it:
; (include-book "proof-gen")

;; It would be good to automate running tgc on the minimal tests,
;; but one issue is that the json file generation is not automated
;; and in fact the json files need to be checked in or they will be
;; useless for investigating regressions in Leo.
;; For regression tests of leo-acl2 tgc now we have:
;; (1) "proof-gen" (mentioned above);
;; (2) Forms that can be evaluated in the ACL2 REPL, see minimal/README.md; and
;; (3) this instance of type-inference theorem (compiler_array_complex_access).
;; For more coverage on regression tests, we have tgc CI tests in the leo repo.
;;
; 2022-10-16 EricM: this file doesn't work now, temporarily remove:
;(include-book "minimal/compiler_array_complex_access/outputs/type-inference-theorem")


;; Moved from leo-acl2/examples.lisp
; 2022-10-16 EricM: this file doesn't work now, temporarily remove:
; (include-book "ast-build-examples")

;; TODO: this used big-step-execution which no longer exists.
;;       Find the replacement and bring it back.
;(include-book "execution/tests")


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ tests
  :parents (leo)
  :short "Test cases for Formal Model of Leo."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is work in progress.  Additional tests will be added."))
  :order-subtopics t)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Dynamic Execution test cases
;; TODO: move each class of test cases to separate file(s).

;; Goal: for each Leo compiler test that can be executed,
;;       we would like to have at least one i/o pair.
;;       The idea is that this can validate the formal specifications and catch
;;       certain kinds of mistakes quickly.

;; Issues:
;; * most of the compiler tests are not executable since they are must `main` with a console.assert()
;; * most of the tests don't have interesting return values---usually just checks if some function
;;   on the inputs is true
;; * there is not very good coverage

;; TODO:
;; * add must-fail tests along with ways to report errors
;; * broaden evaluator to handle other functions than main

;; NOTE: Due to the above issues, the following are contrived test cases
;; NOT taken from any  official Leo compiler test suite.

;; TODO: organize test cases better.  Maybe want something other than defconst, that takes xdoc.


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The root tests directory contains the current file.

(defconsts *tests-dir* (cbd))  ; this puts a slash on the end.
