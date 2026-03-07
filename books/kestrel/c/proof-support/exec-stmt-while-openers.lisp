; C Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
; Copyright (C) 2026 Kestrel Technology LLC (http://kestreltechnology.com)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "C")

(include-book "pure-expression-execution")

(local (include-book "kestrel/utilities/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-stmt-while-openers
  :parents (proof-support)
  :short "Opener rules for @(tsee exec-stmt-while)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide rules for three cases:
     the test is false and the loop terminates;
     the test is true but the body returns (so the loop terminates);
     the test is true and the body does not return,
     so the loop is repeated (in the updated state).
     The third rule can be used when unrolling a loop.")
   (xdoc::p
    "All the rules have @(tsee syntaxp) hypotheses saying that
     the ASTs (for test and body) being executed are quoted constants.
     Thus, the rules are suitable for symbolic execution of concrete code.")
   (xdoc::p
    "Currently these rules are limited to
     loops whose test expressions are pure."))

  (defruled exec-stmt-while-when-false
    (implies (and (syntaxp (and (quotep test)
                                (quotep body)))
                  (expr-purep test)
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit test)))
                  (compustatep compst)
                  (equal eval (exec-expr-pure test compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal val (expr-value->value eval1))
                  (equal continuep (test-value val))
                  (booleanp continuep)
                  (not continuep))
             (equal (exec-stmt-while test body compst fenv limit)
                    (mv (stmt-value-none) compst)))
    :enable (exec-stmt-while
             exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-valuep))

  (defruled exec-stmt-while-when-true-return
    (implies (and (syntaxp (and (quotep test)
                                (quotep body)))
                  (expr-purep test)
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit test)))
                  (compustatep compst)
                  (equal eval (exec-expr-pure test compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal val (expr-value->value eval1))
                  (equal continuep (test-value val))
                  (booleanp continuep)
                  continuep
                  (equal sval+compst1 (exec-stmt body compst fenv (1- limit)))
                  (equal sval (mv-nth 0 sval+compst1))
                  (equal compst1 (mv-nth 1 sval+compst1))
                  (stmt-valuep sval)
                  (equal (stmt-value-kind sval) :return))
             (equal (exec-stmt-while test body compst fenv limit)
                    (mv sval compst1)))
    :enable (exec-stmt-while
             exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-valuep))

  (defruled exec-stmt-while-when-true-noreturn
    (implies (and (syntaxp (and (quotep test)
                                (quotep body)))
                  (expr-purep test)
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit test)))
                  (compustatep compst)
                  (equal eval (exec-expr-pure test compst))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal val (expr-value->value eval1))
                  (equal continuep (test-value val))
                  (booleanp continuep)
                  continuep
                  (equal sval+compst1 (exec-stmt body compst fenv (1- limit)))
                  (equal sval (mv-nth 0 sval+compst1))
                  (equal compst1 (mv-nth 1 sval+compst1))
                  (stmt-valuep sval)
                  (not (equal (stmt-value-kind sval) :return)))
             (equal (exec-stmt-while test body compst fenv limit)
                    (exec-stmt-while test body compst1 fenv (1- limit))))
    :enable (exec-stmt-while
             exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-valuep
             not-errorp-when-stmt-valuep)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *exec-stmt-while-openers*
  :parents (exec-stmt-while-openers)
  :short "List of opener rules for @(tsee exec-stmt-while)."
  '(exec-stmt-while-when-false
    exec-stmt-while-when-true-return
    exec-stmt-while-when-true-noreturn))

;;;;;;;;;;;;;;;;;;;;

(make-event
 `(def-ruleset exec-stmt-while-openers
    ',*exec-stmt-while-openers*))
