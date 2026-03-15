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

(include-book "test-star")
(include-book "pure-expression-execution")

(local (include-book "kestrel/utilities/nfix" :dir :system))

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection exec-stmt-openers
  :parents (proof-support)
  :short "Opener rules for @(tsee exec-stmt)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide rules for different kinds of statements.
     For @('if') and @('if')-@('else'),
     we provide both splitting rules (i.e. which produce @(tsee if)s)
     and non-splitting rules.
     The non-splitting rules use the @(tsee test*) wrapper for the tests,
     which can be enabled if desired;
     see @(tsee test*) for its rationale.
     Perhaps the splitting rules should use that as well.")
   (xdoc::p
    "All the rules have @(tsee syntaxp) hypotheses saying that
     the ASTs (for test and body) being executed are quoted constants.
     Thus, the rules are suitable for symbolic execution of concrete code.")
   (xdoc::p
    "We provide a ruleset with all the rules,
     and two rulesets for splitting vs. non-splitting rules.")
   (xdoc::p
    "Currently the rules for @('if') and @('if')-@('else')
     are limited to tests that are pure expressions.
     Also, some kinds of statements have no rules yet."))

  (defruled exec-stmt-when-compound
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :compound)
                  (not (zp limit))
                  (equal sval+compst1
                         (exec-block-item-list (stmt-compound->items s)
                                               (enter-scope compst)
                                               fenv
                                               (1- limit)))
                  (equal sval (mv-nth 0 sval+compst1))
                  (equal compst1 (mv-nth 1 sval+compst1))
                  (stmt-valuep sval))
             (equal (exec-stmt s compst fenv limit)
                    (mv sval (exit-scope compst1))))
    :enable (exec-stmt
             not-errorp-when-expr-value-optionp))

  (defruled exec-stmt-when-expr
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :expr)
                  (not (zp limit))
                  (equal eval?+compst1
                         (exec-expr (stmt-expr->get s) compst fenv (1- limit)))
                  (equal eval? (mv-nth 0 eval?+compst1))
                  (equal compst1 (mv-nth 1 eval?+compst1))
                  (expr-value-optionp eval?))
             (equal (exec-stmt s compst fenv limit)
                    (mv (stmt-value-none) compst1)))
    :enable (exec-stmt
             not-errorp-when-expr-value-optionp))

  (defruled exec-stmt-when-if
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :if)
                  (expr-purep (stmt-if->test s))
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit (stmt-if->test s))))
                  (compustatep compst)
                  (equal arg1 (exec-expr-pure (stmt-if->test s) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test))
             (equal (exec-stmt s compst fenv limit)
                    (if test
                        (exec-stmt (stmt-if->then s) compst fenv (1- limit))
                      (mv (stmt-value-none) compst))))
    :enable (exec-stmt
             exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-value-optionp))

  (defruled exec-stmt-when-if-and-true
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :if)
                  (expr-purep (stmt-if->test s))
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit (stmt-if->test s))))
                  (compustatep compst)
                  (equal arg1 (exec-expr-pure (stmt-if->test s) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test)
                  (test* test))
             (equal (exec-stmt s compst fenv limit)
                    (exec-stmt (stmt-if->then s) compst fenv (1- limit))))
    :enable (exec-stmt
             exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-value-optionp
             test*))

  (defruled exec-stmt-when-if-and-false
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :if)
                  (expr-purep (stmt-if->test s))
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit (stmt-if->test s))))
                  (compustatep compst)
                  (equal arg1 (exec-expr-pure (stmt-if->test s) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test)
                  (test* (not test)))
             (equal (exec-stmt s compst fenv limit)
                    (mv (stmt-value-none) compst)))
    :enable (exec-stmt
             exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-value-optionp
             test*))

  (defruled exec-stmt-when-ifelse
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :ifelse)
                  (expr-purep (stmt-ifelse->test s))
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit (stmt-ifelse->test s))))
                  (equal arg1 (exec-expr-pure (stmt-ifelse->test s) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test))
             (equal (exec-stmt s compst fenv limit)
                    (if test
                        (exec-stmt
                         (stmt-ifelse->then s) compst fenv (1- limit))
                      (exec-stmt
                       (stmt-ifelse->else s) compst fenv (1- limit)))))
    :expand (exec-stmt s compst fenv limit)
    :enable (exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-value-optionp))

  (defruled exec-stmt-when-ifelse-and-true
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :ifelse)
                  (expr-purep (stmt-ifelse->test s))
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit (stmt-ifelse->test s))))
                  (equal arg1 (exec-expr-pure (stmt-ifelse->test s) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test)
                  (test* test))
             (equal (exec-stmt s compst fenv limit)
                    (exec-stmt (stmt-ifelse->then s) compst fenv (1- limit))))
    :expand (exec-stmt s compst fenv limit)
    :enable (exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-value-optionp
             test*))

  (defruled exec-stmt-when-ifelse-and-false
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :ifelse)
                  (expr-purep (stmt-ifelse->test s))
                  (integerp limit)
                  (>= limit (1+ (expr-pure-limit (stmt-ifelse->test s))))
                  (equal arg1 (exec-expr-pure (stmt-ifelse->test s) compst))
                  (expr-valuep arg1)
                  (equal carg1 (apconvert-expr-value arg1))
                  (expr-valuep carg1)
                  (equal test (test-value (expr-value->value carg1)))
                  (booleanp test)
                  (test* (not test)))
             (equal (exec-stmt s compst fenv limit)
                    (exec-stmt (stmt-ifelse->else s) compst fenv (1- limit))))
    :expand (exec-stmt s compst fenv limit)
    :enable (exec-stmt
             exec-expr-to-exec-expr-pure-when-expr-pure-limit
             not-errorp-when-expr-value-optionp
             test*))

  (defruled exec-stmt-when-while
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :while)
                  (not (zp limit)))
             (equal (exec-stmt s compst fenv limit)
                    (exec-stmt-while (stmt-while->test s)
                                     (stmt-while->body s)
                                     compst
                                     fenv
                                     (1- limit))))
    :enable exec-stmt)

  (defruled exec-stmt-when-return
    (implies (and (syntaxp (quotep s))
                  (equal (stmt-kind s) :return)
                  (not (zp limit))
                  (equal e (stmt-return->value s))
                  e
                  (equal eval+compst1
                         (exec-expr e compst fenv (1- limit)))
                  (equal eval (mv-nth 0 eval+compst1))
                  (equal compst1 (mv-nth 1 eval+compst1))
                  (expr-valuep eval)
                  (equal eval1 (apconvert-expr-value eval))
                  (expr-valuep eval1)
                  (equal val (expr-value->value eval1)))
             (equal (exec-stmt s compst fenv limit)
                    (mv (stmt-value-return val) compst1)))
    :enable (exec-stmt
             not-errorp-when-expr-value-optionp)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *exec-stmt-openers*
  :parents (exec-stmt-openers)
  :short "List of opener rules for @(tsee exec-stmt)."
  '(exec-stmt-when-compound
    exec-stmt-when-expr
    exec-stmt-when-if
    exec-stmt-when-if-and-true
    exec-stmt-when-if-and-false
    exec-stmt-when-ifelse
    exec-stmt-when-ifelse-and-true
    exec-stmt-when-ifelse-and-false
    exec-stmt-when-while
    exec-stmt-when-return))

(defval *exec-stmt-openers-split*
  :parents (exec-stmt-openers)
  :short "List of opener rules for @(tsee exec-stmt)
          that cause splits at conditionals."
  '(exec-stmt-when-compound
    exec-stmt-when-expr
    exec-stmt-when-if
    exec-stmt-when-ifelse
    exec-stmt-when-while
    exec-stmt-when-return))

(defval *exec-stmt-openers-nosplit*
  :parents (exec-stmt-openers)
  :short "List of opener rules for @(tsee exec-stmt)
          that do not cause splits at conditionals."
  '(exec-stmt-when-compound
    exec-stmt-when-expr
    exec-stmt-when-if-and-true
    exec-stmt-when-if-and-false
    exec-stmt-when-ifelse-and-true
    exec-stmt-when-ifelse-and-false
    exec-stmt-when-while
    exec-stmt-when-return))

;;;;;;;;;;;;;;;;;;;;

(make-event
 `(def-ruleset exec-stmt-openers
    ',*exec-stmt-openers*))

(make-event
 `(def-ruleset exec-stmt-openers-split
    ',*exec-stmt-openers-split*))

(make-event
 `(def-ruleset exec-stmt-openers-nosplit
    ',*exec-stmt-openers-nosplit*))
