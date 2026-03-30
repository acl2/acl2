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

(acl2::controlled-configuration)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ exec-expr-pure-list-openers
  :parents (proof-support)
  :short "Opener rules for @(tsee exec-expr-pure-list)."
  :long
  (xdoc::topstring
   (xdoc::p
    "We provide rules for empty and non-empty lists.")
   (xdoc::p
    "We provide a ruleset for the rules."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-list-of-nil
  :short "Opener rule for empty lists of expressions."
  (equal (exec-expr-pure-list nil compst)
         nil)
  :enable exec-expr-pure-list)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defruled exec-expr-pure-list-when-consp
  :short "Opener rule for non-empty lists of expressions."
  (implies (and (syntaxp (quotep es))
                (consp es)
                (equal eval (exec-expr-pure (car es) compst))
                (expr-valuep eval)
                (equal eval1 (apconvert-expr-value eval))
                (expr-valuep eval1)
                (equal val (expr-value->value eval1))
                (equal vals (exec-expr-pure-list (cdr es) compst))
                (value-listp vals))
           (equal (exec-expr-pure-list es compst)
                  (cons val vals)))
  :enable (exec-expr-pure-list (:e tau-system)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defval *exec-expr-pure-list-openers*
  :short "List of opener rules for @(tsee exec-expr-pure-list)."
  '(exec-expr-pure-list-of-nil
    exec-expr-pure-list-when-consp))

;;;;;;;;;;;;;;;;;;;;

(make-event
 `(def-ruleset exec-expr-pure-list-openers
    ',*exec-expr-pure-list-openers*))
