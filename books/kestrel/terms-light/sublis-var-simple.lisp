; Utilities that perform substitution
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See tests in sublis-var-simple-tests.lisp.
;; See proofs in sublis-var-simple-proofs.lisp.

;; See also the built-in function sublis-var.  It evaluates ground applications of certain functions:
;; (sublis-var (acons 'a ''3 nil) '(binary-+ a a)) = '6
;; It does not resolve IFs when the test is a constant:
;; (sublis-var (acons 'a ''3 nil) '(if (equal '3 a) x y)) = (IF 'T X Y)

;; See also Axe functions like sublis-var-and-eval-basic, which can evaluate
;; certain ground function applications and simplify IFs with constant tests.

;; Apply ALIST to replace free variables in TERM.  Free variables not bound in ALIST are left alone.
;; This function is simpler than sublis-var and, unlike sublis-var, doesn't evaluate functions applied to constant arguments.
;; TODO: Consider simplifying IFs whose tests are constants (i.e., don't build both branches of such an IF).
(mutual-recursion
 (defund sublis-var-simple (alist term)
   (declare (xargs :guard (and (symbol-alistp alist) ; usually a symbol-term-alistp
                               (pseudo-termp term))
                   :measure (acl2-count term)))
   (cond ((variablep term)
          (let ((res (assoc-eq term alist)))
            (if res (cdr res) term)))
         ((fquotep term) term)
         (t (cons-with-hint
             ;; Since lambdas are closed, we don't have to do anything to the lambda body:
             (ffn-symb term)
             (sublis-var-simple-lst alist (fargs term))
             term))))

 (defund sublis-var-simple-lst (alist terms)
   (declare (xargs :measure (acl2-count terms)
                   :guard (and (symbol-alistp alist)
                               (pseudo-term-listp terms))))
   (if (endp terms)
       nil
     (cons-with-hint (sublis-var-simple alist (car terms))
                     (sublis-var-simple-lst alist (cdr terms))
                     terms))))
