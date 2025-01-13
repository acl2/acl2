; Utilities for expanding lambdas
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also the proofs in expand-lambdas-in-term-proof.lisp.

(include-book "sublis-var-simple")
(include-book "lambda-free-termp")
(include-book "lambdas-closed-in-termp")
(local (include-book "sublis-var-simple-proofs"))
(local (include-book "../alists-light/pairlis-dollar"))
(local (include-book "../lists-light/subsetp-equal"))
(local (include-book "../typed-lists-light/symbol-listp"))

;; Some of these could be moved to more general libraries:

;; Substitution doesn't introduce lambdas if there were none to start with and
;; there are none in the alist being used for substitution.
(defthm-flag-sublis-var-simple
  (defthm lambda-free-termp-of-sublis-var-simple
    (implies (and (lambda-free-termp term)
                  (lambda-free-termsp (strip-cdrs alist)))
             (lambda-free-termp (sublis-var-simple alist term)))
    :flag sublis-var-simple)
  (defthm lambda-free-termsp-of-sublis-var-simple-lst
    (implies (and (lambda-free-termsp terms)
                  (lambda-free-termsp (strip-cdrs alist)))
             (lambda-free-termsp (sublis-var-simple-lst alist terms)))
    :flag sublis-var-simple-lst)
  :hints (("Goal" :in-theory (enable sublis-var-simple
                                     sublis-var-simple-lst))))

;; End of library material

;; Expands away all lambdas in TERM (beta reduction).  This is similar to the
;; built-in function REMOVE-LAMBDAS, but that one does more (to preserve quote
;; normal form). For example: (remove-lambdas '((lambda (x y) (binary-+ x y))
;; '1 '2)) produces '3 whereas we want (binary-+ '1 '2).
(mutual-recursion
 (defund expand-lambdas-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :measure (acl2-count term)
                   :verify-guards nil ; done below
                   ))
   (if (or (variablep term)
           (fquotep term))
       term
     ;;it's a function call (maybe a lambda application):
     (let* ((args (fargs term))
            (args (expand-lambdas-in-terms args)) ;process the args first
            (fn (ffn-symb term)))
       (if (flambdap fn) ;test for lambda application.  term is: ((lambda (formals) body) ... args ...)
           (let* ((lambda-body (expand-lambdas-in-term (lambda-body fn)))) ;;apply recursively to the lambda body
             ;; beta-reduce (TODO: Make a simple version of subcor-var and call that here):
             (sublis-var-simple (pairlis$ (lambda-formals fn) args) lambda-body))
         ;;not a lambda application, so just rebuild the function call:
         `(,fn ,@args)))))

 (defund expand-lambdas-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)
                   :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (expand-lambdas-in-term (first terms))
           (expand-lambdas-in-terms (rest terms))))))

(make-flag expand-lambdas-in-term)

;TODO: Automate some of this?

(defthm len-of-expand-lambdas-in-terms
  (equal (len (expand-lambdas-in-terms terms))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable len expand-lambdas-in-terms))))

(defthm consp-of-expand-lambdas-in-terms
  (equal (consp (expand-lambdas-in-terms terms))
         (consp terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable len expand-lambdas-in-terms))))

;; Expanding lambdas preserves pseudo-termp.
(defthm-flag-expand-lambdas-in-term
  (defthm pseudo-termp-of-expand-lambdas-in-term
    (implies (pseudo-termp term)
             (pseudo-termp (expand-lambdas-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm pseudo-term-listp-of-expand-lambdas-in-terms
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (expand-lambdas-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :in-theory (enable expand-lambdas-in-term
                                     expand-lambdas-in-terms))))

(verify-guards expand-lambdas-in-term)

(defthm car-of-expand-lambdas-in-terms
  (equal (car (expand-lambdas-in-terms terms))
         (expand-lambdas-in-term (car terms)))
  :hints (("Goal" :in-theory (enable expand-lambdas-in-terms))))

;; Expanding lambdas creates a lambda-free term.
(defthm-flag-expand-lambdas-in-term
  (defthm lambda-free-termp-of-expand-lambdas-in-term
    (implies (pseudo-termp term)
             (lambda-free-termp (expand-lambdas-in-term term)))
    :flag expand-lambdas-in-term)
  (defthm lambda-free-term-listp-of-expand-lambdas-in-terms
    (implies (pseudo-term-listp terms)
             (lambda-free-termsp (expand-lambdas-in-terms terms)))
    :flag expand-lambdas-in-terms)
  :hints (("Goal" :in-theory (enable expand-lambdas-in-term
                                     expand-lambdas-in-terms
                                     pairlis$))))

;; Since the new term is lambda-free
(defthm not-consp-of-car-of-expand-lambdas-in-term
  (implies (pseudo-termp term)
           (not (consp (car (expand-lambdas-in-term term)))))
  :hints (("Goal" :use (:instance lambda-free-termp-of-expand-lambdas-in-term)
           ;; :expand (expand-lambdas-in-term term)
           :in-theory (e/d (lambda-free-termp)
                           (lambda-free-termp-of-expand-lambdas-in-term)))))
