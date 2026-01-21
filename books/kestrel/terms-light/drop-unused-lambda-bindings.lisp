; Tools to clean up lambda applications in terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also remove-guard-holders-and-clean-up-lambdas and remove-guard-holders-weak.

;; TODO: Also handle the case where the lambda body is just a var (one of the
;; lambda formals -- in fact, the only lambda formal once we clean up).

;; TODO: Consider also removing guard holders.

;; TODO: Consider (optionally?) not lambda-binding a value that is only used
;; once in the lambda body.

(include-book "tools/flag" :dir :system)
(include-book "filter-formals-and-actuals")
(include-book "free-vars-in-term")
(include-book "make-lambda-with-hint")
;(local (include-book "std/system/all-vars" :dir :system))
(local (include-book "filter-formals-and-actuals-proofs"))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(in-theory (disable mv-nth))

(local (in-theory (disable reverse ;all-vars
                           )))

;; also in books/std/typed-lists/pseudo-term-listp
(local
 (defthmd pseudo-term-listp-when-symbol-listp
   (implies (symbol-listp syms)
            (pseudo-term-listp syms))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Gets rid of lambda formals not used in the corresponding lambda bodies, and their corresponding actuals of those formals.
;; TODO: Get rid of trivial lambdas (ones that bind all of their formals to themselves)?  Or at least empty lambdas (ones with no formals).
(mutual-recursion
 (defun drop-unused-lambda-bindings (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term
         (let ((args (drop-unused-lambda-bindings-lst (fargs term))))
           (if (consp fn)
               ;; it's a lambda:
               (let* ((body (lambda-body fn))
                      (body (drop-unused-lambda-bindings body))
                      (formals (lambda-formals fn))
                      (body-vars (free-vars-in-term body)))
                 (mv-let (formals args)
                   (filter-formals-and-actuals formals args body-vars)
                   ;; could put this back, or call make-lambda-application-simple:
                   ;;(if (equal formals args)
                       ;; If the remaining formals are the same as the args, we
                       ;; don't need a lambda at all:
                       ;; TODO: Or rely on drop-trivial-lambdas for that?
                   ;;    body
                   (cons-with-hint (make-lambda-with-hint formals body fn) args term)
                   ;)
                   ))
             ;; not a lambda:
             (cons-with-hint fn args term)))))))
 (defun drop-unused-lambda-bindings-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons-with-hint (drop-unused-lambda-bindings (first terms))
                     (drop-unused-lambda-bindings-lst (rest terms))
                     terms))))

(make-flag drop-unused-lambda-bindings)

(defthm-flag-drop-unused-lambda-bindings
  (defthm pseudo-termp-of-drop-unused-lambda-bindings
    (implies (pseudo-termp term)
             (pseudo-termp (drop-unused-lambda-bindings term)))
    :flag drop-unused-lambda-bindings)
  (defthm pseudo-term-listp-of-drop-unused-lambda-bindings-lst
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (drop-unused-lambda-bindings-lst terms)))
    :flag drop-unused-lambda-bindings-lst)
  :hints (("Goal" :in-theory (enable pseudo-term-listp-when-symbol-listp))))

(defthm len-of-drop-unused-lambda-bindings-lst
  (equal (len (drop-unused-lambda-bindings-lst terms))
         (len terms))
  :hints (("Goal" :induct (len terms))))

(verify-guards drop-unused-lambda-bindings :hints (("Goal" :expand ((pseudo-termp term)))))
