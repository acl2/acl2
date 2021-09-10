; Tools to clean up lambda applications in terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/std/system/all-vars" :dir :system))
(local (include-book "kestrel/lists-light/revappend" :dir :system))
(local (include-book "kestrel/lists-light/reverse" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

(in-theory (disable mv-nth))

(local (in-theory (disable reverse all-vars)))

;; Walk down FORMALS and ACTUALS in sync, dropping any formal, and its
;; corresponding actual, that is not in BODY-VARS.  Returns (mv formals
;; actuals).
(defun drop-unused-lambda-formals-and-actuals (formals actuals body-vars formals-acc actuals-acc)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp actuals)
                              (symbol-listp body-vars)
                              (symbol-listp formals-acc)
                              (pseudo-term-listp actuals-acc))
                  :verify-guards nil ;done below
                  ))
  (if (endp formals)
      (mv (reverse formals-acc)
          (reverse actuals-acc))
    (let* ((formal (first formals)))
      (if (member-eq formal body-vars)
          (drop-unused-lambda-formals-and-actuals (rest formals) (rest actuals) body-vars
                                                  (cons formal formals-acc)
                                                  (cons (first actuals) actuals-acc))
        ;; drop the formal and the actual:
        (drop-unused-lambda-formals-and-actuals (rest formals) (rest actuals) body-vars
                                                formals-acc
                                                actuals-acc)))))

(defthm symbol-listp-of-mv-nth-0-of-drop-unused-lambda-formals-and-actuals
  (implies (and (symbol-listp formals-acc)
                (symbol-listp formals))
           (symbol-listp (mv-nth 0 (drop-unused-lambda-formals-and-actuals
                                    formals actuals body-vars formals-acc actuals-acc)))))

(defthm pseudo-term-listp-of-mv-nth-1-of-drop-unused-lambda-formals-and-actuals
  (implies (and (pseudo-term-listp actuals-acc)
                (pseudo-term-listp actuals))
           (pseudo-term-listp (mv-nth 1 (drop-unused-lambda-formals-and-actuals
                                    formals actuals body-vars formals-acc actuals-acc)))))

(defthm true-listp-of-mv-nth-0-of-drop-unused-lambda-formals-and-actuals
  (implies (true-listp formals-acc)
           (true-listp (mv-nth 0 (drop-unused-lambda-formals-and-actuals
                                  formals actuals body-vars formals-acc actuals-acc))))
  :rule-classes (:rewrite :type-prescription))

(defthm true-listp-of-mv-nth-1-of-drop-unused-lambda-formals-and-actuals
  (implies (true-listp actuals-acc)
           (true-listp (mv-nth 1 (drop-unused-lambda-formals-and-actuals
                                  formals actuals body-vars formals-acc actuals-acc))))
  :rule-classes (:rewrite :type-prescription))

(verify-guards drop-unused-lambda-formals-and-actuals)

(defthm len-of-mv-nth-1-of-drop-unused-lambda-formals-and-actuals
  (implies (equal (len formals-acc) (len actuals-acc))
           (equal (len (mv-nth 1 (drop-unused-lambda-formals-and-actuals formals actuals body-vars formals-acc actuals-acc)))
                  (len (mv-nth 0 (drop-unused-lambda-formals-and-actuals formals actuals body-vars formals-acc actuals-acc))))))

;; Gets rid of lambda formals not used in the corresponding lambda bodies, and
;; gets rid of trivial lambdas (ones that bind all of their formals to themselves).
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
                      (body-vars (all-vars body)))
                 (mv-let (formals args)
                   (drop-unused-lambda-formals-and-actuals formals args body-vars nil nil)
                   (if (equal formals args)
                       ;; If the remaining formals are the same as the args, we
                       ;; don't need a lambda at all:
                       body
                     `((lambda ,formals ,body) ,@args))))
             ;; not a lambda:
             (cons-with-hint fn args term)))))))
 (defun drop-unused-lambda-bindings-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (drop-unused-lambda-bindings (first terms))
           (drop-unused-lambda-bindings-lst (rest terms))))))

(make-flag drop-unused-lambda-bindings)

;; also in books/std/typed-lists/pseudo-term-listp
(defthmd pseudo-term-listp-when-symbol-listp
  (implies (symbol-listp syms)
           (pseudo-term-listp syms)))

(defthm-flag-drop-unused-lambda-bindings
  (defthm pseudo-termp-of-drop-unused-lambda-bindings
    (implies (pseudo-termp term)
             (pseudo-termp (drop-unused-lambda-bindings term)))
    :flag drop-unused-lambda-bindings)
  (defthm pseudo-termp-of-drop-unused-lambda-bindings-lst
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (drop-unused-lambda-bindings-lst terms)))
    :flag drop-unused-lambda-bindings-lst)
  :hints (("Goal" :in-theory (enable pseudo-term-listp-when-symbol-listp))))

(verify-guards drop-unused-lambda-bindings :hints (("Goal" :expand ((PSEUDO-TERMP TERM)))))
