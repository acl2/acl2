; A utility to gather the let-bound vars in a term
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We use the term "let var" to mean a variable bound in a lambda that is not
;; trivially bound (that is, that is not bound to itself).  Trivial bindings
;; often arise because lambdas in ACL2 must be complete.

(include-book "tools/flag" :dir :system)
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))

;; Returns (mv non-trivial-formals non-trivial-args).
(defun non-trivial-formals-and-args (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp args) ;; not necessarily pseudo-terms
                              )))
  (if (endp formals)
      (mv nil nil)
    (b* ((formal (first formals))
         (arg (first args))
         ((mv cdr-formals cdr-args)
          (non-trivial-formals-and-args (rest formals) (rest args))))
      (if (equal formal arg)
          ;; skip since trivial:
          (mv cdr-formals cdr-args)
        (mv (cons formal cdr-formals)
            (cons arg cdr-args))))))

(defthm symbol-listp-of-mv-nth-0-of-non-trivial-formals-and-args
  (implies (symbol-listp formals)
           (symbol-listp (mv-nth 0 (non-trivial-formals-and-args formals args)))))

(defthm true-listp-of-mv-nth-0-of-non-trivial-formals-and-args
  (implies (symbol-listp formals)
           (true-listp (mv-nth 0 (non-trivial-formals-and-args formals args)))))

(defthm true-listp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (true-listp args)
           (true-listp (mv-nth 1 (non-trivial-formals-and-args formals args)))))

(defthm pseudo-term-listp-of-mv-nth-1-of-non-trivial-formals-and-args
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (mv-nth 1 (non-trivial-formals-and-args formals args)))))

(defthm len-of-mv-nth-1-of-non-trivial-formals-and-args
  (equal (len (mv-nth 1 (non-trivial-formals-and-args formals args)))
         (len (mv-nth 0 (non-trivial-formals-and-args formals args))))
  :hints (("Goal" :in-theory (enable non-trivial-formals-and-args))))

;; Returns the members of formals that don't correspond to themselves in the args.
(defun non-trivial-formals (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args))))
  (if (endp formals)
      nil
    (b* ((formal (first formals))
         (arg (first args)))
      (if (equal formal arg)
          ;; skip since trivial:
          (non-trivial-formals (rest formals) (rest args))
        (cons formal (non-trivial-formals (rest formals) (rest args)))))))

(mutual-recursion
 ;; Gather all the vars that are bound in lambdas in TERM, except don't include
 ;; variable that ar simply bound to themselves.  Vars may appear only once in
 ;; the result.  Does not include vars that are free (unless they are also
 ;; bound by a lambbda).
 (defun let-vars-in-term (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       nil ;; not a lambda-bound var
     (let ((fn (ffn-symb term)))
       (if (eq fn 'quote)
           nil
         (if (consp fn)
             ;; a lambda application:
             (union-eq (non-trivial-formals (lambda-formals fn) (fargs term))
                       (union-eq (let-vars-in-term (lambda-body fn))
                                 (let-vars-in-terms (fargs term))))
           ;; not a lambda application:
           (let-vars-in-terms (fargs term)))))))

 (defun let-vars-in-terms (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (union-eq (let-vars-in-term (first terms))
               (let-vars-in-terms (rest terms))))))

;todo: make a variant of defthm-flag-xxx that puts in the guards as assumptions
(make-flag let-vars-in-term)

(defthm-flag-let-vars-in-term
  (defthm symbol-listp-of-let-vars-in-term
    (implies (pseudo-termp term)
             (symbol-listp (let-vars-in-term term)))
    :flag let-vars-in-term)
  (defthm symbol-listp-of-let-vars-in-terms
    (implies (pseudo-term-listp terms)
             (symbol-listp (let-vars-in-terms terms)))
    :flag let-vars-in-terms)
  :hints (("Goal" :expand (pseudo-term-listp term)
           :in-theory (enable pseudo-term-listp))))

(defthm-flag-let-vars-in-term
  (defthm true-listp-of-let-vars-in-term
    (true-listp (let-vars-in-term term))
    :flag let-vars-in-term)
  (defthm true-listp-of-let-vars-in-terms
    (true-listp (let-vars-in-terms terms))
    :flag let-vars-in-terms)
  :hints (("Goal" :expand (pseudo-term-listp term)
           :in-theory (enable pseudo-term-listp))))

(verify-guards let-vars-in-term)
