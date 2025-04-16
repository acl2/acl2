; A tool to replace (if x x y) with (if x t y) in boolean contexts
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; The pattern (if x x y) can come from translating (or x y), but we don't want to rewrite X twice if we can avoid it.
;; TODO: Consider also bool-fixing constants (see below, or sepatately?)
;; TODO: Consider lambda binding the X when we don't have boolean info.

(include-book "make-lambda-with-hint")
(local (include-book "tools/flag" :dir :system))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))

;; todo: what should we name this?  it may soon also also bool-fix constants.
(mutual-recursion
  ;; If iffp is true, the result must only be boolean equivalent to the input.  Otherwise it must be EQUAL.
 (defun simplify-ors (term iffp)
   (declare (xargs :guard (and (pseudo-termp term)
                               (booleanp iffp))
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (case fn
         (quote term
                ;; todo: consider this:
                ;; (if (and iffp
                ;;          (not (booleanp (unquote term))))
                ;;     ;; bool-fix the constant:
                ;;     (kwote (if term t nil))
                ;;   term)
                )
         ;; (if test then else):
         (if (if (not (consp (cddr (fargs term)))) ; for guard proof
                 (prog2$ (er hard? 'simplify-ors "Bad term: ~x0." term)
                         term)
               (let* ((test (fargn term 1))
                      (then (fargn term 2))
                      (else (fargn term 3))
                      (test (simplify-ors test t)) ; only have to preserve IFF for the test
                      (then (simplify-ors then iffp)) ; propagate IFF context to branches
                      (else (simplify-ors else iffp)))
                 (if (and iffp
                          (equal test then))
                     ;; replace (if x x y) with (if x 't y):
                     `(if ,test 't ,else)
                   ;; todo: cons-with-hint:
                   `(if ,test ,then ,else)))))
         ;; (not arg):
         (not (if (not (consp (fargs term))) ; for guard proof
                  (prog2$ (er hard? 'simplify-ors "Bad term: ~x0." term)
                          term)
                (let* ((arg (fargn term 1))
                       (arg (simplify-ors arg t))) ; use a boolean context for the arg
                  `(not ,arg))))
         ;; todo: build in any other functions?  myif/boolif
         (t ;; normal function call or lambda application:
          (let ((args (simplify-ors-lst (fargs term)))) ; can't use boolean context for args
            (if (consp fn)
                ;; it's a lambda:
                (let* ((formals (lambda-formals fn))
                       (body (lambda-body fn))
                       ;; propagate boolean context:
                       (body (simplify-ors body iffp)))
                  `(,(make-lambda-with-hint formals body fn) ;;(lambda ,formals ,body)
                    ,@args))
              ;; non-lambda:
              (cons-with-hint fn args term))))))))

 ;; TODO: Generalize to take iffp arguments for each of the terms?
 (defun simplify-ors-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons-with-hint (simplify-ors (first terms) nil)
                     (simplify-ors-lst (rest terms))
                     terms))))

(local (make-flag simplify-ors))

(defthm len-of-simplify-ors-lst
  (equal (len (simplify-ors-lst terms))
         (len terms))
  :hints (("Goal" :induct (len terms))))

(local
 (defthm-flag-simplify-ors
   (defthm pseudo-termp-of-simplify-ors
     (implies (pseudo-termp term)
              (pseudo-termp (simplify-ors term iffp)))
     :flag simplify-ors)
   (defthm pseudo-termp-of-simplify-ors-lst
     (implies (pseudo-term-listp terms)
              (pseudo-term-listp (simplify-ors-lst terms)))
     :flag simplify-ors-lst)
   :hints (("Goal" :in-theory (enable pseudo-term-listp-when-symbol-listp)))))

;; redundant and non-local
(defthm pseudo-termp-of-simplify-ors
  (implies (pseudo-termp term)
           (pseudo-termp (simplify-ors term iffp))))

;; redundant and non-local
(defthm pseudo-term-listp-of-simplify-ors-lst
  (implies (pseudo-term-listp terms)
           (pseudo-term-listp (simplify-ors-lst terms))))

(verify-guards simplify-ors :hints (("Goal" :expand ((pseudo-termp term)))))
