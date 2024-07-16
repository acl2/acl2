; A tool to substitute lambda vars that are bound to constants
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "substitute-constants-in-lambdas") ; todo
(include-book "kestrel/utilities/quote" :dir :system) ; todo: reduce
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))

;move
(defun strong-quote-listp (items)
  (declare (xargs :guard t))
  (if (atom items)
      (null items)
    (and (myquotep (first items))
         (strong-quote-listp (rest items)))))

(local
  (defthm pseudo-termp-when-myquotep
    (implies (myquotep term)
             (pseudo-termp term))))

;; Returns (mv remaining-formals remaining-args var-constant-alist)
(defund handle-constant-lambda-formals (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (pseudo-term-listp args)
                              (equal (len formals) (len args)))))
  (if (endp formals)
      (mv nil nil nil)
    (mv-let (cdr-remaining-formals cdr-remaining-args cdr-var-constant-alist)
      (handle-constant-lambda-formals (rest formals) (rest args))
      (let ((formal (first formals))
            (arg (first args)))
        (if (quotep arg)
            (mv cdr-remaining-formals
                cdr-remaining-args
                (acons formal arg cdr-var-constant-alist))
          (mv (cons-with-hint formal cdr-remaining-formals formals)
              (cons-with-hint arg cdr-remaining-args args)
              cdr-var-constant-alist))))))

(local (in-theory (enable handle-constant-lambda-formals)))

(defthm handle-constant-lambda-formals-return-type
  (implies (and (symbol-listp formals)
                (pseudo-term-listp args)
                (equal (len formals) (len args)))
           (and (symbol-listp (mv-nth 0 (handle-constant-lambda-formals formals args)))
                (pseudo-term-listp (mv-nth 1 (handle-constant-lambda-formals formals args)))
                (symbol-alistp (mv-nth 2 (handle-constant-lambda-formals formals args)))
                (strong-quote-listp (strip-cdrs (mv-nth 2 (handle-constant-lambda-formals formals args))))
                (equal (len (mv-nth 1 (handle-constant-lambda-formals formals args)))
                       (len (mv-nth 0 (handle-constant-lambda-formals formals args)))))))


(mutual-recursion
 (defund substitute-constants-in-lambdas2-aux (term alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-alistp alist)
                               (strong-quote-listp (strip-cdrs alist)))
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       (let ((res (assoc-eq term alist)))
         (if res
             (cdr res) ; put in the constant for this var
           term))
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term
         ;; function call or lambda:
         (let ((new-args (substitute-constants-in-lambdas2-aux-lst (fargs term) alist)))
           (if (consp fn)
               ;; it's a lambda:
               (let ((formals (lambda-formals fn))
                     (body (lambda-body fn)))
                 (mv-let (remaining-formals remaining-args var-constant-alist)
                   (handle-constant-lambda-formals formals new-args)
                   ;; Since the lambda is closed, we completely replace the
                   ;; alist passed in when processing the lambda-body:
                   (let ((new-body (substitute-constants-in-lambdas2-aux body var-constant-alist)))
                     (if nil ; (equal remaining-formals remaining-args) ; todo: put back? but this affects the free vars in the result, about which we have a theorem
                         ;; avoid trivial lambda:
                         new-body
                       (cons-with-hint (make-lambda-with-hint remaining-formals new-body fn) remaining-args term)))))
             ;; not a lambda:
             (cons-with-hint fn new-args term)))))))
 (defund substitute-constants-in-lambdas2-aux-lst (terms alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-alistp alist)
                               (strong-quote-listp (strip-cdrs alist)))))
   (if (endp terms)
       nil
     (cons-with-hint (substitute-constants-in-lambdas2-aux (first terms) alist)
                     (substitute-constants-in-lambdas2-aux-lst (rest terms) alist)
                     terms))))

(defthm len-of-substitute-constants-in-lambdas2-aux-lst
  (equal (len (substitute-constants-in-lambdas2-aux-lst terms alist))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable substitute-constants-in-lambdas2-aux-lst))))

(make-flag substitute-constants-in-lambdas2-aux)

(defthm-flag-substitute-constants-in-lambdas2-aux
  (defthm pseudo-termp-of-substitute-constants-in-lambdas2-aux
    (implies (and (pseudo-termp term)
                  (strong-quote-listp (strip-cdrs alist)))
             (pseudo-termp (substitute-constants-in-lambdas2-aux term alist)))
    :flag substitute-constants-in-lambdas2-aux)
  (defthm pseudo-termp-of-substitute-constants-in-lambdas2-aux-lst
    (implies (and (pseudo-term-listp terms)
                  (strong-quote-listp (strip-cdrs alist)))
             (pseudo-term-listp (substitute-constants-in-lambdas2-aux-lst terms alist)))
    :flag substitute-constants-in-lambdas2-aux-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (pseudo-termp (cons (car term)
                        (substitute-constants-in-lambdas2-aux-lst (cdr term) alist)))
           :in-theory (enable pseudo-termp
                              pseudo-term-listp
                              substitute-constants-in-lambdas2-aux
                              substitute-constants-in-lambdas2-aux-lst
                              pseudo-term-listp-when-symbol-listp
                              intersection-equal-of-set-difference-equal-arg2
                              true-listp-when-symbol-listp-rewrite-unlimited))))

(verify-guards substitute-constants-in-lambdas2-aux-lst :hints (("Goal" :expand (pseudo-termp term) :in-theory (enable pseudo-termp))))

(defund substitute-constants-in-lambdas2 (term)
  (declare (xargs :guard (pseudo-termp term)))
  (substitute-constants-in-lambdas2-aux term nil))
