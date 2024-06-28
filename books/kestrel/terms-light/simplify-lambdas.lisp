; Tools to simplify lambda applications in terms
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; STATUS: IN-PROGRESS

;; This does the following to lambdas:
;; 1. Substitute for lambda vars bound to constants
;; TODO: 2. Avoid trivial lambdas (all formals bound to themselves).  Or do this separately?

;; TODO: add more kinds of simplifications (see clean-up-lambdas, etc.).  Perhaps first freeze and rename this to something like substitute-constants-for-lambda-vars.lisp.

(include-book "sublis-var-simple")
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
;(local (include-book "kestrel/lists-light/list-sets" :dir :system)) ; drop?

(in-theory (disable mv-nth))

;move
(defthm intersection-equal-of-set-difference-equal-arg2
  (equal (intersection-equal x (set-difference-equal y z))
         (set-difference-equal (intersection-equal x y) z))
  :hints (("Goal" :in-theory (enable intersection-equal
                                     set-difference-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv formals-for-constant-args constant-args).
(defund formals-and-constant-args (formals args)
  (declare (xargs :guard (and (symbol-listp formals)
                              (equal (len formals) (len args)))))
  (if (endp formals)
      (mv nil nil)
    (let ((formal (first formals))
          (arg (first args)))
      (mv-let (rest-formals rest-args)
        (formals-and-constant-args (rest formals) (rest args))
        (if (quotep arg)
            (mv (cons formal rest-formals)
                (cons arg rest-args))
          (mv rest-formals rest-args))))))

(defthm symbol-listp-of-mv-nth-0-of-formals-and-constant-args
  (implies (symbol-listp formals)
           (symbol-listp (mv-nth 0 (formals-and-constant-args formals args))))
  :hints (("Goal" :in-theory (enable formals-and-constant-args))))

(defthm pseudo-term-listp-of-mv-nth-1-of-formals-and-constant-args
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (mv-nth 1 (formals-and-constant-args formals args))))
  :hints (("Goal" :in-theory (enable formals-and-constant-args))))

(defthm no-nils-in-termsp-of-mv-nth-1-of-formals-and-constant-args
  (implies (pseudo-term-listp args)
           (no-nils-in-termsp (mv-nth 1 (formals-and-constant-args formals args))))
  :hints (("Goal" :in-theory (enable formals-and-constant-args))))

(defthm len-of-mv-nth-1-of-formals-and-constant-args
  (equal (len (mv-nth 1 (formals-and-constant-args formals args)))
         (len (mv-nth 0 (formals-and-constant-args formals args))))
  :hints (("Goal" :in-theory (enable formals-and-constant-args))))

;; (thm
;;  (equal (intersection-equal formals1 (formals-and-constant-args formals2 args))
;;         (formals-and-constant-args (intersection-equal formals1 formals2) args))
;;  :hints (("Goal" :in-theory (enable ;formals-and-constant-args
;;                                     intersection-equal))))

;; (thm
;;  (equal (intersection-equal formals (formals-and-constant-args formals args))
;;         (formals-and-constant-args formals args))
;;  :hints (("Goal" :in-theory (enable formals-and-constant-args intersection-equal))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Walk through the args, keeping any that correspond to formals in target-formals.
;see also get-args-for-formals!
(defund filter-args-for-formals (formals args target-formals)
  (declare (xargs :guard (and (symbol-listp formals)
                              (true-listp args)
                              (equal (len formals) (len args))
                              (symbol-listp target-formals))
                  :measure (len args)))
  (if (endp args)
      nil
    (let ((arg (first args))
          (formal (first formals)))
      (if (member-eq formal target-formals)
          (cons arg (filter-args-for-formals (rest formals) (rest args) target-formals))
        (filter-args-for-formals (rest formals) (rest args) target-formals)))))

(defthm pseudo-term-listp-of-filter-args-for-formals
  (implies (pseudo-term-listp args)
           (pseudo-term-listp (filter-args-for-formals formals args target-formals)))
  :hints (("Goal" :in-theory (enable filter-args-for-formals))))

(defthm len-of-filter-args-for-formals
  (implies (equal (len formals) (len args))
           (equal (len (filter-args-for-formals formals args target-formals))
                  (len (intersection-equal formals target-formals))))
  :hints (("Goal" :in-theory (enable filter-args-for-formals))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(mutual-recursion
 (defund simplify-lambdas (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term
         (let ((args (simplify-lambdas-lst (fargs term))))
           (if (consp fn)
               ;; it's a lambda:
               (let* ((body (lambda-body fn))
                      (body (simplify-lambdas body))
                      (formals (lambda-formals fn)))
                 ;; could make a single pass to compute both formal lists and both arg lists
                 (mv-let (formals-for-constant-args constant-args)
                   (formals-and-constant-args formals args)
                   (let* ((remaining-formals (set-difference-eq formals formals-for-constant-args))
                          (remaining-args (filter-args-for-formals formals args remaining-formals))
                          (body (sublis-var-simple (pairlis$ formals-for-constant-args constant-args)
                                                   body)))
                     ;;(if (equal remaining-formals remaining-args) ; avoid trivial lambda application
                       ;;  body
                       `((lambda ,remaining-formals ,body) ,@remaining-args)
                   ;;  )
                   )))
             ;; not a lambda:
             (cons-with-hint fn args term)))))))
 (defund simplify-lambdas-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons-with-hint (simplify-lambdas (first terms))
                     (simplify-lambdas-lst (rest terms))
                     terms))))

(make-flag simplify-lambdas)

(defthm len-of-simplify-lambdas-lst
  (equal (len (simplify-lambdas-lst terms))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable simplify-lambdas-lst))))

(defthm-flag-simplify-lambdas
  (defthm pseudo-termp-of-simplify-lambdas
    (implies (pseudo-termp term)
             (pseudo-termp (simplify-lambdas term)))
    :flag simplify-lambdas)
  (defthm pseudo-termp-of-simplify-lambdas-lst
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (simplify-lambdas-lst terms)))
    :flag simplify-lambdas-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable simplify-lambdas
                              simplify-lambdas-lst
                              pseudo-term-listp-when-symbol-listp))))

(verify-guards simplify-lambdas :hints (("Goal" :expand ((PSEUDO-TERMP TERM)))))
