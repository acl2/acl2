; A tools to substitute lambda vars that are bound to constants
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
;; TODO: 2. Avoid trivial lambdas (all formals bound to themselves).  Maybe.  Or just call drop-trivial-lambdas.

(include-book "sublis-var-simple")
(include-book "no-nils-in-termp")
(local (include-book "sublis-var-simple-proofs"))
(local (include-book "kestrel/typed-lists-light/pseudo-term-listp" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "kestrel/lists-light/intersection-equal" :dir :system))
(local (include-book "kestrel/lists-light/list-sets" :dir :system))

(in-theory (disable mv-nth))

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
 (defund substitute-constants-in-lambdas (term)
   (declare (xargs :guard (pseudo-termp term)
                   :verify-guards nil ;done below
                   ))
   (if (variablep term)
       term
     (let ((fn (ffn-symb term)))
       (if (eq 'quote fn)
           term
         (let ((args (substitute-constants-in-lambdas-lst (fargs term))))
           (if (consp fn)
               ;; it's a lambda:
               (let* ((body (lambda-body fn))
                      (body (substitute-constants-in-lambdas body))
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
 (defund substitute-constants-in-lambdas-lst (terms)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons-with-hint (substitute-constants-in-lambdas (first terms))
                     (substitute-constants-in-lambdas-lst (rest terms))
                     terms))))

(make-flag substitute-constants-in-lambdas)

(defthm len-of-substitute-constants-in-lambdas-lst
  (equal (len (substitute-constants-in-lambdas-lst terms))
         (len terms))
  :hints (("Goal" :induct (len terms)
           :in-theory (enable substitute-constants-in-lambdas-lst))))

(defthm-flag-substitute-constants-in-lambdas
  (defthm pseudo-termp-of-substitute-constants-in-lambdas
    (implies (pseudo-termp term)
             (pseudo-termp (substitute-constants-in-lambdas term)))
    :flag substitute-constants-in-lambdas)
  (defthm pseudo-termp-of-substitute-constants-in-lambdas-lst
    (implies (pseudo-term-listp terms)
             (pseudo-term-listp (substitute-constants-in-lambdas-lst terms)))
    :flag substitute-constants-in-lambdas-lst)
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable substitute-constants-in-lambdas
                              substitute-constants-in-lambdas-lst
                              pseudo-term-listp-when-symbol-listp
                              intersection-equal-of-set-difference-equal-arg2))))

(verify-guards substitute-constants-in-lambdas :hints (("Goal" :expand ((PSEUDO-TERMP TERM)))))
