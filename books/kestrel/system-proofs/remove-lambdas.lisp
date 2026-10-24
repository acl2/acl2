; Correctness of the ACL2 system function remove-lambdas
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; REMOVE-LAMBDAS (in defuns.lisp) beta-reduces all lambda applications in a
;; term, using SUBCOR-VAR.  It is soundness-critical: for example, the
;; left-hand side of every :rewrite rule is put through remove-lambdas (see
;; interpret-term-as-rewrite-rule1), as are forward-chaining rules (see
;; destructure-forward-chaining-term).

;; We prove that remove-lambdas preserves the meaning of terms whose lambdas
;; are closed and that contain no NIL "variables".  Every term satisfying
;; TERMP has these properties (see remove-lambdas-correct-when-termp).  Neither
;; property is implied by the guard (PSEUDO-TERMP), and neither can be dropped
;; (see the counterexamples in remove-lambdas-tests.lisp).

(include-book "clause-processors/sublis-var-meaning" :dir :system) ; for cterm-ev
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambda-free-termp" :dir :system)
(local (include-book "subcor-var"))
(local (include-book "cterm-ev-helpers"))
(local (include-book "system/subcor-var" :dir :system)) ; for pseudo-termp of subcor-var
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/set-difference-equal" :dir :system))
(local (include-book "helpers"))
(local (include-book "tools/flag" :dir :system))

;; We reason about subcor-var directly, rather than in terms of sublis-var1.
(local (in-theory (disable subcor-var-is-sublis-var1 subcor-var-lst-is-sublis-var1-lst)))

(local (make-flag remove-lambdas1))

(defthm len-of-mv-nth-1-of-remove-lambdas-lst
  (equal (len (mv-nth 1 (remove-lambdas-lst termlist)))
         (len termlist))
  :hints (("Goal" :induct (len termlist)
           :in-theory (enable remove-lambdas-lst))))

(defthm-flag-remove-lambdas1
  (defthm pseudo-termp-of-mv-nth-1-of-remove-lambdas1
    (implies (pseudo-termp term)
             (pseudo-termp (mv-nth 1 (remove-lambdas1 term))))
    :flag remove-lambdas1)
  (defthm pseudo-term-listp-of-mv-nth-1-of-remove-lambdas-lst
    (implies (pseudo-term-listp termlist)
             (pseudo-term-listp (mv-nth 1 (remove-lambdas-lst termlist))))
    :flag remove-lambdas-lst))

(defthm-flag-remove-lambdas1
  (defthm no-nils-in-termp-of-mv-nth-1-of-remove-lambdas1
    (implies (and (no-nils-in-termp term)
                  (pseudo-termp term))
             (no-nils-in-termp (mv-nth 1 (remove-lambdas1 term))))
    :flag remove-lambdas1)
  (defthm no-nils-in-termsp-of-mv-nth-1-of-remove-lambdas-lst
    (implies (and (no-nils-in-termsp termlist)
                  (pseudo-term-listp termlist))
             (no-nils-in-termsp (mv-nth 1 (remove-lambdas-lst termlist))))
    :flag remove-lambdas-lst))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Like the recursion in remove-lambdas1, but the alist changes when we enter a
;; lambda body.
(local
 (defun induct-remove-lambdas1 (flg x a)
   (declare (xargs :measure (acl2-count x)))
   (if flg
       (if (or (variablep x)
               (fquotep x))
           a
         (if (flambdap (ffn-symb x))
             (list (induct-remove-lambdas1 nil (fargs x) a)
                   (induct-remove-lambdas1 t
                                           (lambda-body (ffn-symb x))
                                           (append (pairlis$ (lambda-formals (ffn-symb x))
                                                             (cterm-ev-lst (fargs x) a))
                                                   a)))
           (induct-remove-lambdas1 nil (fargs x) a)))
     (if (consp x)
         (list (induct-remove-lambdas1 t (car x) a)
               (induct-remove-lambdas1 nil (cdr x) a))
       a))))

(local
 (defthm remove-lambdas1-correct-flag
   (if flg
       (implies (and (pseudo-termp x)
                     (lambdas-closed-in-termp x)
                     (no-nils-in-termp x))
                (equal (cterm-ev (mv-nth 1 (remove-lambdas1 x)) a)
                       (cterm-ev x a)))
     (implies (and (pseudo-term-listp x)
                   (lambdas-closed-in-termsp x)
                   (no-nils-in-termsp x))
              (equal (cterm-ev-lst (mv-nth 1 (remove-lambdas-lst x)) a)
                     (cterm-ev-lst x a))))
   :rule-classes nil
   :hints (("Goal" :induct (induct-remove-lambdas1 flg x a)
            :in-theory (enable cterm-ev-of-fncall-args)))))

(defthm remove-lambdas1-correct
  (implies (and (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (no-nils-in-termp term))
           (equal (cterm-ev (mv-nth 1 (remove-lambdas1 term)) a)
                  (cterm-ev term a)))
  :hints (("Goal" :use (:instance remove-lambdas1-correct-flag (flg t) (x term)))))

(defthm remove-lambdas-lst-correct
  (implies (and (pseudo-term-listp termlist)
                (lambdas-closed-in-termsp termlist)
                (no-nils-in-termsp termlist))
           (equal (cterm-ev-lst (mv-nth 1 (remove-lambdas-lst termlist)) a)
                  (cterm-ev-lst termlist a)))
  :hints (("Goal" :use (:instance remove-lambdas1-correct-flag (flg nil) (x termlist)))))

;; The main theorem.
(defthm remove-lambdas-correct
  (implies (and (pseudo-termp term)
                (lambdas-closed-in-termp term)
                (no-nils-in-termp term))
           (equal (cterm-ev (remove-lambdas term) a)
                  (cterm-ev term a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Every proper term satisfies the hyps of remove-lambdas-correct (see
;; helpers.lisp).
(defthm remove-lambdas-correct-when-termp
  (implies (termp term w)
           (equal (cterm-ev (remove-lambdas term) a)
                  (cterm-ev term a))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Counterexamples showing that the hyps of remove-lambdas-correct (other than
;; pseudo-termp) cannot be dropped are in remove-lambdas-tests.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What REMOVE-LAMBDAS is for: the result contains no lambdas.  Also, the
;; CHANGEDP flag returned by remove-lambdas1 is accurate: when it is NIL, the
;; term is returned unchanged.  And remove-lambdas preserves termp.

(local (include-book "kestrel/terms-light/termp" :dir :system))

(defthm-flag-remove-lambdas1
  (defthm mv-nth-1-of-remove-lambdas1-when-unchanged
    (implies (and (not (mv-nth 0 (remove-lambdas1 term)))
                  (pseudo-termp term))
             (equal (mv-nth 1 (remove-lambdas1 term))
                    term))
    :flag remove-lambdas1)
  (defthm mv-nth-1-of-remove-lambdas-lst-when-unchanged
    (implies (and (not (mv-nth 0 (remove-lambdas-lst termlist)))
                  (pseudo-term-listp termlist))
             (equal (mv-nth 1 (remove-lambdas-lst termlist))
                    termlist))
    :flag remove-lambdas-lst))

(defthm-flag-remove-lambdas1
  (defthm lambda-free-termp-of-mv-nth-1-of-remove-lambdas1
    (implies (pseudo-termp term)
             (lambda-free-termp (mv-nth 1 (remove-lambdas1 term))))
    :flag remove-lambdas1)
  (defthm lambda-free-termsp-of-mv-nth-1-of-remove-lambdas-lst
    (implies (pseudo-term-listp termlist)
             (lambda-free-termsp (mv-nth 1 (remove-lambdas-lst termlist))))
    :flag remove-lambdas-lst)
  :hints (("Goal" :in-theory (enable lambda-free-termp))))

(defthm-flag-remove-lambdas1
  (defthm termp-of-mv-nth-1-of-remove-lambdas1
    (implies (termp term w)
             (termp (mv-nth 1 (remove-lambdas1 term)) w))
    :flag remove-lambdas1)
  (defthm term-listp-of-mv-nth-1-of-remove-lambdas-lst
    (implies (term-listp termlist w)
             (term-listp (mv-nth 1 (remove-lambdas-lst termlist)) w))
    :flag remove-lambdas-lst))

(defthm lambda-free-termp-of-remove-lambdas
  (implies (pseudo-termp term)
           (lambda-free-termp (remove-lambdas term))))

(defthm termp-of-remove-lambdas
  (implies (termp term w)
           (termp (remove-lambdas term) w)))

(defthm no-nils-in-termp-of-remove-lambdas
  (implies (and (no-nils-in-termp term)
                (pseudo-termp term))
           (no-nils-in-termp (remove-lambdas term))))

;; These two are trivial, since the result has no lambdas.
(defthm lambdas-closed-in-termp-of-remove-lambdas
  (implies (pseudo-termp term)
           (lambdas-closed-in-termp (remove-lambdas term))))

(defthm no-duplicate-lambda-formals-in-termp-of-remove-lambdas
  (implies (pseudo-termp term)
           (no-duplicate-lambda-formals-in-termp (remove-lambdas term))))
