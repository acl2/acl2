; Correctness of the ACL2 system function subst-var
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; cert_param: (non-acl2r)

;; SUBST-VAR (in translate.lisp) substitutes the term NEW for the variable OLD
;; in the term FORM.  It does not descend into lambda bodies (which are closed
;; in proper terms), and it rebuilds terms using CONS-TERM, which may evaluate
;; calls of primitives on constant arguments.  It is used, for example, when
;; evaluating clause-processor hints (eval-clause-processor), in destructor
;; elimination (apply-instantiated-elim-rule, via subst-var-lst), in
;; congruence rule processing, and in tau (convert-type-set-to-term1).

(include-book "clause-processors/sublis-var-meaning" :dir :system) ; for cterm-ev and the correctness of cons-term
(include-book "kestrel/terms-light/no-nils-in-termp" :dir :system)
(include-book "kestrel/terms-light/lambdas-closed-in-termp" :dir :system)
(include-book "kestrel/terms-light/no-duplicate-lambda-formals-in-termp" :dir :system)
(local (include-book "cons-term-helpers"))
(local (include-book "kestrel/terms-light/termp" :dir :system))
(local (include-book "kestrel/lists-light/subsetp-equal" :dir :system))
(local (include-book "kestrel/lists-light/union-equal" :dir :system))
(local (include-book "kestrel/lists-light/remove-equal" :dir :system))
(local (include-book "kestrel/lists-light/member-equal" :dir :system))
(local (include-book "tools/flag" :dir :system))

(local (make-flag subst-var))

;; Evaluating the result of SUBST-VAR is like evaluating FORM in an alist that
;; binds OLD to the value of NEW.
(defthm-flag-subst-var
  (defthm subst-var-correct
    (implies (and old ; the "variable" NIL always evaluates to NIL
                  (pseudo-termp form))
             (equal (cterm-ev (subst-var new old form) a)
                    (cterm-ev form (acons old (cterm-ev new a) a))))
    :flag subst-var)
  (defthm subst-var-lst-correct
    (implies (and old
                  (pseudo-term-listp l))
             (equal (cterm-ev-lst (subst-var-lst new old l) a)
                    (cterm-ev-lst l (acons old (cterm-ev new a) a))))
    :flag subst-var-lst)
  :hints (("Goal" :in-theory (enable cterm-ev-of-fncall-args))))

;; Replacing a variable with something that has the same value preserves the
;; value of the term.  Unlike subst-var-correct, this allows OLD to be NIL, and
;; FORM need not be a pseudo-term.
(defthm-flag-subst-var
  (defthm subst-var-correct-when-equal-values
    (implies (equal (cterm-ev new a) (cterm-ev old a))
             (equal (cterm-ev (subst-var new old form) a)
                    (cterm-ev form a)))
    :flag subst-var)
  (defthm subst-var-lst-correct-when-equal-values
    (implies (equal (cterm-ev new a) (cterm-ev old a))
             (equal (cterm-ev-lst (subst-var-lst new old l) a)
                    (cterm-ev-lst l a)))
    :flag subst-var-lst)
  :hints (("Goal" :in-theory (enable cterm-ev-of-fncall-args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Properties of terms that SUBST-VAR preserves.  (That it preserves
;; pseudo-termp is proved in books/system/subst-var.lisp.)

(defthm len-of-subst-var-lst
  (equal (len (subst-var-lst new old l))
         (len l))
  :hints (("Goal" :induct (len l)
           :in-theory (enable subst-var-lst))))

(defthm-flag-subst-var
  (defthm termp-of-subst-var
    (implies (and (termp new w)
                  (termp form w))
             (termp (subst-var new old form) w))
    :flag subst-var)
  (defthm term-listp-of-subst-var-lst
    (implies (and (termp new w)
                  (term-listp l w))
             (term-listp (subst-var-lst new old l) w))
    :flag subst-var-lst)
  :hints (("Goal" :in-theory (enable termp))))

(defthm-flag-subst-var
  (defthm no-nils-in-termp-of-subst-var
    (implies (and (no-nils-in-termp new)
                  (no-nils-in-termp form))
             (no-nils-in-termp (subst-var new old form)))
    :flag subst-var)
  (defthm no-nils-in-termsp-of-subst-var-lst
    (implies (and (no-nils-in-termp new)
                  (no-nils-in-termsp l))
             (no-nils-in-termsp (subst-var-lst new old l)))
    :flag subst-var-lst))

(defthm-flag-subst-var
  (defthm lambdas-closed-in-termp-of-subst-var
    (implies (and (lambdas-closed-in-termp new)
                  (lambdas-closed-in-termp form))
             (lambdas-closed-in-termp (subst-var new old form)))
    :flag subst-var)
  (defthm lambdas-closed-in-termsp-of-subst-var-lst
    (implies (and (lambdas-closed-in-termp new)
                  (lambdas-closed-in-termsp l))
             (lambdas-closed-in-termsp (subst-var-lst new old l)))
    :flag subst-var-lst)
  :hints (("Goal" :in-theory (enable lambdas-closed-in-termp))))

(defthm-flag-subst-var
  (defthm no-duplicate-lambda-formals-in-termp-of-subst-var
    (implies (and (no-duplicate-lambda-formals-in-termp new)
                  (no-duplicate-lambda-formals-in-termp form))
             (no-duplicate-lambda-formals-in-termp (subst-var new old form)))
    :flag subst-var)
  (defthm no-duplicate-lambda-formals-in-termsp-of-subst-var-lst
    (implies (and (no-duplicate-lambda-formals-in-termp new)
                  (no-duplicate-lambda-formals-in-termsp l))
             (no-duplicate-lambda-formals-in-termsp (subst-var-lst new old l)))
    :flag subst-var-lst)
  :hints (("Goal" :in-theory (enable no-duplicate-lambda-formals-in-termp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; What SUBST-VAR is for: the free vars of the result are those of NEW plus
;; those of FORM other than OLD (at most).

(defthm-flag-subst-var
  (defthm subsetp-equal-of-free-vars-in-term-of-subst-var
    (subsetp-equal (free-vars-in-term (subst-var new old form))
                   (union-equal (free-vars-in-term new)
                                (remove-equal old (free-vars-in-term form))))
    :flag subst-var)
  (defthm subsetp-equal-of-free-vars-in-terms-of-subst-var-lst
    (subsetp-equal (free-vars-in-terms (subst-var-lst new old l))
                   (union-equal (free-vars-in-term new)
                                (remove-equal old (free-vars-in-terms l))))
    :flag subst-var-lst)
  :hints (("Goal" :in-theory (enable free-vars-in-term free-vars-in-terms))))

;; In particular, OLD is no longer free, unless it is free in NEW.
(defthm not-member-equal-of-free-vars-in-term-of-subst-var
  (implies (not (member-equal old (free-vars-in-term new)))
           (not (member-equal old (free-vars-in-term (subst-var new old form)))))
  :hints (("Goal" :use (subsetp-equal-of-free-vars-in-term-of-subst-var
                        (:instance member-equal-when-subsetp-equal-1
                                   (x old)
                                   (lst2 (free-vars-in-term (subst-var new old form)))
                                   (lst (union-equal (free-vars-in-term new)
                                                     (remove-equal old (free-vars-in-term form))))))
           :in-theory (disable subsetp-equal-of-free-vars-in-term-of-subst-var
                               member-equal-when-subsetp-equal-1
                               member-equal-when-subsetp-equal-2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; SUBST-EACH-FOR-VAR (in translate.lisp) substitutes each of the NEW-LST in
;; turn for OLD in TERM, returning a list of terms.  It is used to make the
;; type expressions for a TYPE declaration with several variables (see
;; type-expressions-from-type-spec).

(defthm len-of-subst-each-for-var
  (equal (len (subst-each-for-var new-lst old term))
         (len new-lst)))

;; The Nth term returned evaluates like TERM in an alist that binds OLD to the
;; value of the Nth member of NEW-LST.
(defthm subst-each-for-var-correct
  (implies (and old ; the "variable" NIL always evaluates to NIL
                (pseudo-termp term)
                (< (nfix n) (len new-lst)))
           (equal (cterm-ev (nth n (subst-each-for-var new-lst old term)) a)
                  (cterm-ev term (acons old (cterm-ev (nth n new-lst) a) a))))
  :hints (("Goal" :induct (nth n new-lst)
           :in-theory (enable nth))))

;; Properties of terms that SUBST-EACH-FOR-VAR preserves.  (That it preserves
;; pseudo-termp is proved in books/system/remove-guard-holders.lisp.)

(defthm term-listp-of-subst-each-for-var
  (implies (and (term-listp new-lst w)
                (termp term w))
           (term-listp (subst-each-for-var new-lst old term) w))
  :hints (("Goal" :in-theory (enable subst-each-for-var))))

(defthm no-nils-in-termsp-of-subst-each-for-var
  (implies (and (no-nils-in-termsp new-lst)
                (no-nils-in-termp term))
           (no-nils-in-termsp (subst-each-for-var new-lst old term)))
  :hints (("Goal" :in-theory (enable subst-each-for-var))))

(defthm lambdas-closed-in-termsp-of-subst-each-for-var
  (implies (and (lambdas-closed-in-termsp new-lst)
                (lambdas-closed-in-termp term))
           (lambdas-closed-in-termsp (subst-each-for-var new-lst old term)))
  :hints (("Goal" :in-theory (enable subst-each-for-var))))

(defthm no-duplicate-lambda-formals-in-termsp-of-subst-each-for-var
  (implies (and (no-duplicate-lambda-formals-in-termsp new-lst)
                (no-duplicate-lambda-formals-in-termp term))
           (no-duplicate-lambda-formals-in-termsp (subst-each-for-var new-lst old term)))
  :hints (("Goal" :in-theory (enable subst-each-for-var))))
