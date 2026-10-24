; Correctness of sublis-expr
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We show that replacing TERMS by fresh variables VARS, using sublis-expr,
;; preserves the meaning of a term, provided the variables are bound to the
;; values of the terms.  Note that sublis-expr does not look inside lambda
;; bodies, which is fine because a lambda body is evaluated using only the
;; values of its formals.

(include-book "generalize-logic")
(include-book "generalize-ev")
(include-book "tools/flag" :dir :system)
(include-book "kestrel/terms-light/free-vars-in-term" :dir :system)
(local (include-book "helpers"))

(local (in-theory (disable generalize-ev-of-fncall-args)))

;; The alist that binds each variable in VARS to the value of the
;; corresponding term in TERMS, in front of A.
(defund generalization-alist (terms vars a)
  (append (pairlis$ vars (generalize-ev-list terms a)) a))

;; The variables must be distinct, non-nil symbols, one for each term.
(defund generalization-vars-okp (vars terms)
  (and (symbol-listp vars)
       (no-duplicatesp-equal vars)
       (not (member-equal nil vars))
       (equal (len vars) (len terms))))

(local
 (defthm cdr-of-assoc-equal-of-append-of-pairlis$-when-not-member-equal
   (implies (not (member-equal key keys))
            (equal (assoc-equal key (append (pairlis$ keys vals) a))
                   (assoc-equal key a)))
   :hints (("Goal" :in-theory (enable pairlis$)))))

(local
 (defthm member-equal-of-cdr-of-assoc-equal-of-pairlis$
   (implies (and (assoc-equal x (pairlis$ terms vars))
                 (equal (len vars) (len terms)))
            (member-equal (cdr (assoc-equal x (pairlis$ terms vars))) vars))
   :hints (("Goal" :induct (pairlis$ terms vars)
            :in-theory (enable pairlis$)))))

;; Looking up the variable that replaces X gives the value of X.
(local
 (defthm assoc-equal-of-cdr-of-assoc-equal-of-pairlis$
   (implies (and (assoc-equal x (pairlis$ terms vars))
                 (no-duplicatesp-equal vars)
                 (equal (len vars) (len terms)))
            (equal (cdr (assoc-equal (cdr (assoc-equal x (pairlis$ terms vars)))
                                     (append (pairlis$ vars (generalize-ev-list terms a)) a)))
                   (generalize-ev x a)))
   :hints (("Goal" :induct (pairlis$ terms vars)
            :in-theory (enable pairlis$)))))

(local
 (defthm symbolp-when-member-equal-and-symbol-listp
   (implies (and (member-equal x vars)
                 (symbol-listp vars))
            (symbolp x))))

;; Evaluating the variable that replaces X gives the value of X.
(local
 (defthm generalize-ev-of-cdr-of-assoc-equal-of-pairlis$
   (implies (and (assoc-equal x (pairlis$ terms vars))
                 (generalization-vars-okp vars terms))
            (equal (generalize-ev (cdr (assoc-equal x (pairlis$ terms vars)))
                                  (append (pairlis$ vars (generalize-ev-list terms a)) a))
                   (generalize-ev x a)))
   :hints (("Goal" :use member-equal-of-cdr-of-assoc-equal-of-pairlis$
            :in-theory (e/d (generalization-vars-okp)
                            (member-equal-of-cdr-of-assoc-equal-of-pairlis$))))))

(make-flag sublis-expr)

(defthm-flag-sublis-expr
  (defthm generalize-ev-of-sublis-expr-helper
    (implies (and (equal alist (pairlis$ terms vars))
                  (generalization-vars-okp vars terms)
                  (not (intersectp-equal vars (free-vars-in-term term)))
                  (pseudo-termp term))
             (equal (generalize-ev (sublis-expr alist term)
                                   (generalization-alist terms vars a))
                    (generalize-ev term a)))
    :flag sublis-expr)
  (defthm generalize-ev-list-of-sublis-expr-lst-helper
    (implies (and (equal alist (pairlis$ terms vars))
                  (generalization-vars-okp vars terms)
                  (not (intersectp-equal vars (free-vars-in-terms lst)))
                  (pseudo-term-listp lst))
             (equal (generalize-ev-list (sublis-expr-lst alist lst)
                                        (generalization-alist terms vars a))
                    (generalize-ev-list lst a)))
    :flag sublis-expr-lst)
  :hints (("Goal" :expand ((free-vars-in-term term)
                           (free-vars-in-terms lst))
           :in-theory (e/d (sublis-expr sublis-expr-lst generalization-alist
                                        generalization-vars-okp
                                        generalize-ev-of-fncall-args)
                           (generalize-ev-of-fncall-args-back)))))

;; Replacing the terms by the variables preserves the meaning of a term.
(defthm generalize-ev-of-sublis-expr
  (implies (and (generalization-vars-okp vars terms)
                (not (intersectp-equal vars (free-vars-in-term term)))
                (pseudo-termp term))
           (equal (generalize-ev (sublis-expr (pairlis$ terms vars) term)
                                 (generalization-alist terms vars a))
                  (generalize-ev term a))))

(defthm generalize-ev-list-of-sublis-expr-lst
  (implies (and (generalization-vars-okp vars terms)
                (not (intersectp-equal vars (free-vars-in-terms lst)))
                (pseudo-term-listp lst))
           (equal (generalize-ev-list (sublis-expr-lst (pairlis$ terms vars) lst)
                                      (generalization-alist terms vars a))
                  (generalize-ev-list lst a))))
