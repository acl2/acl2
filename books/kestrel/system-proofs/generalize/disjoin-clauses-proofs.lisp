; Correctness of disjoin-clauses
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; We show that disjoin-clauses is sound: If the clause it returns is false,
;; then so are both of the clauses it was given.  (Disjoin-clauses may return
;; the true clause, or drop a literal, when it sees that the result is a
;; tautology or that a literal is redundant.)

(include-book "generalize-logic")
(include-book "generalize-ev")
(include-book "tools/flag" :dir :system)

(local (in-theory (disable generalize-ev-of-fncall-args)))

;; A call of EQUAL or IFF has the meaning given by its first two arguments.
(local
 (defthmd generalize-ev-when-equal-or-iff
   (implies (and (member-equal (car term) '(equal iff))
                 (consp term))
            (equal (generalize-ev term a)
                   (generalize-ev (list (car term) (cadr term) (caddr term)) a)))
   :hints (("Goal" :in-theory (e/d (generalize-ev-of-fncall-args) (generalize-ev-of-fncall-args-back))))))

(defthm generalize-ev-when-comm-equal
  (implies (and (comm-equal fn lhs rhs term)
                (member-equal fn '(equal iff)))
           (equal (generalize-ev term a)
                  (generalize-ev (list fn lhs rhs) a)))
  :hints (("Goal" :use generalize-ev-when-equal-or-iff
           :in-theory (enable comm-equal))))

(defthm not-generalize-ev-when-member-term2
  (implies (and (member-term2 fn lhs rhs cl)
                (all-eval-to-false-with-generalize-ev cl a)
                (member-equal fn '(equal iff)))
           (not (generalize-ev (list fn lhs rhs) a)))
  :hints (("Goal" :in-theory (enable member-term2))))

(defthm generalize-ev-when-member-complement-term1
  (implies (and (member-complement-term1 lit cl)
                (all-eval-to-false-with-generalize-ev cl a))
           (generalize-ev lit a))
  :hints (("Goal" :in-theory (enable member-complement-term1))))

(defthm generalize-ev-when-member-complement-term2
  (implies (and (member-complement-term2 fn lhs rhs cl)
                (all-eval-to-false-with-generalize-ev cl a)
                (member-equal fn '(equal iff)))
           (generalize-ev (list fn lhs rhs) a))
  :hints (("Goal" :in-theory (enable member-complement-term2))))

(make-flag member-term)

;; Member-term detects a literal that is already in the clause (perhaps
;; differently expressed), and member-complement-term detects a literal whose
;; complement is in the clause.
(defthm-flag-member-term
  (defthm not-generalize-ev-when-member-term
    (implies (and (member-term lit cl)
                  (all-eval-to-false-with-generalize-ev cl a))
             (not (generalize-ev lit a)))
    :flag member-term)
  (defthm generalize-ev-when-member-complement-term
    (implies (and (member-complement-term lit cl)
                  (all-eval-to-false-with-generalize-ev cl a))
             (generalize-ev lit a))
    :flag member-complement-term)
  :hints (("Goal" :in-theory (enable member-term member-complement-term))))

;; Adding a false literal to a false clause gives a false clause.
(defthm all-eval-to-false-with-generalize-ev-of-add-literal
  (implies (and (not (generalize-ev lit a))
                (all-eval-to-false-with-generalize-ev cl a)
                (pseudo-termp lit))
           (all-eval-to-false-with-generalize-ev (add-literal lit cl at-end-flg) a))
  :hints (("Goal" :use (generalize-ev-when-member-complement-term
                        (:instance generalize-ev-when-member-complement-term1
                                   (lit (cons 'integerp (cdr lit))))
                        (:instance not-generalize-ev-when-all-eval-to-false-with-generalize-ev-and-member-equal
                                   (term (cons 'rationalp (cdr (cadr lit))))
                                   (terms cl)))
           :in-theory (e/d (add-literal) (member-term member-complement-term)))
          (and stable-under-simplificationp
               '(:in-theory (e/d (add-literal generalize-ev-of-fncall-args)
                                 (generalize-ev-of-fncall-args-back
                                  member-term member-complement-term))))))

(defthm all-eval-to-false-with-generalize-ev-of-disjoin-clauses1
  (implies (and (all-eval-to-false-with-generalize-ev cl1 a)
                (all-eval-to-false-with-generalize-ev cl2 a)
                (pseudo-term-listp cl2))
           (all-eval-to-false-with-generalize-ev (disjoin-clauses1 cl1 cl2) a))
  :hints (("Goal" :in-theory (enable disjoin-clauses1))))

;; The main theorem of this book.
(defthm all-eval-to-false-with-generalize-ev-of-disjoin-clauses
  (implies (and (all-eval-to-false-with-generalize-ev cl1 a)
                (all-eval-to-false-with-generalize-ev cl2 a)
                (pseudo-term-listp cl2))
           (all-eval-to-false-with-generalize-ev (disjoin-clauses cl1 cl2) a))
  :hints (("Goal" :in-theory (enable disjoin-clauses))))
