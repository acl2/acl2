; Copyright (C) 2016, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See soundness.lisp.  Here we prove a key lemma in support of that book.

(in-package "ACL2")

(include-book "satisfiable-add-proof-clause-base")

(defthm remove-deleted-clauses-leaves-no-deleted-clauses
  (implies (not (equal (cdr (hons-assoc-equal index acc))
                       0))
           (not (equal (cdr (hons-assoc-equal
                             index
                             (remove-deleted-clauses fal acc)))
                       0))))

(defthm shrink-formula-fal-has-no-deleted-clauses
  (not (equal (cdr (hons-assoc-equal index
                                     (shrink-formula-fal fal)))
              0))
  :hints (("Goal" :in-theory (enable shrink-formula-fal))))

(in-theory (disable fast-alist-clean))

(defthm hons-assoc-equal-remove-deleted-clauses-for-non-member
  (implies (not (member-equal index (strip-cars fal)))
           (equal (hons-assoc-equal index (remove-deleted-clauses fal acc))
                  (hons-assoc-equal index acc))))


(defthm hons-assoc-equal-remove-deleted-clauses
  (implies (no-duplicatesp-equal (strip-cars fal))
           (equal (hons-assoc-equal index (remove-deleted-clauses fal acc))
                  (if (equal (cdr (hons-assoc-equal index fal))
                             0)
                      (hons-assoc-equal index acc)
                    (or (hons-assoc-equal index fal)
                        (hons-assoc-equal index acc))))))

(defthm member-strip-cars-is-hons-assoc-equal
  (implies (alistp x)
           (iff (member a (strip-cars x))
                (hons-assoc-equal a x))))

(defthm no-duplicatesp-strip-cars-fast-alist-fork
  (implies (alistp ans)
           (iff (no-duplicatesp (strip-cars (fast-alist-fork alist ans)))
                (no-duplicatesp (strip-cars ans)))))

(defthm alistp-forward-to-null-cdr-last
  (implies (alistp x)
           (equal (cdr (last x))
                  nil))
  :rule-classes :forward-chaining)

(defthm no-duplicatesp-strip-cars-fast-alist-clean
  (implies (alistp fal)
           (no-duplicatesp (strip-cars (fast-alist-clean fal))))
  :hints (("Goal" :in-theory (enable fast-alist-clean))))

(defthm hons-assoc-equal-fast-alist-fork
  (equal (hons-assoc-equal key (fast-alist-fork fal ans))
         (or (hons-assoc-equal key ans)
             (hons-assoc-equal key fal))))

(defthm hons-assoc-equal-fast-alist-clean
  (implies (alistp fal)
           (equal (hons-assoc-equal key (fast-alist-clean fal))
                  (hons-assoc-equal key fal)))
  :hints (("Goal" :in-theory (enable fast-alist-clean))))

(defthm hons-assoc-equal-shrink-formula-fal
  (implies (alistp fal)
           (equal (hons-assoc-equal index (shrink-formula-fal fal))
                  (if (equal (cdr (hons-assoc-equal index fal))
                             0)
                      nil
                    (hons-assoc-equal index fal))))
  :hints (("Goal" :in-theory (enable shrink-formula-fal))))

(local (in-theory (enable formula-p)))

(defthm formula-true-p-maybe-shrink-formula-forward
  (implies
   (formula-p formula)
   (implies (formula-truep (mv-nth 2 (maybe-shrink-formula ncls ndel formula
                                                           factor))
                           assignment)
            (formula-truep formula assignment)))
  :hints (("Goal"
           :in-theory (enable maybe-shrink-formula)
           :expand ((formula-truep formula assignment))
           :restrict ((formula-truep-necc
                       ((index (formula-truep-witness formula assignment)))))))
  :rule-classes nil)

(defthm formula-true-p-maybe-shrink-formula-backward
  (implies
   (formula-p formula)
   (implies (formula-truep formula assignment)
            (formula-truep (mv-nth 2 (maybe-shrink-formula ncls ndel formula
                                                           factor))
                           assignment)))
  :hints (("Goal"
           :in-theory (enable maybe-shrink-formula)
           :expand ((formula-truep (shrink-formula-fal formula)
                                   assignment))))
  :rule-classes nil)

(defthm formula-true-p-maybe-shrink-formula
  (implies
   (formula-p formula)
   (equal (formula-truep (mv-nth 2 (maybe-shrink-formula ncls ndel formula
                                                         factor))
                         assignment)
          (formula-truep formula assignment)))
  :hints (("Goal" :use (formula-true-p-maybe-shrink-formula-forward
                        formula-true-p-maybe-shrink-formula-backward))))

(defthm satisfiable-maybe-shrink-formula-forward
  (implies
   (formula-p formula)
   (implies
    (satisfiable (mv-nth 2 (maybe-shrink-formula ncls ndel formula factor)))
    (satisfiable formula)))
  :hints
  (("Goal"
    :expand ((satisfiable (mv-nth 2 (maybe-shrink-formula ncls ndel formula factor))))
    :restrict
    ((satisfiable-suff
      ((assignment (satisfiable-witness
                    (mv-nth 2 (maybe-shrink-formula ncls ndel formula factor)))))))))
  :rule-classes nil)

(defthm satisfiable-maybe-shrink-formula-backward
  (implies
   (formula-p formula)
   (implies
    (satisfiable formula)
    (satisfiable (mv-nth 2 (maybe-shrink-formula ncls ndel formula factor)))))
  :hints
  (("Goal"
    :expand ((satisfiable formula))
    :restrict
    ((satisfiable-suff
      ((assignment (satisfiable-witness formula))))))))

(defthm satisfiable-maybe-shrink-formula
  (implies
   (formula-p formula)
   (equal (satisfiable (mv-nth 2 (maybe-shrink-formula ncls ndel formula factor)))
          (satisfiable formula)))
  :hints (("Goal" :use (satisfiable-maybe-shrink-formula-forward
                        satisfiable-maybe-shrink-formula-backward))))

(defthm satisfiable-cons-mv-nth-2-maybe-shrink-formula-lemma
  (implies
   (and
    (satisfiable (cons (cons index clause) formula))
    (formula-fal-p (formula-fal formula))
    (satisfiable formula))
   (satisfiable (cons (cons index clause)
                      (mv-nth 2
                              (maybe-shrink-formula ncls ndel formula
                                                    factor)))))

; I really don't like to give :instructions.  However, it was taking a lot of
; time on this one to eliminate proof-building commands in favor of :hints, so
; I'm going to live with this.  It's really not so horrible to use
; :instructions when nested quantifiers are involved (satisfiable is a defun-sk
; that calls formula-truep, which is a defun-sk).

  :instructions
  ((:in-theory (enable maybe-shrink-formula))
   (:bash ("Goal" :expand ((satisfiable (cons (cons index clause) formula)))))
   (:rewrite
    satisfiable-suff
    ((assignment (satisfiable-witness (cons (cons index clause) formula)))))
   (:bash ("Goal" :expand
           ((formula-truep
             (cons (cons index clause)
                   (shrink-formula-fal formula))
             (satisfiable-witness (cons (cons index clause) formula))))))
   (:contrapose 2)
   (:dv 1)
   (:rewrite formula-truep-necc ((index index)))
   :prove
   (:generalize
    ((formula-truep-witness
      (cons (cons index clause)
            (shrink-formula-fal formula))
      (satisfiable-witness (cons (cons index clause) formula)))
     index2))
   (:contrapose 2)
   (:dv 1)
   (:rewrite formula-truep-necc ((index index2)))
   :prove)
  :rule-classes nil)

(defthm satisfiable-cons-mv-nth-2-maybe-shrink-formula
  (implies
   (and
    (consp index/clause)
    (satisfiable (cons index/clause formula))
    (formula-fal-p (formula-fal formula))
    (satisfiable formula))
   (satisfiable (cons index/clause
                      (mv-nth 2
                              (maybe-shrink-formula ncls ndel formula
                                                    factor)))))
  :hints
  (("Goal"
    :use ((:instance satisfiable-cons-mv-nth-2-maybe-shrink-formula-lemma
                     (index (car index/clause))
                     (clause (cdr index/clause)))))))

(defthm unit-propagation-maybe-shrink-formula
  (implies (formula-p formula)
           (equal (unit-propagation
                   (mv-nth 2 (maybe-shrink-formula ncls ndel formula factor))
                   indices
                   clause)
                  (unit-propagation formula indices clause)))
  :hints (("Goal" :in-theory (enable maybe-shrink-formula formula-p))))
