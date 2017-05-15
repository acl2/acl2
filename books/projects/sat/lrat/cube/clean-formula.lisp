; Copyright (C) 2017, Regents of the University of Texas
; Marijn Heule, Warren A. Hunt, Jr., and Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See README.  This book supports (1) in README, to write out the transformed
; formula.  The problem is that the formula returned by function
; sat-preserved-check (see the final theorem, sat-preserved, in
; sat-preserved.lisp) need not be sorted by index, but we want it to match up
; with what is expected (using diff).  What's more, it may contain deleted
; clauses that shouldn't be printed (if it has pairs (n . :deleted)).  So we
; should print the result of removing shadowed and deleted pairs.  The function
; clean-formula, defined below, does that; but how do we know that it truly
; represents the formula F returned by sat-preserved-check?  It seems
; sufficient to prove that hons-assoc-equal agrees on both F and (clean-formula
; F).  The final theorem in this file does just that.

(in-package "LRAT")

(include-book "cube")

(include-book "demos/sort-by-car" :dir :system) ; redundant, from portcullis

(defun formula-valp (val)
  (declare (xargs :guard t))
  (or (deleted-clause-p val)
      (clause-or-assignment-p val)))

(defun formula-pair-p (pair)
  (declare (xargs :guard t))
  (and (consp pair)
       (posp (car pair))
       (formula-valp (cdr pair))))

(defun car< (x y)
  (declare (xargs :guard (and (formula-pair-p x)
                              (formula-pair-p y))))
  (< (car x) (car y)))

(acl2::defsort sort-by-car<
  :compare< car<
  :comparablep formula-pair-p
  :true-listp t
  :weak t)

(defthm sort-by-car<-list-p-sort-by-car<
  (implies (sort-by-car<-list-p formula)
           (sort-by-car<-list-p (sort-by-car< formula)))
  :rule-classes nil)

(defthm sort-by-car<-list-p-is-formula-p
  (equal (sort-by-car<-list-p x)
         (formula-p x))
  :hints (("Goal" :in-theory (enable sort-by-car<-list-p))))

(defthm formula-p-sort-by-car<
  (implies (formula-p formula)
           (formula-p (sort-by-car< formula)))
  :hints (("Goal" :use sort-by-car<-list-p-sort-by-car<)))

(defun clean-formula (formula)

; We return a formula equivalent to the input formula whose indices are in
; ascending order, suitable for printing.  Note that the returned formula is
; not a fast-alist.

  (declare (xargs :guard (formula-p formula)))
  (sort-by-car< (shrink-formula formula)))

; We want to know that if the formula is satisfiable, so is the cleaned
; formula.  We therefore prove that every member of the cleaned formula is

(defthm formula-p-clean-formula
  (implies (formula-p formula)
           (formula-p (clean-formula formula))))

(encapsulate
  ()
  (local (include-book "../list-based/satisfiable-maybe-shrink-formula"))
  (defthm hons-assoc-equal-shrink-formula
    (implies (alistp fal)
             (equal (hons-assoc-equal index (shrink-formula fal))
                    (if (equal (cdr (hons-assoc-equal index fal))
                               *deleted-clause*)
                        nil
                      (hons-assoc-equal index fal)))))
  (defthm no-duplicatesp-strip-cars-fast-alist-clean
    (implies (alistp fal)
             (no-duplicatesp (strip-cars (fast-alist-clean fal))))
    :hints (("Goal" :in-theory (enable fast-alist-clean)))))

(defthm sort-by-car<-preserves-assoc
     (implies (and (alistp alist)
                   (rational-listp (strip-cars alist))
                   (no-duplicatesp (strip-cars alist)))
              (equal (assoc index (sort-by-car< alist))
                     (assoc index alist)))
     :otf-flg t
     :hints (("Goal"
              :in-theory (enable sort-by-car::sort-by-car<-merge-tr
                                 sort-by-car::sort-by-car<-merge
                                 sort-by-car<-merge
                                 sort-by-car<)
              :do-not-induct t
              :by (:functional-instance
                   sort-by-car::sort-by-car<-preserves-assoc
                   (sort-by-car::valp formula-valp)
                   (sort-by-car::indexed-pair-p formula-pair-p)
                   (sort-by-car::car< car<)
                   (sort-by-car::sort-by-car< sort-by-car<)
                   (sort-by-car::sort-by-car<-merge sort-by-car<-merge)
                   (sort-by-car::sort-by-car<-list-p sort-by-car<-list-p)
                   (sort-by-car::sort-by-car<-ordered-p sort-by-car<-ordered-p)))))

(encapsulate
  ()

  (local
   (defthm hons-assoc-equal-is-assoc-equal
     (implies (alistp x)
              (equal (hons-assoc-equal key x)
                     (assoc-equal key x)))))

  (local
   (defthm rational-listp-strip-cars-formula
     (implies (formula-p formula)
              (rational-listp (strip-cars formula)))))

  (local
   (defthm alistp-sort-by-car<
     (implies (formula-p formula)
              (alistp (sort-by-car< formula)))))

  (defthm sort-by-car<-preserves-clauses
    (implies (and (formula-p formula)
                  (no-duplicatesp (strip-cars formula)))
             (equal (hons-assoc-equal index (sort-by-car< formula))
                    (hons-assoc-equal index formula)))))

(encapsulate
  ()

  (local
   (defthm no-duplicatesp-strip-cars-remove-deleted-clauses
     (implies (and (no-duplicatesp (strip-cars fal))
                   (no-duplicatesp (strip-cars acc))
                   (not (intersectp (strip-cars fal)
                                    (strip-cars acc))))
              (no-duplicatesp
               (strip-cars (remove-deleted-clauses fal acc))))))

  (defthm no-duplicatesp-shrink-fast-alist
    (implies (alistp fal)
             (no-duplicatesp (strip-cars (shrink-formula fal))))
    :hints (("Goal" :in-theory (e/d (shrink-formula) (fast-alist-clean))))))

(defthm clean-formula-preserves-clauses
  (implies (formula-p formula)
           (equal (hons-assoc-equal index (clean-formula formula))
                  (let ((pair (hons-assoc-equal index formula)))
                    (if (equal (cdr pair) *deleted-clause*)
                        nil
                      pair)))))

(defthm clean-formula-preserves-satisfiable-1
  (implies (formula-p formula)
           (implies (satisfiable (clean-formula formula))
                    (satisfiable formula)))
  :hints (("Goal"
           :expand
           ((satisfiable (sort-by-car< (shrink-formula formula)))
            (formula-truep
             formula
             (satisfiable-witness (sort-by-car< (shrink-formula formula)))))
           :use
           ((:instance satisfiable-suff
                       (assignment (satisfiable-witness
                                    (sort-by-car< (shrink-formula formula))))
                       (formula formula)))
           :restrict
           ((formula-truep-necc
             ((index
               (formula-truep-witness
                formula
                (satisfiable-witness (sort-by-car<
                                      (shrink-formula formula))))))))))
  :rule-classes nil)

(defthm clean-formula-preserves-satisfiable-2
  (implies (formula-p formula)
           (implies (satisfiable formula)
                    (satisfiable (clean-formula formula))))
  :hints (("Goal"
           :expand
           ((satisfiable formula)
            (formula-truep (sort-by-car< (shrink-formula formula))
                           (satisfiable-witness formula)))
           :use
           ((:instance satisfiable-suff
                       (assignment (satisfiable-witness formula))
                       (formula (sort-by-car< (shrink-formula formula)))))
           :restrict
           ((formula-truep-necc
             ((index
               (formula-truep-witness
                (sort-by-car< (shrink-formula formula))
                (satisfiable-witness formula))))))))
  :rule-classes nil)

(defthm clean-formula-preserves-satisfiable
  (implies (formula-p formula)
           (equal (satisfiable (clean-formula formula))
                  (satisfiable formula)))
  :hints (("Goal" :use (clean-formula-preserves-satisfiable-1
                        clean-formula-preserves-satisfiable-2))))
