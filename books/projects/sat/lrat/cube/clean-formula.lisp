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

(include-book "defsort/defsort" :dir :system)

(defun formula-pair-p (pair)
  (declare (xargs :guard t))
  (and (consp pair)
       (posp (car pair))
       (let ((val (cdr pair)))
         (or (deleted-clause-p val)
             (clause-or-assignment-p val)))))

#||
(defun indexed-pair-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (rationalp (car x))))

(defun car< (x y)
  (declare (xargs :guard (and (indexed-pair-p x)
                              (indexed-pair-p y))))
  (< (car x) (car y)))
||#

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

; Start proof of sort-by-car<-preserves-clauses

(defthm formula-p-revappend
  (implies (and (formula-p f1)
                (formula-p f2))
           (formula-p (revappend f1 f2))))

(defthm formula-p-first-n-ac
  (implies (and (formula-p f1)
                (formula-p f2)
                (<= n (len f1)))
           (formula-p (first-n-ac n f1 f2))))

(local (in-theory (disable floor)))

(local (include-book "arithmetic-5/top" :dir :system))

(defthm formula-p-nthcdr
  (implies (formula-p x)
           (formula-p (nthcdr n x))))

(defthm hons-assoc-equal-implies-member-equal-strip-cars
  (implies (hons-assoc-equal a x)
           (member-equal a (strip-cars x))))

(defthm hons-assoc-equal-sort-by-car<-merge
  (implies (and (formula-p x)
                (formula-p y)
                (force (not (intersectp (strip-cars x) (strip-cars y)))))
           (equal (hons-assoc-equal index (sort-by-car<-merge x y))
                  (or (hons-assoc-equal index x)
                      (hons-assoc-equal index y))))
  :hints (("Goal" :in-theory (enable sort-by-car<-merge))))

(defthm no-duplicatesp-strip-cars-remove-deleted-clauses
    (implies (and (no-duplicatesp (strip-cars fal))
                  (no-duplicatesp (strip-cars acc))
                  (not (intersectp (strip-cars fal)
                                   (strip-cars acc))))
             (no-duplicatesp (strip-cars (remove-deleted-clauses fal acc)))))

(defthm no-duplicatesp-shrink-fast-alist
  (implies (alistp fal)
           (no-duplicatesp (strip-cars (shrink-formula fal))))
  :hints (("Goal" :in-theory (e/d (shrink-formula) (fast-alist-clean)))))

(defthm no-duplicatesp-revappend
  (implies (and (no-duplicatesp (strip-cars x))
                (no-duplicatesp (strip-cars y))
                (not (intersectp (strip-cars x)
                                 (strip-cars y))))
           (no-duplicatesp (strip-cars (revappend x y)))))

(defthm no-duplicatesp-strip-cars-first-n-ac
  (implies (and (no-duplicatesp (strip-cars x))
                (no-duplicatesp (strip-cars y))
                (not (intersectp (strip-cars x)
                                 (strip-cars y)))
                (natp n)
                (<= n (len x)))
           (no-duplicatesp (strip-cars (first-n-ac n x y)))))

(defthm hons-assoc-equal-revappend
  (implies (and (no-duplicatesp (strip-cars x))
                (no-duplicatesp (strip-cars y))
                (not (intersectp (strip-cars x)
                                 (strip-cars y))))
           (equal (hons-assoc-equal index (revappend x y))
                  (or (hons-assoc-equal index x)
                      (hons-assoc-equal index y))))
  :hints (("Goal" :induct (revappend x y))))

(defthm hons-assoc-equal-both-implies-intersectp-strip-cars
  (implies (and (hons-assoc-equal index x)
                (hons-assoc-equal index y))
           (intersectp (strip-cars x) (strip-cars y))))

(defthm hons-assoc-equal-first-n-ac
  (implies (and (no-duplicatesp (strip-cars x))
                (no-duplicatesp (strip-cars y))
                (not (intersectp (strip-cars x)
                                 (strip-cars y)))
                (natp n)
                (<= n (len x))
                (hons-assoc-equal index (first-n-ac n x y)))
           (equal (hons-assoc-equal index (first-n-ac n x y))
                  (or (hons-assoc-equal index x)
                      (hons-assoc-equal index y))))
  :hints (("Goal" :induct (first-n-ac n x y))))

(skip-proofs
(defthm sort-by-car<-preserves-clauses
  (implies (and (formula-p formula)
                (no-duplicatesp (strip-cars formula)))
           (equal (hons-assoc-equal index (sort-by-car< formula))
                  (hons-assoc-equal index formula)))
  :hints (("Goal"
           :in-theory (e/d (sort-by-car<) (floor))
           :induct t)))
)

(defthm clean-formula-preserves-clauses
  (implies (formula-p formula)
           (equal (hons-assoc-equal index (clean-formula formula))
                  (let ((pair (hons-assoc-equal index formula)))
                    (if (equal (cdr pair) *deleted-clause*)
                        nil
                      pair)))))
