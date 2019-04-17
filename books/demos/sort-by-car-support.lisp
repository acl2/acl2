; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann, May 2017
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See sort-by-car.lisp, which in particular has a sort of apology for the lack
; of more structure in the present file.  Here we prove the lemma,
; sort-by-car<-preserves-assoc.

; Portcullis command:
#||
(defpkg "SORT-BY-CAR"
  (union$
   *acl2-exports*
   *common-lisp-symbols-from-main-lisp-package*
   :test 'eq))
||#

(in-package "SORT-BY-CAR")

(include-book "defsort/defsort" :dir :system)

(encapsulate
  ( ((valp *) => *) )
  (local (defun valp (x) (consp x)))
  (defthm booleanp-valp
    (booleanp (valp x))
    :rule-classes :type-prescription))

(encapsulate
  ( ((indexp *) => *) )
  (local (defun indexp (x) (rationalp x)))

; The following property supports guard verification for car<.

  (defthm indexp-implies-rationalp
    (implies (indexp x)
             (rationalp x))
    :rule-classes :compound-recognizer))

(defun indexed-pair-p (x)
  (declare (xargs :guard t))
  (and (consp x)
       (indexp (car x))
       (valp (cdr x))))

(defun car< (x y)
  (declare (xargs :guard (and (indexed-pair-p x)
                              (indexed-pair-p y))))
  (< (car x) (car y)))

(acl2::defsort sort-by-car<
  :compare< car<
  :comparablep indexed-pair-p
  :true-listp t
  :weak t)

; Start proof of sort-by-car<-preserves-assoc

; Since defsort proves that sorting preserves acl2::duplicity (here, lemma
; sort-by-car<-sort-preserves-duplicity), we can prove that membership is
; preserved by sorting (lemma member-sort-by-car< below).  Then
; sort-by-car<-preserves-assoc follows, if we can prove that assoc agrees for
; alists with the same members assuming that at last one of those alists has no
; duplicate keys.

(defthm same-duplicity-implies-same-member
  (implies (iff (equal (acl2::duplicity a x) 0)
                (equal (acl2::duplicity a y) 0))
           (iff (member a x)
                (member a y)))
  :hints (("Goal" :in-theory (enable acl2::duplicity)))
  :rule-classes nil)

(defthm member-sort-by-car<
  (iff (member pair (sort-by-car< alist))
       (member pair alist))
  :hints (("Goal"
           :use
           ((:instance same-duplicity-implies-same-member
                       (a pair)
                       (x (sort-by-car< alist))
                       (y alist))))))

(defthm member-strip-cars
  (implies (member pair alist)
           (member (car pair)
                   (strip-cars alist))))

(defthmd member-implies-assoc
  (implies (and (member pair alist)
                (no-duplicatesp (strip-cars alist)))
           (equal (assoc (car pair) alist)
                  pair)))

(defthmd assoc-implies-member
  (implies (assoc index alist)
           (member (assoc index alist) alist)))

; Start proof of no-duplicatesp-strip-cars-sort-by-car< Idea of proof: If
; sort-by-car< has duplicate keys then let pair1 and pair2 both have the same
; car.  So pair1 and pair2 are both in alist, so it has duplicate keys, too.

(defun other-assoc-pair (alist)
  (cond ((endp alist) nil)
        (t (let* ((pair (car alist))
                  (key (and (consp pair)
                            (car pair))))
             (or (assoc key (cdr alist))
                 (other-assoc-pair (cdr alist)))))))

(encapsulate
  ()
  (local (defthm member-strip-cars-rewrite
           (implies (alistp alist)
                    (iff (member key (strip-cars alist))
                         (assoc key alist)))))

  (defthm not-no-duplicatesp-strip-cars-iff-other-assoc-pair
    (implies (alistp alist)
             (iff (no-duplicatesp (strip-cars alist))
                  (not (other-assoc-pair alist))))))

(encapsulate
  ()

  (local (defthm alistp-sort-by-car<-merge
           (implies (and (alistp alist1)
                         (alistp alist2))
                    (alistp (sort-by-car<-merge alist1 alist2)))
           :hints (("Goal" :in-theory (enable sort-by-car<-merge)))))

  (local (defthm alistp-revappend
           (implies (alistp x)
                    (equal (alistp (revappend x y))
                           (alistp y)))))

; Mihir M. mod, 04/2019: Adapt to the new definition of take.
  (local (defthm alistp-of-take
           (implies (and (alistp x)
                         (<= n (len x)))
                    (alistp (take n x)))))

  (local (include-book "arithmetic-5/top" :dir :system))

  (local (defthm alistp-nthcdr
           (implies (alistp x)
                    (alistp (nthcdr n x)))))

  (defthm alistp-sort-by-car<
    (implies (alistp alist)
             (alistp (sort-by-car< alist)))
    :hints (("Goal" :in-theory (enable sort-by-car<))))
  )

(defthmd other-assoc-pair-member
  (implies (and (alistp alist)
                (other-assoc-pair alist))
           (member (other-assoc-pair alist) alist))
  :hints (("Goal" :in-theory (enable assoc-implies-member))))

(defthm listp-other-assoc-pair
  (implies (force (alistp alist))
           (or (null (other-assoc-pair alist))
               (consp (other-assoc-pair alist))))
  :rule-classes :type-prescription)

(defthm two-members-implies-other-assoc-pair
  (implies (and (alistp alist)
                (member-equal pair1 alist)
                (member-equal pair2 alist)
                (equal (car pair1) (car pair2))
                (not (equal pair1 pair2)))
           (other-assoc-pair alist)))

(defthmd member-implies-member-assoc
  (implies (member pair alist)
           (member (assoc-equal (car pair) alist)
                   alist)))

(defthm car-assoc
  (implies (assoc index alist)
           (equal (car (assoc index alist))
                  index)))

(defthm car-member
  (implies (member a x)
           (equal (car (member a x))
                  a)))

(defthm member-implies-assoc-car
  (implies (and (alistp alist)
                (member pair alist))
           (assoc (car pair) alist)))

; Start (or continue?) proof of other-assoc-pair-is-not-assoc

(encapsulate
  ()

  (local (defthm other-assoc-pair-implies-assoc
           (implies
            (and (alistp alist)
                 (other-assoc-pair alist)
                 (no-duplicatesp alist)
                 (equal index (car (other-assoc-pair alist))))
            (assoc index alist))))

  (local (defthm assoc-implies-member-alt
           (implies (and (equal (assoc-equal (car pair) alist)
                                pair)
                         pair)
                    (member pair alist))
           :hints (("Goal" :in-theory (enable assoc-implies-member)))))

  (defthm other-assoc-pair-is-not-assoc
    (implies (and (alistp alist)
                  (other-assoc-pair alist)
                  (no-duplicatesp alist))
             (not (equal (other-assoc-pair alist)
                         (assoc-equal (car (other-assoc-pair alist))
                                      alist)))))
  )

(defthm no-duplicatesp-strip-cars-sort-by-car<-lemma
  (implies (and (alistp alist)
                (no-duplicatesp alist)
                (no-duplicatesp (strip-cars alist)))
           (no-duplicatesp (strip-cars (sort-by-car< alist))))
  :hints (("Goal"
           :use ((:instance other-assoc-pair-member
                            (alist (sort-by-car< alist)))
                 (:instance member-implies-member-assoc
                            (pair (other-assoc-pair (sort-by-car< alist)))
                            (alist (sort-by-car< alist))))
           :cases ((member (assoc (car (other-assoc-pair (sort-by-car< alist)))
                                  (sort-by-car< alist))
                           (sort-by-car< alist))))))

(defthm no-duplicatesp-strip-cars-implies-no-duplicatesp
  (implies (no-duplicatesp (strip-cars alist))
           (no-duplicatesp alist)))

(defthm no-duplicatesp-strip-cars-sort-by-car<
  (implies (and (alistp alist)
                (no-duplicatesp (strip-cars alist)))
           (no-duplicatesp (strip-cars (sort-by-car< alist))))
  :hints (("Goal"
           :in-theory
           (disable not-no-duplicatesp-strip-cars-iff-other-assoc-pair))))

(defthm car-assoc
  (implies (assoc index alist)
           (equal (car (assoc index alist))
                  index)))

(defthm sort-by-car<-preserves-assoc-1
  (implies (and (alistp alist)
                (no-duplicatesp (strip-cars alist))
                (assoc index (sort-by-car< alist)))
           (equal (assoc index (sort-by-car< alist))
                  (assoc index alist)))
  :hints (("Goal"
           :use
           ((:instance assoc-implies-member
                       (alist (sort-by-car< alist)))
            (:instance member-implies-assoc
                       (pair (assoc-equal index (sort-by-car< alist)))
                       (alist alist)))))
  :rule-classes nil)

(defthm sort-by-car<-preserves-assoc-2
  (implies (and (alistp alist)
                (no-duplicatesp (strip-cars alist))
                (assoc index alist))
           (equal (assoc index (sort-by-car< alist))
                  (assoc index alist)))
  :hints (("Goal"
           :use
           ((:instance assoc-implies-member
                       (alist alist))
            (:instance member-implies-assoc
                       (pair (assoc-equal index alist))
                       (alist (sort-by-car< alist))))))
  :rule-classes nil)

(defthm sort-by-car<-preserves-assoc
  (implies (and (alistp alist)
                (no-duplicatesp (strip-cars alist)))
           (equal (assoc index (sort-by-car< alist))
                  (assoc index alist)))
  :hints (("Goal" :use (sort-by-car<-preserves-assoc-1
                        sort-by-car<-preserves-assoc-2))))
