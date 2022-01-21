; BV Lists Library: bvchop-list
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "../bv/bvchop")
(include-book "../typed-lists-light/all-integerp")
(include-book "all-unsigned-byte-p")
(include-book "unsigned-byte-listp")
(local (include-book "../lists-light/cons"))
(local (include-book "../lists-light/nth"))
(local (include-book "../lists-light/len"))

;; Apply BVCHOP with the indicated SIZE to every element in LST
;; TODO: This re-does the expt inside the bvchop over and over.
(defund bvchop-list-exec (size lst)
  (declare (type (integer 0 *) size)
           (xargs :guard (and (true-listp lst)
                              ;;(all-integerp lst)
                              )
                  :guard-hints (("Goal" :in-theory (enable all-integerp
                                                           )))))
  (if (atom lst)
      nil
    (cons (bvchop size (ifix (car lst)))
          (bvchop-list-exec size (cdr lst)))))

(defthm bvchop-list-exec-does-nothing-rewrite
  (implies (and (<= 0 size)
                (integerp size)
                (all-unsigned-byte-p size lst)
                (true-listp lst))
           (equal (bvchop-list-exec size lst)
                  lst))
  :hints (("Goal" :in-theory (enable bvchop-list-exec))))

;the use of :exec means this does not rebuild the list in the case when it would do nothing (may be very common, especially when this is called by bv-array-write)
;fixme or should bv-array-write just call this one?
(defund bvchop-list (size lst)
  (declare (type (integer 0 *) size)
           (xargs :guard (true-listp lst) ;(all-integerp lst) todo
                  :verify-guards nil ;done below
                  ))
  (mbe :logic (if (atom lst)
                  nil
                (cons (bvchop size (ifix (car lst)))
                      (bvchop-list size (cdr lst))))
       :exec (if (unsigned-byte-listp size lst)
                 lst
               (bvchop-list-exec size lst))))

(defthm bvchop-list-exec-becomes-bvchop-list
  (equal (bvchop-list-exec size lst)
         (bvchop-list size lst))
  :hints (("Goal" :in-theory (enable bvchop-list bvchop-list-exec))))

(defthm consp-of-bvchop-list
  (equal (consp (bvchop-list size lst))
         (consp lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(verify-guards bvchop-list
  :hints (("Goal" :in-theory (enable bvchop-list
                                     unsigned-byte-listp-rewrite))))

(defthm bvchop-list-of-cons
  (equal (bvchop-list size (cons a b))
         (cons (bvchop size a) (bvchop-list size b)))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-of-nil
  (equal (bvchop-list size nil)
         nil)
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm nth-of-bvchop-list
  (implies (natp i) ;todo
           (equal (nth i (bvchop-list esize data))
                  (if (< i (len data))
                      (bvchop esize (nth i data))
                    nil)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (bvchop-list
                            nth
                            len-of-cdr)
                           (nth-of-cdr)))))

(defthm len-of-bvchop-list
  (equal (len (bvchop-list size lst))
         (len lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-iff
  (iff (bvchop-list element-size lst)
       (true-list-fix lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthmd bvchop-list-of-take-of-bvchop-list
  (equal (bvchop-list size (take len (bvchop-list size lst)))
         (bvchop-list size (take len lst)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable take bvchop-list))))

(defthm bvchop-list-of-bvchop-list
  (equal (bvchop-list size (bvchop-list size lst))
         (bvchop-list size lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-does-nothing
  (implies (and (all-unsigned-byte-p size lst)
                (natp size)
                (true-listp lst))
           (equal (bvchop-list size lst)
                  lst))
  :hints (("Goal" :in-theory (enable bvchop-list all-unsigned-byte-p))))

(defthm all-unsigned-byte-p-of-bvchop-list
  (implies (natp size)
           (all-unsigned-byte-p size (bvchop-list size lst)))
  :hints (("Goal" :in-theory (enable bvchop-list all-unsigned-byte-p))))

(defthm true-listp-of-bvchop-list
  (true-listp (bvchop-list size lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm all-integerp-of-bvchop-list
  (all-integerp (bvchop-list width lst))
  :hints (("Goal" :in-theory (enable all-integerp bvchop-list))))

(defthm all-unsigned-byte-p-of-bvchop-list-gen
  (implies (and (<= element-size size)
                (natp size)
                (natp element-size))
           (all-unsigned-byte-p size
                                 (bvchop-list element-size lst)))
  :hints (("Goal" :in-theory (enable all-unsigned-byte-p bvchop-list))))

(defthm bvchop-list-of-append
  (equal (bvchop-list n (append lst1 lst2))
         (append (bvchop-list n lst1)
                 (bvchop-list n lst2)))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm take-of-bvchop-list
  (implies (<= n (len lst))
           (equal (take n (bvchop-list size lst))
                  (bvchop-list size (take n lst))))
  :hints (("Goal" :in-theory (enable take bvchop-list))))

;improve: see the -better version nthcdr-of-bvchop-list
(defthm nthcdr-of-bvchop-list
  (implies (and (<= n (len lst))
                (natp n))
           (equal (nthcdr n (bvchop-list size lst))
                  (bvchop-list size (nthcdr n lst))))
  :hints (("Goal" :in-theory (e/d (nthcdr bvchop-list) (ifix)))))

(defthm cdr-of-bvchop-list
  (equal (cdr (bvchop-list size lst))
         (bvchop-list size (cdr lst)))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm car-of-bvchop-list
  (equal (car (bvchop-list size lst))
         (if (consp lst)
             (bvchop size (car lst))
           nil))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-of-take
  (implies (<= n (len lst))
           (equal (bvchop-list esize (take n lst))
                  (take n (bvchop-list esize lst))))
  :hints (("Goal" :in-theory (enable bvchop-list take))))

;which rule do we want?
(in-theory (disable bvchop-list-of-take))

(theory-invariant (incompatible (:rewrite bvchop-list-of-take) (:rewrite take-of-bvchop-list)))

;yuck?! this is an opener rule
;may cause problems in later proofs
(defthmd bvchop-list-when-consp
  (implies (consp x)
           (equal (bvchop-list size x)
                  (cons (bvchop size (car x))
                        (bvchop-list size (cdr x)))))
  :hints (("Goal" :in-theory (enable bvchop-list))))

;slow?
;improve
(defthm nthcdr-of-bvchop-list-better
  (equal (nthcdr n (bvchop-list size lst))
         (if (natp n)
             (bvchop-list size (nthcdr n lst))
           (bvchop-list size lst)))
  :hints (("Goal" :in-theory (enable nthcdr bvchop-list))))

(defthmd bvchop-list-of-nthcdr
  (equal (bvchop-list width (nthcdr n lst))
         (nthcdr n (bvchop-list width lst)))
  :hints (("Goal" :in-theory (enable nthcdr-of-bvchop-list-better))))

(theory-invariant (incompatible (:rewrite nthcdr-of-bvchop-list) (:rewrite bvchop-list-of-nthcdr)))
(theory-invariant (incompatible (:rewrite nthcdr-of-bvchop-list-better) (:rewrite bvchop-list-of-nthcdr)))

(defthm bvchop-list-of-true-list-fix
  (equal (bvchop-list element-size (true-list-fix lst))
         (bvchop-list element-size lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-when-arg1-is-not-an-integer
  (implies (not (integerp arg))
           (equal (bvchop-list arg lst)
                  (bvchop-list 0 lst)))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-when-arg1-is-negative
  (implies (< arg 0)
           (equal (bvchop-list arg lst)
                  (bvchop-list 0 lst)))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-of-true-list-fix
  (equal (bvchop-list element-size (true-list-fix lst))
         (bvchop-list element-size lst))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm equal-of-true-list-fix-and-bvchop-list-same
  (implies (natp size)
           (equal (equal (true-list-fix x)
                         (bvchop-list size x))
                  (all-unsigned-byte-p size x)))
  :hints (("Goal" :in-theory (enable bvchop-list))))

(defthm bvchop-list-when-unsigned-byte-listp
  (implies (and (unsigned-byte-listp size lst)
                (natp size)
                (true-listp lst))
           (equal (bvchop-list size lst)
                  lst))
  :hints (("Goal" :in-theory (enable bvchop-list all-unsigned-byte-p))))

(defthm unsigned-byte-listp-of-bvchop-list
  (implies (natp size)
           (unsigned-byte-listp size (bvchop-list size lst)))
  :hints (("Goal" :in-theory (enable unsigned-byte-listp-rewrite))))
