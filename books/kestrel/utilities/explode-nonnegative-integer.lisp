; A lightweight book about explode-nonnegative-integer
;
; Copyright (C) 2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "digit-to-char"))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/lists-light/true-list-fix" :dir :system))

(in-theory (disable explode-nonnegative-integer))

(local (in-theory (disable floor mod print-base-p)))

;; Could move to a separate book
(defthm print-base-p-forward
  (implies (print-base-p print-base)
           (and (integerp print-base)
                (<= 2 print-base)
                (<= print-base 16)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable print-base-p))))

(defthm true-listp-of-explode-nonnegative-integer
  (equal (true-listp (explode-nonnegative-integer n print-base ans))
         (true-listp ans))
  :hints (("Goal" :in-theory (enable explode-nonnegative-integer))))

(defthm consp-of-explode-nonnegative-integer-type
  (implies (true-listp ans)
           (consp (explode-nonnegative-integer n print-base ans)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable explode-nonnegative-integer))))

(defthm explode-nonnegative-integer-type2
  (explode-nonnegative-integer n print-base ans)
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable explode-nonnegative-integer))))

(defthm <=-of-len-of-explode-nonnegative-integer-linear
  (<= (len ans)
      (len (explode-nonnegative-integer n print-base ans)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable explode-nonnegative-integer))))

(defthm equal-of-singleton-0-and-explode-nonnegative-integer
  (equal (equal '(#\0) (explode-nonnegative-integer n print-base ans))
         (and (or (zp n)
                  (not (print-base-p print-base)))
              (or (null ans)
                  (equal ans '(#\0)))))
  :hints (("Goal" :in-theory (enable explode-nonnegative-integer))))

(defthm equal-of-len-of-explode-nonnegative-integer-and-len
  (equal (equal (len ans) (len (explode-nonnegative-integer n print-base ans)))
         (and (or (zp n)
                  (not (print-base-p print-base)))
              (equal (explode-nonnegative-integer n print-base ans)
                     ans)))
  :hints (("Goal" :in-theory (enable explode-nonnegative-integer))))

(defthm not-equal-of-explode-when-too-short
  (implies (< (len x) (len ans))
           (not (equal x (explode-nonnegative-integer n print-base ans)))))

(defthm equal-of-explode-nonnegative-integer-same
  (equal (equal ans (explode-nonnegative-integer n print-base ans))
         (and (or (zp n)
                  (not (print-base-p print-base)))
              (not (null ans))))
  :hints (("Goal" :in-theory (enable explode-nonnegative-integer))))

(local
 (defun explode-nonnegative-integer-double-induct (n1 n2 print-base ans1 ans2)
   (declare (xargs :hints (("Goal" :in-theory (e/d (member-equal) (floor))))))
   (cond ((or (zp n1)
              (not (print-base-p print-base)))
          (list n1 n2 print-base ans1 ans2))
         (t (explode-nonnegative-integer-double-induct
             (floor n1 print-base)
             (floor n2 print-base)
             print-base
             (cons (digit-to-char (mod n1 print-base))
                   ans1)
             (cons (digit-to-char (mod n2 print-base))
                   ans2))))))

;; explode-nonnegative-integer is essentially injective
(defthm equal-of-explode-nonnegative-integer-and-explode-nonnegative-integer
  (implies (equal (len ans1) (len ans2))
           (equal (equal (explode-nonnegative-integer n1 print-base ans1)
                         (explode-nonnegative-integer n2 print-base ans2))
                  (and (equal ans1 ans2)
                       (or (not (print-base-p print-base))
                           (equal (nfix n1) (nfix n2))))))
  :hints (("Goal" :induct (explode-nonnegative-integer-double-induct n1 n2 print-base ans1 ans2)
           :expand ((explode-nonnegative-integer n1 print-base ans1)
                    (explode-nonnegative-integer n2 print-base ans))
           :in-theory (e/d (explode-nonnegative-integer zp equal-when-equal-of-floors-and-equal-of-mods)
                           (floor)))))
