; The inverse of the function GROUP
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/typed-lists-light/items-have-len" :dir :system)
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "nth"))
(local (include-book "nthcdr"))
(local (include-book "len"))
(local (include-book "cdr"))
(local (include-book "cons"))
(local (include-book "append"))
(local (include-book "take"))
(local (include-book "kestrel/library-wrappers/arithmetic-inequalities" :dir :system))

;move
(defthm multiple-when-<=
  (implies (and (<= m n)
                (posp m)
                (posp n))
           (equal (integerp (* m (/ n)))
                  (equal m n)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil nil)))
  :hints (("Goal" :in-theory (enable DIVISIBILITY-IN-TERMS-OF-FLOOR))))

;the n here is mostly so we don't have to rediscover it later?
(defund ungroup (n x)
  (declare (xargs :guard (and (posp n)
                              (true-listp x)
                              (true-list-listp x)
                              (items-have-len n x))))
  (if (endp x)
      nil
    (append (take n (car x))
            (ungroup n (cdr x)))))

(defthm true-listp-of-ungroup
  (true-listp (ungroup n x)))

(defthm ungroup-of-true-list-fix
  (equal (ungroup n (true-list-fix x))
         (ungroup n x))
  :hints (("Goal" :in-theory (enable ungroup))))

(defun ungroup-induct (x n m)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n)
          (not (posp m)))
      (list x n m)
    (ungroup-induct (cdr x) (- n m) m)))

(defthm car-of-ungroup
  (implies (posp n)
           (equal (car (ungroup n x))
                  (if (endp x)
                      nil
                    (car (car x)))))
  :hints (("Goal" :in-theory (enable ungroup))))

(defthm take-of-ungroup
  (implies (and (equal 0 (mod m n))
                (<= m (* n (len x)))
                (posp n)
                (natp m))
           (equal (take m (ungroup n x))
                  (ungroup n (take (floor m n) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :induct (ungroup-induct x m n)
           :expand ((NTH 1 X)
                    (NTH 0 (CDR X))
                    (UNGROUP N (TAKE (* M (/ N)) X)))
           :in-theory (e/d (natp ungroup ;take
                                 len-of-cdr
                                 CDR-OF-TAKE
                                 )
                           (;CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER
                            ;SUBRANGE-OF-APPEND
                            DIVISIBILITY-IN-TERMS-OF-FLOOR
                            ;TAKE-OF-CDR-BECOMES-SUBRANGE
                            ;NTH-OF-CDR LIST::NTH-OF-CDR ;fixme are these two the same?
;LIST::EQUAL-APPEND-REDUCTION!
                            )))))

(defthm consp-of-ungroup
  (implies (posp n)
           (equal (consp (ungroup n x))
                  (consp x)))
  :hints (("Goal" :in-theory (enable ungroup))))

(defthm len-of-ungroup
  (implies (posp n)
           (equal (len (ungroup n x))
                  (* n (len x))))
  :hints (("Goal" :in-theory (enable ungroup))))

(defthm nthcdr-of-ungroup
  (implies (and (equal 0 (mod n m))
                (natp n)
                (posp m))
           (equal (nthcdr n (ungroup m x))
                  (ungroup m (nthcdr (floor n m) x))))
  :hints (("Goal" :induct (ungroup-induct x n m)
           :in-theory (enable posp ungroup)
           :do-not '(generalize eliminate-destructors))))

(defthm nth-of-ungroup
  (implies (and (< n (* size (len x))) ;move to conclusion?
                (posp size)
                (natp n))
           (equal (nth n (ungroup size x))
                  (nth (mod n size)
                       (nth (floor n size)
                            x))))
  :hints (("Goal"
           :induct (ungroup-induct x n size)
           :in-theory (enable nth-of-0 ungroup len-of-cdr mod-sum-cases)
           :do-not '(generalize eliminate-destructors))))

(defthm nth-of-ungroup-gen
  (implies (and (posp size)
                (natp n))
           (equal (nth n (ungroup size x))
                  (if (< n (* size (len x)))
                      (nth (mod n size)
                           (nth (floor n size)
                                x))
                    nil)))
  :hints (("Goal" :in-theory (enable nth-when-<=-len))))
