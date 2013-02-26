#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;bzo many of the rules below suggest analogous logbitp rules.  Someone should
;try to add those rules to logbitp.lisp.  And vice-versa!

(include-book "ihs/ihs-lemmas" :dir :system)
(local (include-book "arithmetic"))
;(include-book "ash")

(defthm logbit-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logbit pos i) 
                  0))
  :hints
  (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-zero
  (equal (logbit pos 0)
         0)
  :hints (("Goal" :in-theory (enable logbit))))

;go the other way too?
(defthm logbitp-forward-to-logbit-one
  (implies (logbitp n x)
           (equal 1 (logbit n x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbitp-forward-to-logbit-zero
  (implies (not (logbitp n x))
           (equal 0 (logbit n x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-when-i-is-non-positive
  (implies (<= i 0)
           (equal (logbit i j)
                  (logcar j)))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-logbit
  (equal (logbit pos1 (logbit pos2 i))
         (if (zp pos1)
             (logbit pos2 i)
           0))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-one
  (equal (logbit pos 1) 
         (if (zp pos)
             1
           0))
  :hints (("Goal" :cases ((zp pos))
           :in-theory (enable logbit))))

(defthm unsigned-byte-p-of-logbit
  (implies (< 0 n)
           (equal (unsigned-byte-p n (logbit pos i))
                  (integerp n)))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm unsigned-byte-p-of-logbit-fw
  (unsigned-byte-p 1 (logbit pos i))
  :rule-classes ((:forward-chaining :trigger-terms ((logbit pos i)))))
