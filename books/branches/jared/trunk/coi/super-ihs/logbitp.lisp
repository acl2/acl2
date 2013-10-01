#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;bzo many of the rules below suggest analogous logbit rules.  Someone should
;try to add those rules to logbit.lisp.  And vice-versa!

(include-book "ihs/ihs-lemmas" :dir :system)
(local (include-book "arithmetic"))
;(include-book "ash")

(in-theory (disable logbitp))

(defthm logbitp-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logbitp i j)
                  nil))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-when-j-is-zero
  (equal (logbitp i 0)
         nil)
  :hints (("goal" :in-theory (enable logbitp ifix))))

(defthm logbitp-when-i-is-zero
  (equal (logbitp 0 j) 
         (equal (logcar j) 1))
  :hints (("goal" :in-theory (enable logbit logbitp))))

;further simplify the RHS?
(defthm logbitp-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logbitp i j)
                  (logbitp 0 j)))
  :hints (("Goal" :in-theory (enable logbitp
                                     ;oddp-rewrite-to-logcar-fact
                                     ))))

(defthm logbitp-when-i-is-non-positive
  (implies (<= i 0)
           (equal (logbitp i j)
                  (not (equal 0 (logcar j)))))
  :hints (("Goal" :in-theory (enable logbitp)
           :do-not '(generalize eliminate-destructors)
           )))

(defthm logbitp-0-minus-1-better-1
  (equal (logbitp pos 0)
         nil)
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-0-minus-1-better-2
  (equal (logbitp pos -1)
         t)
  :hints (("Goal" :in-theory (enable logbitp))))

(in-theory (disable LOGBITP-0-MINUS-1))


;rule for logbit?
(defthm logbitp-of-one
  (equal (logbitp pos 1)
         (zp pos))
  :hints (("Goal" :cases ((zp pos))
           :in-theory (enable logbitp))))

;bzo gen
(defthm logbitp-of-expt-hack
  (implies (and (integerp size) (<= 0 size))
           (logbitp size (expt 2 size)))
  :hints (("Goal" :in-theory (enable logbitp))))
