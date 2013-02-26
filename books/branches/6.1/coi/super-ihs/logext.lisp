#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#
(in-package "ACL2")

;make the inclusion of arithmetic stuff local?
(include-book "ihs/ihs-lemmas" :dir :system)
(local (include-book "arithmetic"))
(include-book "logbitp")
(include-book "logapp")
(include-book "loghead")
;(include-book "ash")

(defthm logext-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logext size i)
                  0))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthm logext-when-i-is-zero
  (equal (logext size 0) 
         0)
  :hints (("goal" :in-theory (e/d (logext 
                                   logapp 
                                   ) 
                                  (LOGAPP-0)))))

(defthm logext-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (logext size i)
                  (logext 1 (logcar i))
                  ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :cases ((acl2-numberp size))
           :in-theory (enable logext))))

;rhs?
(defthm logext-when-size-is-0
  (equal (logext 0 i) 
         (if (equal (logcar i) 0)
             0
           -1))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-when-size-is-non-positive
  (implies (<= size 0)
           (equal (logext size i)
                  (logext 1 (logcar i))
                  ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logext))))

(DEFTHM LOGEXT*-better
  (IMPLIES (AND (INTEGERP SIZE)
                (> SIZE 0)
     ;(INTEGERP I)
                )
           (EQUAL (LOGEXT SIZE I)
                  (COND ((EQUAL SIZE 1)
                         (IF (EQUAL (LOGCAR I) 0) 0 -1))
                        (T (LOGCONS (LOGCAR I)
                                    (LOGEXT (1- SIZE) (LOGCDR I)))))))
  :RULE-CLASSES
  ((:DEFINITION :CLIQUE (LOGEXT)
                :CONTROLLER-ALIST ((LOGEXT T T))))
  :hints (("Goal" :use (:instance LOGEXT*)
           :in-theory (disable LOGEXT*))))

(defthm evenp-of-logext
  (implies (and (integerp n)
                (<= 0 n))
           (equal (evenp (logext n x))
                  (evenp (ifix x))))
  :hints (("Goal" :in-theory (e/d (logext) 
                                  (evenp loghead)))))

(defthm equal-logext-0
  (implies (and; (integerp x)
                (integerp n)
                (< 0 n))
           (equal (equal (logext n x) 0)
                  (equal (loghead n x) 0))))

(defthm equal-logext-minus-1
  (implies (and; (integerp x)
                (integerp n)
                (< 0 n))
           (equal (equal (logext n x) -1)
                  (equal (loghead n x) (loghead n -1))))
  :hints (("goal" :in-theory (enable))))

(defthm logext-does-nothing-rewrite
  (implies (and (integerp n)
                (< 0 n))
           (equal (equal (logext n x) x)
                  (signed-byte-p n x))))

(defthm logext-+-logext-better
  (equal (logext size (+ i (logext size j)))
         (logext size (+ i (ifix j))))
  :hints (("Goal" :use (:instance logext-+-logext (i (fix i)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d () ( logext-+-logext)))))

(in-theory (disable LOGEXT-+-LOGEXT))

