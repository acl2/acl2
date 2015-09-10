; RTL - A Formal Theory of Register-Transfer Logic and Computer Arithmetic
; Copyright (C) 1995-2013 Advanced Mirco Devices, Inc.
;
; Contact:
;   David Russinoff
;   1106 W 9th St., Austin, TX 78703
;   http://www.russsinoff.com/
;
; See license file books/rtl/rel9/license.txt.
;
; Author: David M. Russinoff (david@russinoff.com)

(in-package "ACL2")

(include-book "cat-def")


(local ; ACL2 primitive
 (defun natp (x)
   (declare (xargs :guard t))
   (and (integerp x)
        (<= 0 x))))

(defund bvecp (x k)
  (declare (xargs :guard (integerp k)))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 k))))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

(defund setbits (x w i j y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp i)
                              (integerp j)
                              (<= 0 j)
                              (<= j i)
                              (integerp w)
                              (< i w))
                  :verify-guards nil))
  (mbe :logic (cat (bits x (1- w) (1+ i))
                   (+ -1 w (- i))
                   (cat (bits y (+ i (- j)) 0)
                        (+ 1 i (- j))
                        (bits x (1- j) 0)
                        j)
                   (1+ i))
       :exec  (cond ((int= j 0)
                     (cond ((int= (1+ i) w)
                            (bits y (+ i (- j)) 0))
                           (t
                            (cat (bits x (1- w) (1+ i))
                                 (+ -1 w (- i))
                                 (bits y (+ i (- j)) 0)
                                 (1+ i)))))
                    ((int= (1+ i) w)
                     (cat (bits y (+ i (- j)) 0)
                          (+ 1 i (- j))
                          (bits x (1- j) 0)
                          j))
                    (t
                     (cat (bits x (1- w) (1+ i))
                          (+ -1 w (- i))
                          (cat (bits y (+ i (- j)) 0)
                               (+ 1 i (- j))
                               (bits x (1- j) 0)
                               j)
                          (1+ i))))))

(local (include-book "setbits"))
(local (include-book "../../arithmetic/top"))
(local (include-book "bits"))
(local (include-book "cat"))

(defund setbitn (x w n y)
  (declare (xargs :guard (and (natp x)
                              (natp y)
                              (integerp n)
                              (<= 0 n)
                              (integerp w)
                              (< n w))
                  :verify-guards nil))
  (setbits x w n n y))

(defthm setbitn-nonnegative-integer-type
  (and (integerp (setbitn x w n y))
       (<= 0 (setbitn x w n y)))
  :hints (("Goal" :in-theory (enable setbitn)))
  :rule-classes (:type-prescription)
  )

;this rule is no better than setbits-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription setbitn)))

(defthm setbitn-natp
  (natp (setbitn x w n y)))

;add setbitn-bvecp-simple?

(defthm setbitn-bvecp
  (implies (and (<= w k)
                (case-split (integerp k)))
           (bvecp (setbitn x w n y) k))
  :hints (("goal" :in-theory (enable setbitn))))

(defthm setbitn-rewrite
  (implies (syntaxp (quotep n))
           (equal (setbitn x w n y)
                  (setbits x w n n y)))
  :hints (("Goal" :in-theory (enable setbitn))))

;gen?
(defthm bitn-setbitn
  (implies (and (case-split (bvecp y 1))
                (case-split (< 0 w))
                (case-split (< n w))
                (case-split (< k w))
                (case-split (<= 0 k))
                (case-split (integerp w))
                (case-split (integerp n))
                (<= 0 n)
                (case-split (integerp k))
                )
           (equal (bitn (setbitn x w n y) k)
                  (if (equal n k)
                      y
                    (bitn x k))))
  :hints (("Goal" :cases ((< n k) (= n k))
           :in-theory (enable setbitn bitn bits-does-nothing)))
  )



(defthm setbitn-setbitn
  (implies (and (case-split (<= 0 n))
                (case-split (< n w))
                (case-split (integerp w))
                (case-split (integerp n))
                )
           (equal (setbitn (setbitn x w n y) w n y2)
                  (setbitn x w n y2)))
  :hints (("Goal"
           :in-theory (enable setbits setbitn natp)))
  )

(defthm setbitn-does-nothing
  (implies (and (case-split (<= 0 n))
                (case-split (< n w))
                (case-split (integerp w))
                (case-split (integerp n))
                )
           (equal (setbitn x w n (bitn x n))
                  (bits x (1- w) 0))
           )
  :hints (("Goal" :cases ((< (+ -1 W) (+ 1 N)))
           :in-theory (enable bitn setbits setbitn natp)))
  )

#|
;bad name?
(defthm setbitn-commutativity
  (implies (and (< n n2);(not (equal n n2))
                (case-split (<= 0 n))
                (case-split (<= 0 n2))
                (case-split (< n w))
                (case-split (< n2 w))
                (case-split (integerp w))
                (case-split (integerp n))
                (case-split (integerp n2))
                (case-split (bvecp y 1))
                (case-split (bvecp y2 1))
                (case-split (bvecp x w)) ;drop!
)
           (equal (setbitn (setbitn x w n y) w n2 y2)
                  (setbitn (setbitn x w n2 y2) w n y)
))
  :rule-classes ((:rewrite :loop-stopper ((n n2 s))))
  :hints (("Goal"
           :in-theory (enable setbitn setbits-rewrite setbits-rewrite-when-j-is-0)))
  )


(defthm setbitn-commutativity
  (implies (and (< n n2);(not (equal n n2))
                (case-split (<= 0 n))
                (case-split (<= 0 n2))
                (case-split (< n w))
                (case-split (< n2 w))
                (case-split (integerp w))
                (case-split (integerp n))
                (case-split (integerp n2))
                (case-split (bvecp y 1))
                (case-split (bvecp y2 1))
                (case-split (bvecp x w)) ;drop!
)
           (equal (setbitn (setbitn x w n y) w n2 y2)
                  (setbitn (setbitn x w n2 y2) w n y)
))
  :rule-classes ((:rewrite :loop-stopper ((n n2 s))))
  :hints (("Goal"
           :in-theory (set-difference-theories
                       (enable setbitn setbits-rewrite setbits-rewrite-when-j-is-0
 ;                              bits-bits-1
  ;                             bits-bits-2
                               bits-ocat-1
                               bits-ocat-2
                               bits-ocat-3
;                               natp
                              )
                       '(bits-bits bits-ocat)
                       ))
          ))

prove bits-setbitn?

|#
