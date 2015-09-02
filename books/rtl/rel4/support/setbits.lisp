(in-package "ACL2")

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

(include-book "cat-def")
(local (include-book "setbits-proofs"))

(defund bitn (x n)
  (declare (xargs :guard (and (natp x)
                              (natp n))
                  :verify-guards nil))
  (mbe :logic (bits x n n)
       :exec  (if (evenp (ash x (- n))) 0 1)))

#|

Currently we expect to leave setbits enabled so that it rewrites to cat, but there are some lemmas below which
might be useful if we choose to keep setbits disabled...

is this comment still valid? :
;it may happen that setbitn is called with an index which is a signal rather than a constant.
;in that case, we probably don't want it to expand to setbits.
;thus, we always expect the indices in setbits calls to be constants


;Set bits I down to J of the W-bit value X to Y.

(setbits x w i j y) is only well-defined when the following predicate is true:

(and (natp w)
     (bvecp x w)
     (integerp i)
     (integerp j)
     (<= 0 j)
     (<= j i)
     (< i w)
     (bvecp y (+ 1 i (- j))))

|#

;Note: when j is 0, there is no lower part of x, but we have cat-with-n-0 to handle this case.
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

(defthm setbits-nonnegative-integer-type
  (and (integerp (setbits x w i j y))
       (<= 0 (setbits x w i j y)))
  :rule-classes (:type-prescription))

;this rule is no better than setbits-nonnegative-integer-type and might be worse:
(in-theory (disable (:type-prescription setbits)))

(defthm setbits-natp
  (natp (setbits x w i j y)))

;BOZO r-c?
;tighten?
(defthm setbits-upper-bound
  (< (setbits x w i j y) (expt 2 w)))

(defthm setbits-bvecp-simple
  (bvecp (setbits x w i j y) w))

(defthm setbits-bvecp
  (implies (and (<= w k) ;gen?
                (case-split (integerp k))
                )
           (bvecp (setbits x w i j y) k)))

(defthm setbits-does-nothing
  (implies (and (case-split (< i w))
                (case-split (<= j i))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (<= 0 j))
                )
           (equal (setbits x w i j (bits x i j))
                  (bits x (1- w) 0))))

;taking bits from the lower third
(defthm bits-setbits-1
  (implies (and (< k j)
                (case-split (<= 0 w))
                (case-split (< i w))
                (case-split (<= 0 l))
                (case-split (<= j i)) ;drop?
                (case-split (integerp w))
                (case-split (integerp i))
                (case-split (integerp j))
                )
           (equal (bits (setbits x w i j y) k l)
                  (bits x k l)))
  :hints (("Goal" :in-theory (enable setbits))))

;taking bits from the middle third
;gen?
(defthm bits-setbits-2
  (implies (and (<= k i)
                (<= j l)
                (case-split (integerp i))
                (case-split (<= 0 j))
                (case-split (integerp j))
                (case-split (acl2-numberp k));		  (case-split (integerp k))
                (case-split (acl2-numberp l)) ;	  (case-split (integerp l))
                (case-split (integerp w))
                (case-split (<= 0 w))
                (case-split (< i w))
                )
           (equal (bits (setbits x w i j y) k l)
                  (bits y (- k j) (- l j))))
  :hints (("Goal" :in-theory (enable setbits natp))))

;taking bits from the upper third
(defthm bits-setbits-3
  (implies (and (< i l)
                (case-split (< i w))
                (case-split (< k w)) ;handle this?
                (case-split (<= j i))
                (case-split (<= 0 l))
                (case-split (<= 0 j))
                (case-split (<= 0 w))
                (case-split (integerp l))
                (case-split (integerp w))
                (case-split (integerp i))
                (case-split (integerp j))
                (case-split (integerp k))
                )
           (equal (bits (setbits x w i j y) k l)
                  (bits x k l)))
  :hints (("Goal" :in-theory (enable setbits natp))))

(defthm setbits-with-w-0
  (equal (setbits x 0 i j y)
         0))

;add case-splits to the bitn-setbits rules?
;why can't i prove this from bits-setbits?
(defthm bitn-setbits-1
  (implies (and (< k j) ;case 1
                (< i w)
                (<= 0 i)
                (<= 0 j)
                (<= 0 k)
                (<= j i)
                (integerp k)
                (integerp w)
                (integerp i)
                (integerp j)
                )
           (equal (bitn (setbits x w i j y) k)
                  (bitn x k))))

(defthm bitn-setbits-2
  (implies (and(<= k i) ;;case-2
               (<= j k) ;;case-2
               (<= 0 i)
               (<= 0 j)
               (< i w)
               (integerp k)
               (integerp w)
               (integerp i)
               (integerp j)
               )
           (equal (bitn (setbits x w i j y) k)
                  (bitn y (- k j)))))

(defthm bitn-setbits-3
  (implies (and (< i k) ;;case-3
                (< k w) ;;case-3
;                (< i w)
                (<= 0 i)
                (<= 0 j)
                (<= j i)
                (integerp i)
                (integerp j)
                (integerp k)
                (integerp w))
           (equal (bitn (setbits x w i j y) k)
                  (bitn x k))))

;taking a slice of each of the lower two thirds.
(defthm bits-setbits-4
  (implies (and (<= k i) ;;case-4
                (<= j k) ;;case-4
                (< l j) ;;case-4
                (< i w)
                (<= 0 j)
                (<= 0 l)
                (integerp i)
                (integerp j)
                (integerp w)
                (acl2-numberp l) ;(integerp l)
                )
           (equal (bits (setbits x w i j y) k l)
                  (cat (bits y (- k j) 0)
                       (+ 1 k (- j))
                       (bits x (1- j) l)
                       (- j l))))
  :hints (("Goal" :in-theory (enable setbits))))

;taking a slice of each of the upper two thirds.
(defthm bits-setbits-5
    (implies (and (< i k)  ;case-5
		  (<= l i) ;case-5
		  (<= j l) ;case-5
                  (< k w)  ;case-5 ;BOZO drop stuff like this?
                  (<= 0 j)
                  (integerp i)
                  (integerp j)
                  (integerp w)
                  (acl2-numberp l) ;(integerp l)
                  )
	     (equal (bits (setbits x w i j y) k l)
		    (cat (bits x k (1+ i))
                         (+ k (- i))
			 (bits y (- i j) (- l j))
			 (1+ (- i l))))))

;taking a slice of each of the thirds.
;make one huge bits-setbits lemma?
(defthm bits-setbits-6
  (implies (and (< i k) ;;case-6
                (< l j) ;;case-6
                (<= j i)
                (< k w)
                (<= 0 l)
                (integerp i)
                (integerp j)
                (acl2-numberp l) ; (integerp l)
                (integerp w)
                )
           (equal (bits (setbits x w i j y) k l)
                  (cat (bits x k (1+ i))
                       (+ k (- i))
                       (cat (bits y (+ i (- j)) 0)
                            (1+ (- i j))
                            (bits x (1- j) l)
                            (- j l))
                       (+ 1 i (- l))))))

;prove that if (not (natp w)) setbits = 0 .

;are our setbits-combine rules sufficient to cover all of the cases?

;combining these adjacent ranges [i..j][k..l]
(defthm setbits-combine
  (implies (and (equal j (+ k 1))
                (case-split (<= j i))
                (case-split (<= l k))
                (case-split (natp w))
                (case-split (natp i))
                (case-split (natp j))
                (case-split (natp k))
                (case-split (natp l))
                )
  (equal (setbits (setbits x w k l y1) w i j y2)
         (setbits x w i l (cat y2
                                (+ 1 i (- j))
                                y1
                                (+ 1 k (- l))
                                )))))

(defthm setbits-combine-2
  (implies (and (equal j (+ k 1))
                (case-split (< i w))
                (case-split (<= j i))
                (case-split (<= l k))
                (case-split (natp w))
                (case-split (natp i))
                (case-split (natp j))
                (case-split (natp k))
                (case-split (natp l))
                )
  (equal (setbits (setbits x w i j y2) w k l y1)
         (setbits x w i l (cat y2
                                (+ 1 i (- j))
                                y1
                                (+ 1 k (- l))
                                )))))

(defthm setbits-combine-3
  (implies (and (equal j (+ k 1))
                (case-split (< i w))
                (case-split (<= j i))
                (case-split (<= l k))
                (case-split (natp w))
                (case-split (natp i))
                (case-split (natp j))
                (case-split (natp k))
                (case-split (natp l)))
           (equal (setbits (setbits x w i j y2) w k l y1)
                  (setbits x w i l
                           (cat y2 (+ 1 i (- j))
                                 y1 (+ 1 k (- l)))))))


(defthm setbits-all
  (implies (and (equal i (1- w))
                (case-split (bvecp y w))
                )
  (equal (setbits x w i 0 y)
         y)))

