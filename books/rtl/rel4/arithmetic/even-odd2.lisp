(in-package "ACL2")

;This is different from the book even-odd.  (We define new functions EVEN and ODD here.)
;This book contains only the results I want to export.  The proofs are in even-odd2-proofs.lisp
;I could take pains to define functions that agree with evenp and oddp for all inputs (complex-rationalps are
;a little weird).  But for now, I'll just focus on the integers.
;Perhaps see also the function REVEN in x-2xx.lisp

(include-book "ground-zero")
(local (include-book "even-odd2-proofs"))

;just a helper function
(defund even-aux (x)
  (if (zp x)
      t
    (if (eql 1 x)
        nil
      (even-aux (+ -2 x)))))

;A recursive recognizer for even integers.
;Note that EVEN is not the same as the built in function EVENP
;handle complex numbers?
(defund even (x)
  (if (not (integerp x))
      nil
    (if (< x 0)
        (even-aux (- x))
      (even-aux x))))

;A recognizer for odd integers.
;Most theorems about ODD follow from theorems about EVEN.
(defund odd (x)
  (and (integerp x)
       (not (even x))))

;keep disabled?
(defthmd even-is-evenp
  (implies (integerp x)
           (equal (even x) (evenp x))))

(defthm even-minus
  (implies (case-split (acl2-numberp x))
           (equal (even (* -1 x))
                  (even x))))

;not currently a rewrite rule
(defthm even-means-integerp
  (implies (even x)
           (integerp x))
  :rule-classes (;:compound-recognizer
                 :forward-chaining))

;not currently a rewrite rule
(defthm odd-means-integerp
  (implies (odd x)
           (integerp x))
  :rule-classes (;:compound-recognizer
                 :forward-chaining))

(defthm even-sum-rewrite-1
  (implies (and (even x)
                (case-split (acl2-numberp y))
                )
           (and (equal (even (+ x y))
                       (even y))
                (equal (even (+ y x))
                       (even y)))))

(defthm even-sum-rewrite-2
  (implies (odd x)
           (and (equal (even (+ x y))
                       (odd y))
                (equal (even (+ y x))
                       (odd y)))))

(defthm odd-sum-rewrite-1
  (implies (even x)
           (and (equal (odd (+ x y))
                       (odd y))
                (equal (odd (+ y x))
                       (odd y)))))

(defthm odd-sum-rewrite-2
  (implies (and (odd x)
                (case-split (acl2-numberp y))
                )
           (and (equal (odd (+ x y))
                       (even y))
                (equal (odd (+ y x))
                       (even y)))))


;avoid loops
;wait, why would even ever be around?
(theory-invariant (incompatible (:rewrite even-reduce) (:definition even-aux)))

;yuck.  generalize?
(defthm even-reduce
  (implies (case-split (integerp n))
           (equal (even (+ -1 n))
                  (not (even n)))))


(defthm odd-reduce
  (implies (case-split (integerp n))
           (equal (odd (+ -1 n))
                  (not (odd n)))))

(defthm even-double
  (implies (integerp x)
           (even (* 2 x))))

(defthm odd-double
  (implies (integerp x)
           (not (odd (* 2 x)))))


;do we want this enabled?
;Eric needed this for an RTL proof, but perhaps we should think more about how to handle this.
(defthm even-means-half-is-integer
  (implies (even x)
           (integerp (* 1/2 x))))

#|

there are plenty more nice even-odd theorems

(defthm even-sum-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (even (+ x y))
                  (or (and (even x) (even y))
                      (and (odd x) (odd y)))))
  :hints (("Goal" :in-theory (enable odd))))

plus rules to rewrite oddp and evenp

(defthm oddp-sum
  (implies (and (integerp x)
                (integerp y))
           (equal (oddp (+ x y))
                  (or (and (oddp x) (evenp y))
                      (and (evenp x) (oddp y))))))



;move? ;or just prove rules like EVEN-SUM-REWRITE-1, etc. about even-aux
(defthm even-aux-reduce-by-4
  (implies (and (case-split (integerp n))
                (case-split (<= 4 n)))
           (equal (even-aux (+ -4 n))
                  (even-aux n)))
  :hints (("Goal" :in-theory (e/d (even odd) (ODD-REDUCE EVEN-REDUCE  EVEN-SUM-REWRITE-1
                                                   ODD-SUM-REWRITE-1
                                                    EVEN-SUM-REWRITE-2
                                                     ODD-SUM-REWRITE-2))
           :use ((:instance even-reduce (n n))
                 (:instance even-reduce (n (+ -1 n)))
                 (:instance even-reduce (n (+ -2 n)))
                 (:instance even-reduce (n (+ -3 n)))))))
|#

