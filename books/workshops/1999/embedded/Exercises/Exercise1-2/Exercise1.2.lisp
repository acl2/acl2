;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;
;;;;               Exercise 1.2
;;;;
;;;;   Load with (ld "Exercise1.2.lisp")
;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; The proof is structured in two main phases:
;;
;; 1 - Prove that, given a set of coprimes m and a value m,
;;     if each element of m divides v, then the product of the elements of m
;;     divides v.
;; 2 - Prove that, given a set of coprimes m, and given two values v1 and v2 which are
;;     congruent modulo m with two sets of values l1 and l2, then l1 and l2
;;     are congruent w.r.t. m iff v1 and v2 differ by a multiple of the
;;     product of the elements of m. The ``if'' direction of this proof
;;     exploits the statement obtained in phase 1.
;;
;; Once the statement of phase 2 is proved, the theorem requested in the exercise
;; is easily proved.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Phase 1:
;;
;; The key facts that are proved are the following (we omit the
;; statement of some hypothesis here):
;;
;; (1) gcd(x,y) = 1 ^  y|v ^ x|v ==> xy|v                     (divides-both)
;; (2) gcd(x,y) = 1 ^  z|x ^ z|y ==> z = 1                    (only-divisor-of-coprimes-is-1)
;; (3) gcd(x,y)|x   ^ gcd(x,y)|y                              (gcd-divides-both)
;; (4) gcd(m,n) = 1 ^ gcd(n,k) = 1 ==> gcd(m,nk) =1           (prime-of-product)
;; (5) ForAll i: gcd(e,m_i) = 1 ==> gcd(m,Product(m_i)) = 1   (rel-prime-of-product)
;; (6) ForAll i,j with j<>j: gcd(m_i,m_j) = 1 ^
;;     ForAll i: m_i|v ==> Product(m_i)|v
;;                             (if-every-coprime-divides-v-then-product-of-coprimes-divides-v)
;;
;;
;; The proof structure of this phase goes as follows:
;;
;;                             (2)     (3)
;;                               \     /
;;                                \   /
;;                                 (4)
;;                                 /
;;                                /
;;                      (1)     (5)
;;                        \     /
;;                         \   /
;;                          (6)
;;
;;
;;

(in-package "ACL2")


(include-book "../../../../../arithmetic/mod-gcd")

(include-book "../../../../../rtl/rel1/lib1/basic")

(include-book "../../../../../rtl/rel1/support/fp")

;(local (include-book "../../../../../arithmetic/mod-gcd"))

;(local (include-book "../../../../../fp/lib/basic"))

;(local (include-book "../../../../../fp/fp"))


(defun g-c-d (x y) (nonneg-int-gcd x y))


(defun rel-prime (x y)
  (= (g-c-d x y) 1))

(defun rel-prime-all (x l)
  (if (endp l)
      t
    (and (rel-prime x (car l))
         (rel-prime-all x (cdr l)))))

(defun rel-prime-moduli (l)
  (if (endp l)
      t
    (and (integerp (car l))
         (>= (car l) 2)
         (rel-prime-all (car l) (cdr l))
         (rel-prime-moduli (cdr l)))))

(defun divided-by-all (k m)
  (if (endp m)
      t
    (and
     (integerp (/ k (car m)))
     (divided-by-all k (cdr m)))))

(defun natp-all (l)
  (if (endp l)
      t
    (and (natp (car l))
         (natp-all (cdr l)))))

(defun posp-all (l)
  (if (endp l)
      t
    (and (posp (car l))
	 (posp-all (cdr l)))))

(defun prod (l)
  (if (endp l)
      1
    (* (car l) (prod (cdr l)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; First we prove that, if x and y are positive coprimes, and they both divide v,
;; then x * y divides v. We exploit the fact that the g-c-d can be expressed as
;; a linear combination of two multiplier functions, defined into the mod-gcd book.
;;
;; The final lemma is stated by theorem divides-both.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun a (x y) (nonneg-int-gcd-multiplier1 x y))

(defun b (x y) (nonneg-int-gcd-multiplier2 x y))


(defthm g-c-d-type
    (implies (and (integerp x) (integerp y))
             (integerp (g-c-d x y)))
  :rule-classes (:type-prescription))

(defthm a-b-thm
    (implies (and (integerp x) (>= x 0)
                  (integerp y) (>= y 0))
             (= (+ (* (a x y) x)
                   (* (b x y) y))
                (g-c-d x y)))
  :hints (("Goal" :use Linear-combination-for-nonneg-int-gcd))
  :rule-classes ())


(in-theory (disable g-c-d))

(defthm hack-1
	(implies (and (integerp v) (= gcd 1)) (= (* v gcd) v))
	:rule-classes nil)

(defthm hack-2
 (implies
  (and
   (natp x)
   (natp y)
   (integerp v)
   (= (g-c-d x y) 1))
 (= (* v (+ (* (A X Y) X) (* (B X Y) Y))) v))
 :hints (("Goal" :in-theory '((:definition natp))
	:use (a-b-thm
	      (:instance hack-1 (gcd (+ (* (A X Y) X) (* (B X Y) Y)))))))
 :rule-classes nil)


(defthm hack-3
 (implies
  (and
   (integerp a)
   (integerp b)
   (natp x)
   (natp y)
   (> x 0)
   (> y 0)
   (integerp v))
 (= (* v (+ (* A X) (* B Y)) (/ (* x y)))
    (+ (* (/ v y) a) (* (/ v x) b))))
 :rule-classes nil)


(defthm hack-4
 (implies
  (and
   (natp x)
   (natp y)
   (> x 0)
   (> y 0)
   (integerp v))
 (= (* v (+ (* (A X Y) X) (* (B X Y) Y)) (/ (* x y)))
    (+ (* (/ v y) (a x y)) (* (/ v x) (b x y)))))
 :hints (("Goal" :use ((:instance hack-3 (a (a x y)) (b (b x y)))
	               (:type-prescription a)
	               (:type-prescription b))))
 :rule-classes nil)


(defthm hack-5
 (implies
   (and
     (integerp v1)
     (integerp v2)
     (integerp v3)
     (integerp v4))
   (integerp (+ (* v1 v2) (* v3 v4))))
 :rule-classes nil)


(defthm hack-6
 (implies
  (and
   (integerp (/ v y))
   (integerp (/ v x)))
   (integerp (+ (* (/ v y) (a x y)) (* (/ v x) (b x y)))))
	 :hints (("Goal" :use ( (:instance hack-5 (v1 (/ v y)) (v2 (a x y)) (v3 (/ v x)) (v4 (b x y)))
	               (:type-prescription a)
	               (:type-prescription b))))
  :rule-classes nil)

(defthm hack-7
(IMPLIES
 (AND
  (equal decomp-a-b
	 V)
  (equal (* decomp-a-b
	    div)
	 res)
  (INTEGERP res))
 (INTEGERP (* V div)))
:hints (("Goal" :in-theory nil))
:rule-classes nil)



(defthm divides-both
 (implies
  (and
   (natp x)
   (natp y)
   (> x 0)
   (> y 0)
   (integerp v)
   (integerp (/ v y))
   (integerp (/ v x))
   (rel-prime x y))
  (integerp (/ v (* x y))))
 :hints (("Goal" :in-theory (current-theory 'ground-zero)
        :use (rel-prime
              hack-2
              hack-4
              hack-6
	     (:instance hack-7 (div (/ (* X Y)))
                                  (res  (+ (* (* V (/ Y)) (A X Y)) (* (* V (/ X)) (B X Y))))
	                          (decomp-a-b (* V (+ (* (A X Y) X) (* (B X Y) Y)))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Now we prove that the only common divisor of two coprimes is 1.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;




(defthm hack-8
  (implies
   (and
    (natp n)
    (posp d))
   (equal (integerp (/ n d)) (equal (nonneg-int-mod n d) 0)))
  :hints (("Goal" :use (:instance Left-nonneg-int-mod-* (n d) (j (/ n d))))))



(defthm only-divisor-of-coprimes-is-1
 (implies
  (and
   (natp y)
   (natp x)
   (posp z)
   (rel-prime x y)
   (integerp (/ x z))
   (integerp (/ y z)))
  (= z 1))
 :hints (("Goal" :use (rel-prime g-c-d
		       (:instance Nonneg-int-gcd-is-LARGEST-common-divisor-<= (d z)))))
 :rule-classes nil)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; We now prove that (g-c-d x y) divides both x and y.
;; This is stated by theorem gcd-divides-both.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm integer-div-of-factor
 (implies
  (and
   (natp a)
   (natp b)
   (natp c)
   (rel-prime a b)
   (integerp (/ (* b c) a)))
  (integerp (/ c a)))
  :hints (("Goal" :use
	   ((:instance rel-prime (x a) (y b))
            (:instance g-c-d (x a) (y b))
	    (:instance hack-8 (n c) (d a))
	    (:instance hack-8 (n (* b c)) (d a))
	    (:instance Divisor-of-product-divides-factor (y b) (z a) (x c))))))


(defthm hack-9
 (implies
  (and
   (integerp x)
   (posp y)
   (integerp (/ x y)))
  (= x (* (/ x y) y)))
 :rule-classes nil)

(defthm hack-10
 (implies
  (and
   (integerp c)
   (= (+ (* a x) (* b y)) 1))
   (= (* c (+ (* a x) (* b y))) c))
 :rule-classes nil)

(defthm hack-11
 (implies
  (and
   (integerp c))
   (= (+ (* c a x) (* c b y))
      (* c (+ (* a x) (* b y)))))
 :rule-classes nil)

(defthm hack-12
 (implies
  (and
   (integerp c)
   (= (+ (* a x) (* b y)) 1))
   (= (+ (* c a x) (* c b y)) c))
 :hints (("Goal" :use (hack-10 hack-11)))
 :rule-classes nil)




(defthm hack-13
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (rel-prime m n))
  (= k (+ (* k (a m n) m) (* k (b m n) n))))
 :hints (("Goal" :use (
		       (:instance hack-12 (a (a m n)) (b (b m n)) (x m) (y n) (c k))
		       (:instance a-b-thm (x m) (y n))
		       (:instance rel-prime (x m) (y n)))))
 :rule-classes nil)

(defthm hack-14
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (= k (+ (* k (a m n) (/ m cd) cd) (* (b m n) (/ (* n k) cd) cd))))
 :hints (("Goal" :use (
		       hack-13
		       (:instance hack-9 (x m) (y cd))
		       (:instance hack-9 (x (* n k)) (y cd)))))
 :rule-classes nil)

(defthm hack-15
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (= k (* cd (+ (* k (a m n) (/ m cd) ) (* (b m n) (/ (* n k) cd))))))
 :hints (("Goal" :use hack-14))
 :rule-classes nil)

(defthm hack-16
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (integerp (+ (* k (a m n) (/ m cd) ) (* (b m n) (/ (* n k) cd)))))
 :rule-classes nil)

(defthm hack-17
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (= (/ k cd) (+ (* k (a m n) (/ m cd) ) (* (b m n) (/ (* n k) cd)))))
 :hints (("Goal" :use ( hack-16 hack-15)))
 :rule-classes nil)


(defthm hack-18
 (implies
  (and
   (natp m)
   (natp n)
   (natp k)
   (posp cd)
   (integerp (/ m cd))
   (integerp (/ (* n k) cd))
   (rel-prime m n))
  (integerp (/ k cd)))
 :hints (("Goal" :in-theory nil :use ( hack-16 hack-17)))
 :rule-classes nil)



(defthm gcd-divides-both
 (implies
  (and
   (natp x)
   (posp y))
  (and
   (integerp (/ x (g-c-d x y)))
   (integerp (/ y (g-c-d x y)))))
 :hints (("Goal" :in-theory (enable g-c-d))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Frome the fact that (g-c-d x y) divides both x and y, we easily
;; derive that, if m and n are coprimes, and m and k are coprimes,
;; then m and (n * k) are coprimes.
;; This is stated by prime-of-product.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm hack-19
  (implies
  (and
   (posp x)
   (posp y)
   (natp v)
   (rel-prime v x)
   (rel-prime v y))
  (and
   (integerp (/ v       (g-c-d v (* x y))))
   (integerp (/ (* x y) (g-c-d v (* x y))))))
   :hints (("Goal" :use  ((:instance gcd-divides-both (x v) (y (* x y)))))))


(defthm hack-20
  (implies
  (and
   (posp n)
   (posp k)
   (natp m)
   (rel-prime m n)
   (rel-prime m k))
  (and
   (integerp (/ m       (g-c-d m (* n k))))
   (integerp (/ k       (g-c-d m (* n k))))))
   :hints (("Goal" :use  (
			  (:instance g-c-d (x m) (y (* n k)))
			  (:instance Nonneg-int-gcd->-0 (n m) (d (* n k)))
			  (:instance hack-19 (v m) (x n) (y k))
			  (:instance hack-18 (cd (g-c-d m (* n k))))))))


(defthm prime-of-product
   (implies
  (and
   (posp n)
   (posp k)
   (natp m)
   (rel-prime m n)
   (rel-prime m k))
  (rel-prime m (* n k)))
   :hints (("Goal" :in-theory (enable rel-prime)
	   :use ( hack-20
		  (:instance g-c-d (x m) (y (* n k)))
		  (:instance Nonneg-int-gcd->-0 (n m) (d (* n k)))
		  (:instance only-divisor-of-coprimes-is-1
			     (z (g-c-d m (* n k)))
			     (x m)
			     (y k))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; We now prove that, if el is coprime with every element of a list
;; l, then it is coprime with their product (prod l).
;; This is stated by rel-prime-of-product.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(in-theory (enable prod rel-prime rel-prime-moduli))

(defthm hack-21
 (implies
  (and
   (not (endp m))
   (posp-all m))
  (and
    (posp-all (cdr m))
    (posp (car m))
    (posp (prod m))
    (posp (prod (cdr m)))))
 :rule-classes nil)

(defthm hack-22
 (implies
  (and
   (not (endp m))
   (rel-prime-all el m))
  (and
   (rel-prime el (car m))
   (rel-prime-all el (cdr m))))
 :hints (("Goal" :use (:instance rel-prime-all (x el) (l m))))
 :rule-classes nil)


(defthm rel-prime-of-product
 (implies
   (and
   (posp-all m)
   (natp el)
   (rel-prime-all el m))
   (rel-prime el (prod m)))
 :hints ( ("Goal" :in-theory (disable rel-prime natp) :induct (len m))
	  ("Subgoal *1/2''" :use ( (:instance rel-prime (x el) (y 1))
				   (:instance g-c-d (x el) (y 1))
				   (:instance Nonneg-int-gcd-1-right (x el))))
	  ("Subgoal *1/1'" :use
	   (hack-21
	    hack-22
	    (:instance prod (l m))
	    (:instance prime-of-product (n (car m)) (k (prod (cdr m))) (m el))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; We prove the main lemma of the first part of the proof,
;; namely that if m is a list of positive coprimes, and
;; every element of m divides v, then the product of the elements
;; of m, (prod m), divides v.
;; This is stated by if-every-coprime-divides-v-then-product-of-coprimes-divides-v.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm hack-23
 (implies
  (and
   (not (endp m))
   (rel-prime-moduli m))
  (and
   (rel-prime-moduli (cdr m))
   (posp-all (cdr m))
   (natp (car m))
   (< 0 (car m)))))




(defthm if-every-coprime-divides-v-then-product-of-coprimes-divides-v
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v)
    (divided-by-all v m))
  (integerp (/ v (prod m))))
 :hints (("Goal" :induct (len m))
	 ("Subgoal *1/1"
	  :in-theory '((:definition posp) (:definition natp))
	  :use
	  (
           hack-21
           hack-23
	   (:instance natp-all (l m))
	   (:instance posp-all (l m))
	   (:instance prod (l m))
	   (:instance rel-prime-moduli (l m))
	   (:instance divided-by-all (k v))
	   (:instance rel-prime-of-product (el (car m)) (m (cdr m)))
	   (:instance divides-both (x (car m)) (y (prod (cdr m))))))))





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Second part of the proof.
;;
;; We start by introducing the notion of congruence of a pair of lists
;; of numbers w.r.t. a third list of numbers.
;; Then we prove the following facts (where some hypothesis are omitted,
;; ``congruent'' indicates the definition congruent-all-mod, and
;; ``congruent-lists'' indicates the definition in
;; congruant-all-mod-list):
;;
;; (7)  ForAll i: m_i|k ==> congruent (x,y,m) ,==> congruent((x mod k),y,m)
;; (8)  ForAll i,j with j<>j: gcd(m_i,m_j) = 1 ^
;;      congruent(v1,l1,m) ^ congruent (v2,l2,m) ^
;;      Product(m_i)|(v1-v2) ==> congruent-lists(l1,l2,m)
;; (9)  ForAll i,j with j<>j: gcd(m_i,m_j) = 1 ^
;;      congruent(v1,l1,m) ^ congruent (v2,l2,m) ^
;;      congruent-lists(l1,l2,m) ==> Product(m_i)|(v1-v2)
;; (10) ForAll i,j with j<>j: gcd(m_i,m_j) = 1 ^
;;      congruent(v1,l1,m) ^ congruent (v2,l2,m) ==>
;;      (congruent-lists(l1,l2,m) <==> Product(m_i)|(v1-v2))
;; (11) (0<=v1<p) ^ (0<=v2<p) ^ p|(v1-v2) ==> v1 = v2
;; (12) ForAll i,j with j<>j: gcd(m_i,m_j) = 1 ^
;;      (0<=v1<p) ^ (0<=v2<p) ^
;;      congruent(v1,l,m) ^ congruent(v2,l,m) ==> v1 = v2
;;
;;
;; The proof scheme is the following (where (6) refers to the main statement derived
;; in phase 1):
;;
;;                               (6)      (7)
;;                                |        |
;;                                |        |
;;                               (9)      (8)
;;                                 \      /
;;                                  \    /
;;                                   (10)      (11)
;;                                      \      /
;;                                       \    /
;;                                        (12)
;;


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory
 (union-theories (current-theory 'ground-zero)
		 '((:definition prod)
		   (:definition natp)
		   (:definition natp-all)
		   (:definition posp)
		   (:executable-counterpart prod)
		   (:type-prescription prod)
		   (:induction prod)
		   (:executable-counterpart posp)
		   (:type-prescription posp)
		   (:definition posp-all)
		   (:executable-counterpart posp-all)
		   (:type-prescription posp-all)
		   (:induction posp-all)
		   (:definition divided-by-all)
		   (:executable-counterpart divided-by-all)
		   (:type-prescription divided-by-all)
		   (:induction divided-by-all) )))



(defun congruent-mod (x y m)
  (= (mod x m) (mod y m)))



(defun congruent-all-mod (x a m)
  (declare (xargs :measure (len m)))
  (if (endp m)
      t
    (and (congruent-mod x (car a) (car m))
	 (congruent-all-mod x (cdr a) (cdr m)))))


(defun congruent-all-mod-list (l1 l2 m)
  (declare (xargs :measure (len m)))
  (if (endp m)
      t
    (and
     (congruent-mod (car l1) (car l2) (car m))
     (congruent-all-mod-list (cdr l1) (cdr l2) (cdr m)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; We load some books, importing only some key lemmas about
;; the combination of mod and arithmetic functions.
;; We prove some additional basic lemmas.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(include-book "../../../../../arithmetic/top-with-meta")

(include-book "Minimal-Mod-Lemmas")

(in-theory (disable mod-x-y-=-x-exp))

(in-theory (disable mod))

(defthm r-mod-mod
  (implies
   (and
    (integerp x)
    (integerp z)
    (integerp i)
    (> i 0)
    (> z 0))
   (equal (mod (mod x (* i z)) z)
	  (mod x z)))
  :hints (("Goal" :use (:instance rewrite-mod-mod-exp (y (* i z))))))

(defthm r-mod-mod-cancel
 (implies
   (and
    (integerp x)
    (integerp z)
    (> z 0))
   (equal (mod (mod x z) z) (mod x z))))



(defthm product-divided-by-all
 (implies
  (posp-all m)
  (divided-by-all (prod m) m))
 :hints (("Subgoal *1/1.2''"
	  :induct t)
	 ("Goal"
	  :in-theory (disable commutativity-of-*)
	  :induct (len m))))



(defthm prod-is-pos
 (implies
  (posp-all m)
  (posp (prod m))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Here we prove that, if two values v1 and v2 differ by the product
;; of a list of coprimes m, then lists congruent to them are congruent w.r.t. m.
;; This is stated by if-values-differ-by-product-of-m-then-cong-lists-are-congruent-wrt-m.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm if-k-is-divided-by-all-then-x-and-x-mod-k-have-same-congruence
 (implies
  (and
   (equal (len y) (len m))
   (integerp x)
   (posp k)
   (posp-all m)
   (divided-by-all k m))
  (equal
   (congruent-all-mod (mod x k) y m)
   (congruent-all-mod x y m))))


(defthm modulo-prod-has-same-congruence
 (implies
  (and
   (equal (len y) (len m))
   (integerp x)
   (posp-all m))
  (equal
   (congruent-all-mod (mod x (prod m)) y m)
   (congruent-all-mod x y m))))




(defthm express-mod-changing-arg-sign
  (implies
   (and
    (integerp x)
    (integerp y)
    (not (integerp (/ x y))))
   (equal (mod (- x) y) (- y (mod x y))))
  :hints (("Goal" :in-theory (enable mod)))
  :rule-classes nil)

(defthm mod-0-allows-changing-arg-sign
  (implies
   (and
    (integerp x)
    (integerp y)
    (not (equal y 0))
    (integerp (/ x y)))
   (and
    (equal (mod x y) 0)
    (equal (mod (- x) y) 0)))
  :rule-classes nil)





(defthm hack-24
  (implies
   (and (integerp x)
	(integerp y)
	(integerp z)
	(not (integerp (/ y z)))
	(not (equal z 0)))
   (equal (mod (- x y) z)
	  (mod (- (mod x z) (mod y z)) z)))
  :hints (("Goal"
	 :use (
		 (:instance mod-+-exp (y (- y)))
		 (:instance express-mod-changing-arg-sign (x y) (y z))
		 (:instance cancel-mod-+-exp
			    (i (/ z z))
			    (x z)
			    (y (- (mod x z) (mod y z))))
		 (:instance integerp-mod-exp (i x) (j z))
		 (:instance integerp-mod-exp (i y) (j z)) )
	 :in-theory '(
		      (:rewrite inverse-of-*)
		      (:rewrite associativity-of-+)
		      (:rewrite commutativity-of-+))))
  :rule-classes nil)


(defthm hack-25
  (implies
   (and (integerp x)
	(integerp y)
	(integerp z)
	(integerp (/ y z))
	(not (equal z 0)))
   (equal (mod (- x y) z)
	  (mod (- (mod x z) (mod y z)) z)))
  :hints (("Goal" :in-theory (enable mod)))
  :rule-classes nil)

(defthm mod--
  (implies
   (and (force (integerp x))
	(force (integerp y))
	(force (integerp z))
	(force (not (equal z 0))))
   (equal (mod (- x y) z)
	  (mod (- (mod x z) (mod y z)) z)))
  :hints (("Goal" :use (hack-24 hack-25))))



(defthm cong-all-mod-implies-cong-all-mod-list
 (implies
  (and
   (congruent-all-mod v1 l1 m)
   (congruent-all-mod v1 l2 m))
  (congruent-all-mod-list l1 l2 m)))


(defthm hack-26
 (implies
  (rel-prime-moduli m)
  (and
   (posp-all m)
   (posp (prod m))))
 :hints (("Goal" :in-theory (enable rel-prime-moduli)))
 :rule-classes :forward-chaining)


(defthm hack-27
 (implies
  (integerp (/ a b))
  (integerp (/ (- a) b)))
 :rule-classes nil)


(defthm hack-28
  (implies
   (and
    (integerp v1)
    (integerp v2)
    (posp (prod m))
    (integerp (/ (- v1 v2) (prod m))))
   (and
    (integerp (/ (- v2 v1) (prod m)))
    (equal  v2 (+ v1 (* (/ (- v2 v1) (prod m)) (prod m))))))
  :hints (("Goal" :use (:instance hack-27 (a (- v1 v2)) (b (prod m)))))
  :rule-classes nil)


(defthm if-values-differ-by-product-of-m-then-cong-lists-are-congruent-wrt-m
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v1)
    (integerp v2)
    (natp-all l1)
    (natp-all l2)
    (equal (len l1) (len m))
    (equal (len l2) (len m))
    (congruent-all-mod v1 l1 m)
    (congruent-all-mod v2 l2 m)
    (integerp (/ (- v1 v2) (prod m))))
   (congruent-all-mod-list l1 l2 m))
  :hints (("Goal"
	   :in-theory '((:definition posp)
			(:rewrite unicity-of-1))
	   :use
	   ( hack-28
	     hack-26
	     cong-all-mod-implies-cong-all-mod-list
	     (:instance mod-x+i*y-y-exp (i (/ (- v2 v1) (prod m))) (x v1) (y (prod m)))
	     (:instance r-mod-mod (x v1) (i 1) (z (prod m)))
	     (:instance modulo-prod-has-same-congruence (x v1) (y l2))
	     (:instance modulo-prod-has-same-congruence (x v2) (y l2))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Now we prove that, given two values v1 and v2, if lists congruent to
;; them are congruent w.r.t. m, then v1 and v2 differ by the product
;; of the elements of m.
;;
;; This is stated by
;; if-values-are-congruent-wrt-m-via-cong-lists-then-they-differ-by-a-multiple-of-prod-m.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defthm same-congruence-over-conglist
 (implies
  (congruent-all-mod-list l1 l2 m)
 (equal
    (congruent-all-mod v l1 m)
    (congruent-all-mod v l2 m)))
 :rule-classes nil)

(defun cong-sg-val (v1 v2 m)
  (if
      (endp m)
      t
    (and
     (congruent-mod v1 v2 (car m))
     (cong-sg-val   v1 v2 (cdr m)))))


(defthm same-cong-lists-means-same-mods
 (implies
  (and
   (equal (len l) (len m))
   (congruent-all-mod v1 l m)
   (congruent-all-mod v2 l m))
  (cong-sg-val v1 v2 m)))

(defthm mod-of-0
 (implies (posp carm) (equal (mod 0 carm) 0))
 :rule-classes nil)


(defthm same-cong-vals-implies-diff-has-cong-to-zero
 (implies
  (and
   (posp-all m)
   (integerp v1)
   (integerp v2))
   (implies
    (cong-sg-val v1 v2 m)
    (cong-sg-val (- v1 v2) 0 m)))
 :hints (("Goal"
	  :in-theory (disable mod-=-0-exp
                              mod--
                              mod-+-exp
                              cancel-mod-+-exp
                              rewrite-mod-mod-exp
                              r-mod-mod-cancel
                              integerp-mod-exp)
	  :induct (len m))
	 ("Subgoal *1/1" :use  (
				(:instance mod-of-0 (carm (car m)))
				(:instance mod-- (x v1) (y v2) (z (car m)))))))


(defthm cong-0-is-divided-by-all
 (implies
  (and
   (integerp v)
   (posp-all m))
  (equal (cong-sg-val v 0 m) (divided-by-all v m)))
 :hints (("Goal" :induct (len m))
	 ("Subgoal *1/1" :use ((:instance mod-of-0 (carm (car m)))
			       (:instance mod-=-0-exp (x v) (y (car m))))
                         :in-theory (disable MOD-=-0-EXP)))
 :rule-classes nil)




(in-theory (enable if-every-coprime-divides-v-then-product-of-coprimes-divides-v))




(defthm if-values-are-congruent-wrt-m-via-cong-lists-then-they-differ-by-a-multiple-of-prod-m
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v1)
    (integerp v2)
    (natp-all l1)
    (natp-all l2)
    (equal (len l1) (len m))
    (equal (len l2) (len m))
    (congruent-all-mod v1 l1 m)
    (congruent-all-mod v2 l2 m)
    (congruent-all-mod-list l1 l2 m))
  (integerp (/ (- v1 v2) (prod m))))
  :hints (("Goal" :use ( hack-26
			 (:instance cong-0-is-divided-by-all (v (- v1 v2)))
			 (:instance same-congruence-over-conglist (v v2))
			 (:instance same-cong-vals-implies-diff-has-cong-to-zero (v1 v1) (v2 v2))
			 (:instance if-every-coprime-divides-v-then-product-of-coprimes-divides-v
                                    (v (- v1 v2)))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; We prove that congruence w.r.t. m is equivalent to checking that the difference
;; of two values is a multiple of the product of the elements of l.
;; This follows easily from the ``if'' and ``only if'' lemmas proved above.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defthm congruence-of-cong-lists-is-equivalent-to-dividabilty-by-prod-m
  (implies
   (and
    (rel-prime-moduli m)
    (integerp v1)
    (integerp v2)
    (natp-all l1)
    (natp-all l2)
    (equal (len l1) (len m))
    (equal (len l2) (len m))
    (congruent-all-mod v1 l1 m)
    (congruent-all-mod v2 l2 m))
   (equal
    (congruent-all-mod-list l1 l2 m)
    (integerp (/ (- v1 v2) (prod m)))))
  :hints (("Goal"
           :use (if-values-differ-by-product-of-m-then-cong-lists-are-congruent-wrt-m
                 if-values-are-congruent-wrt-m-via-cong-lists-then-they-differ-by-a-multiple-of-prod-m))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Here we prove a basic lemma: if two numbers differ by a multiple of a fixed number prod,
;; and they both are in the range [0,prod), then they are equal.
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm hack-29
 (implies
  (and
   (posp prod)
   (integerp resdiv))
  (and
   (implies (equal resdiv 0) (equal (* resdiv prod) 0))
   (implies (< resdiv 0)     (<     (* resdiv prod) 0))
   (implies (> resdiv 0)     (>=    (* resdiv prod) prod)))))


(defthm hack-30
 (implies
  (and
    (natp v)
    (posp prod)
    (< v prod)
    (integerp (/ v prod)))
  (equal v 0))
; Matt K. v7-1 mod for avoiding "Goal'", 2/13/2015: "Goal''" changed to "Goal'".
 :hints (("Goal'" :use (:instance hack-29 (resdiv (/ v prod)))))
 :rule-classes nil)


(defthm hack-31
 (implies
  (and
    (posp prod)
    (natp v1)
    (natp v2)
    (< v1 prod)
    (< v2 prod)
    (integerp (/ (abs (- v1 v2)) prod)))
  (equal v1 v2))
 :hints (("Goal" :use (:instance hack-30 (v (abs (- v1 v2))))))
 :rule-classes nil)


(defthm hack-32
  (iff (integerp (/ (abs a) b)) (integerp (/ a b)))
  :rule-classes nil)

(defthm equality-in-range
 (implies
  (and
    (posp prod)
    (natp v1)
    (natp v2)
    (< v1 prod)
    (< v2 prod)
    (integerp (/ (- v1 v2) prod)))
  (equal v1 v2))
 :hints (("Goal" :use (hack-31
		       (:instance hack-32 (a (- v1 v2)) (b prod)))))
 :rule-classes nil)





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Required statement
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(defthm unique-inversion
  (implies
   (and
    (rel-prime-moduli m)
    (natp v1)
    (natp v2)
    (< v1 (prod m))
    (< v2 (prod m))
    (natp-all l)
    (equal (len l) (len m))
    (congruent-all-mod v1 l m)
    (congruent-all-mod v2 l m))
   (equal v1 v2))
  :hints (("Goal" :use
	   ( (:instance congruence-of-cong-lists-is-equivalent-to-dividabilty-by-prod-m (l1 l) (l2 l))
	     (:instance equality-in-range (prod (prod m))))))
  :rule-classes nil)





