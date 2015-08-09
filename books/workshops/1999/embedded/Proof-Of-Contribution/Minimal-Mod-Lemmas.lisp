(in-package "ACL2")


(local (include-book "private-qr-lemmas"))


(defthm rewrite-mod-mod-exp
  (implies
   (and (equal i (/ y z))
	(integerp i)
	(integerp x)
	(integerp y)
	(integerp z)
	(> y 0)
	(> z 0))
   (equal (mod (mod x y) z)
	  (mod x z)))
  :hints (("Goal"
	   :in-theory nil
	   :use rewrite-mod-mod)))

(defthm mod-=-0-exp
  (implies
   (and
    (integerp x)
    (integerp y)
    (not (equal y 0)))
   (equal (equal (mod x y) 0)
	  (integerp (/ x y))))
  :hints (("Goal"
	   :in-theory nil
	   :use mod-=-0)))


(defthm mod-type-exp
  (implies
   (and
    (integerp x)
    (integerp y)
    (not (equal y 0)))
   (and
    (equal (< (mod x y) 0)
	   (and (< y 0)
		(not (integerp (/ x y)))))
    (equal (> (mod x y) 0)
	   (and (> y 0)
		(not (integerp (/ x y)))))))
 :hints (("Goal"
	  :in-theory nil
	  :use mod-type)))


(defthm integerp-mod-exp
  (implies
   (and (integerp i)
	(integerp j))
   (integerp (mod i j)))
  :hints (("Goal"
	   :in-theory nil
	   :use integerp-mod)))


(defthm mod-bounds-exp
  (and
   (implies
    (and (> y 0)
	 (integerp x)
	 (integerp y)
	 (not (equal y 0)))
    (< (mod x y) y))
   (implies
    (and (< y 0)
	 (integerp x)
	 (integerp y)
	 (not (equal y 0)))
    (> (mod x y) y)))
  :hints (("Goal"
	   :in-theory nil
	   :use mod-bounds)))

(defthm mod-+-exp
  (implies
   (and (integerp x)
	(integerp y)
	(integerp z)
	(not (equal z 0)))
   (equal (mod (+ x y) z)
	  (mod (+ (mod x z) (mod y z)) z)))
  :hints (("Goal"
	   :in-theory nil
	   :use mod-+)))





(defthm cancel-mod-+-exp
  (implies
   (and (equal i (/ x z))
	(integerp i)
	(integerp x)
	(integerp y)
	(integerp z)
	(not (equal z 0)))
   (and
    (equal (mod (+ x y) z)
	   (mod y z))
    (equal (mod (+ y x) z)
	   (mod y z))))
  :hints (("Goal"
	   :in-theory nil
	   :use cancel-mod-+)))

(defthm mod-x+i*y-y-exp
   (implies
    (and
     (integerp i)
     (integerp x)
     (integerp y)
     (not (equal y 0)))
    (equal (mod (+ x (* i y)) y)
	   (mod x y)))
  :hints (("Goal"
	   :in-theory nil
	   :use mod-x+i*y-y)))

(defthm mod-x-y-=-x-exp
  (implies
   (and
    (integerp x)
    (integerp y)
    (not (equal y 0)))
   (equal (equal (mod x y) x)
          (or (and (>= x 0) (> y 0) (< x y))
              (and (<= x 0) (< y 0) (> x y)))))
  :hints (("Goal"
	   :in-theory nil
	   :use mod-x-y-=-x)))





