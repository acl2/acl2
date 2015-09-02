
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; bytes-and-words.lisp
;;;
;;; bits, nibbles, bytes, and words.
;;;
;;; From work by Warren Hunt.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "arithmetic-5/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; We start with a slew of definitions

;;; recognizers

(defund n01p (x)
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 1))))

(defund n04p (x)
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 4))))

(defund n08p (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 8))))

(defund n16p (x)
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 16))))

(defund n32p (x)
  (declare (xargs :guard t))
  (and (integerp x)
       (<= 0 x)
       (< x (expt 2 32))))

(defund word-aligned-p (x)
  (declare (xargs :guard (integerp x)))
  (and (integerp x)
       (<= 0 x)
       (equal (mod x (expt 2 2))
              0)))

;;; fixers

(defund n01 (x)
  (logand x (+ -1 (expt 2 1))))

(defund n04 (x)
  (logand x (+ -1 (expt 2 4))))

(defund n08 (x)
  (declare (xargs :guard (integerp x)))
  (logand x (+ -1 (expt 2 8))))

(defund n16 (x)
  (logand x (+ -1 (expt 2 16))))

(defund n32 (x)
  (declare (xargs :guard (integerp x)))
  (logand x (+ -1 (expt 2 32))))

(defund word-align (x)
  ;; mask off the bottom 2 bits of a 32 bit address
  (declare (xargs :guard (integerp x)))
  (logand x (ash (+ -1 (expt 2 30)) 2)))

;;; accessors

;;; RBK: These are some odd definitions.  I would probably replace
;;; these with one that specified the bit range to be extracted.

(defund bits-04 (x i)
  (n04 (ash x (- (ash i 2)))))

(defund bits-08 (x i)
  (n08 (ash x (- (ash i 3)))))

(defund bits-16 (x i)
  (n16 (ash x (- (ash i 4)))))

;;; converting from unsigned to signed formats

(defund n04-to-i04 (x)
  (if (<= (expt 2 3) x)
      (- x (expt 2 4))
    x))

(defund n08-to-i08 (x)
  (if (<= (expt 2 7) x)
      (- x (expt 2 8))
    x))

(defund n16-to-i16 (x)
  (if (<= (expt 2 15) x)
      (- x (expt 2 16))
    x))

(defund n32-to-i32 (x)
  (if (<= (expt 2 31) x)
      (- x (expt 2 32))
    x))

;;; pasting together

(defund n04-n04-to-n08 (x y)
  (logior y (ash x 4)))

;;; Arithmetic operators

(defund n16+ (x y)
  (n16 (+ x y)))

(defund n32+ (x y)
  (declare (xargs :guard (and (integerp x)
			      (integerp y))))
  (n32 (+ x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Some theorems --- should be expanded

(defthm |(n32-to-i32 x) --- 1|
  (implies (< x (expt 2 31))
           (equal (n32-to-i32 x)
                  x))
  :hints (("Goal" :in-theory (enable n32-to-i32))))

(defthm |(n32-to-i32 x) --- 2|
  (implies (<= (expt 2 31) x)
           (equal (n32-to-i32 x)
                  (- x (expt 2 32))))
  :hints (("Goal" :in-theory (enable n32-to-i32))))

(defthm |(n08p x)|
  (implies (and (integerp x)
                (<= 0 x)
                (< x (expt 2 8)))
           (n08p x))
  :hints (("Goal" :in-theory (enable n08p))))

(defthm |(n32p x)|
  (implies (and (integerp x)
                (<= 0 x)
                (< x (expt 2 32)))
           (n32p x))
  :hints (("Goal" :in-theory (enable n32p))))

(defthm |(word-aligned-p x)|
  (implies (and (integerp x)
                (<= 0 x)
                (equal (mod x (expt 2 2))
                       0))
           (word-aligned-p x))
  :hints (("Goal" :in-theory (enable word-aligned-p))))

(defthm n08-bounds
  (implies (n08p n)
           (and (<= 0 n)
                (<= n (+ -1 (expt 2 8)))))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable n08p))))

(defthm n32-bounds
  (implies (n32p n)
           (and (<= 0 n)
                (<= n (+ -1 (expt 2 32)))))
  :rule-classes ((:forward-chaining))
  :hints (("Goal" :in-theory (enable n32p))))

(defthm n08p-type
  (implies (n08p n)
	   (and (integerp n)
                (<= 0 n)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable n08p))))

(defthm n32p-type
  (implies (n32p n)
	   (and (integerp n)
                (<= 0 n)))
  :rule-classes :compound-recognizer
  :hints (("Goal" :in-theory (enable n32p))))

(defthm n08-type
  (and (integerp (n08 n))
       (<= 0 (n08 n)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable n08))))

(defthm n32-type
  (and (integerp (n32 n))
       (<= 0 (n32 n)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable n32))))

(defthm n32-to-i32-type
  (implies (integerp n)
           (integerp (n32-to-i32 n)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable n32-to-i32))))

(defthm |(n08 n)|
  (implies (n08p n)
           (equal (n08 n)
                  n))
  :hints (("Goal" :in-theory (enable n08 n08p))))

(defthm |(n32 n)|
  (implies (n32p n)
           (equal (n32 n)
                  n))
  :hints (("Goal" :in-theory (enable n32 n32p))))

(defthm |(n08p (n08 x))|
  (implies (integerp n)
           (n08p (n08 n)))
  :hints (("Goal" :in-theory (enable n08 n08p))))

(defthm |(n32p (n32 x))|
  (implies (integerp x)
           (n32p (n32 x)))
  :hints (("Goal" :in-theory (enable n32p n32))))

(defthm |(n32+ x y)|
  (implies (n32p (+ x y))
           (equal (n32+ x y)
                  (+ x y)))
  :hints (("Goal" :in-theory (enable n32+))))

(defthm |(n32p (n32+ x y))|
  (implies (and (integerp x)
		(integerp y))
	   (n32p (n32+ x y)))
  :hints (("Goal" :in-theory (enable n32+
				     |(n32p (n32 x))|))))

 (defthm |(word-aligned-p (word-align x))|
   (implies (<= 0 x)
            (word-aligned-p (word-align x)))
   :hints (("Goal" :in-theory (enable word-aligned-p
                                      word-align)
            :use ((:instance mod-logand
                             (x x)
                             (y 4294967292)
                             (n 2))))))

 (defthm |(word-align x)|
   (implies (and (n32p x)
                 (word-aligned-p x))
            (equal (word-align x)
                   x))
   :hints (("Goal" :in-theory (enable word-aligned-p
                                      word-align)
            :use ((:instance logand-floor-expt-2-n
                             (x x)
                             (y 4294967292)
                             (n 2))))))

(defthm n32+-when-word-aligned
  (implies (and (integerp n)
                (<= 0 n)
                (< n 4)
                (n32p x)
                (word-aligned-p x))
           (equal (n32+ n x)
                  (+ n x)))
   :hints (("Goal" :in-theory (enable word-aligned-p
                                      word-align
                                      n32p
                                      n32+))))

;;; Some minor math theorems

(defthm binary-logand-<=
  (implies (and (natp m)
                (natp n))
           (<= (binary-logand m n) m))
  :hints (("Goal" :cases ((= m 0))))
  :rule-classes :linear)

(defthm binary-logand->=-0
  (implies (or (natp m)
	       (natp n))
	   (>= (binary-logand m n) 0))
  :rule-classes :linear)

(defthm n32p-binary-logand
  (implies (and (n32p m)
		(natp n))
	   (n32p (binary-logand m n)))
  :hints (("Goal" :in-theory (enable n32p
				     binary-logand->=-0)
	   :use binary-logand-<=)))
