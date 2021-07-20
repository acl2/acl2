; Versions of built-in functions with guards of t
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book defines functions that are equivalent to ACL2 built-in functions
;; but have guards of t (for use in evaluators).

;; Disable certification of this book in ACL2(r), due to differences in FLOOR:
; cert_param: (non-acl2r)

(include-book "unguarded-primitives")

(defund mv-nth-unguarded (n x)
  (declare (xargs :guard t))
  (mv-nth (nfix n) x))

;supports the correctness of the evaluator
(defthm mv-nth-unguarded-correct
  (equal (mv-nth-unguarded n x)
         (mv-nth n x))
  :hints (("Goal" :in-theory (enable mv-nth
                                     mv-nth-unguarded))))

(defund zp-unguarded (x)
  (declare (xargs :guard t))
  (zp (nfix x)))

(defthm zp-unguarded-correct
  (equal (zp-unguarded x)
         (zp x))
  :hints (("Goal" :in-theory (enable zp-unguarded))))

(defund assoc-equal-unguarded (x alist)
  (declare (xargs :guard t))
  (cond ((atom alist) nil)
        ((equal x (car-unguarded (car-unguarded alist)))
         (car-unguarded alist))
        (t (assoc-equal-unguarded x (cdr-unguarded alist)))))

(defthm assoc-equal-unguarded-correct
  (equal (assoc-equal-unguarded x alist)
         (assoc-equal x alist))
  :hints (("Goal" :in-theory (enable assoc-equal
                                     assoc-equal-unguarded))))

(defund symbol<-unguarded (x y)
  (declare (xargs :guard t))
  (let ((x1 (if (symbolp x) (symbol-name x) ""))
        (y1 (if (symbolp y) (symbol-name y) "")))
       (or (string< x1 y1)
           (and (equal x1 y1)
                (string< (if (symbolp x) (symbol-package-name x) "")
                         (if (symbolp y) (symbol-package-name y) ""))))))

(defthm symbol<-unguarded-correct
  (equal (symbol<-unguarded x y)
         (symbol< x y))
  :hints (("Goal" :in-theory (enable symbol<-unguarded symbol<))))

(defund numerator-unguarded (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (numerator x)
    0))

(defthm numerator-unguarded-correct
  (equal (numerator-unguarded x)
         (numerator x))
  :hints (("Goal" :in-theory (enable numerator-unguarded))))

(defund denominator-unguarded (x)
  (declare (xargs :guard t))
  (if (rationalp x)
      (denominator x)
    1))

(defthm denominator-unguarded-correct
  (equal (denominator-unguarded x)
         (denominator x))
  :hints (("Goal" :in-theory (enable denominator-unguarded))))

(defund nonnegative-integer-quotient-unguarded (i j)
  (declare (xargs :guard t))
  (if (or (= (nfix j) 0) (< (ifix i) j))
      0
    (nonnegative-integer-quotient i j)))

(defthm nonnegative-integer-quotient-unguarded-correct
  (equal (nonnegative-integer-quotient-unguarded x y)
         (nonnegative-integer-quotient x y))
  :hints (("Goal" :in-theory (enable nonnegative-integer-quotient
                                     nonnegative-integer-quotient-unguarded))))

(defund floor-unguarded (i j)
  (declare (xargs :guard t))
  (if (and (real/rationalp i)
           (real/rationalp j)
           (not (equal j 0)))
      (floor i j)
    ;; may be slow:
    (let* ((q (binary-*-unguarded i (unary-/-unguarded j)))
           (n (numerator-unguarded q))
           (d (denominator-unguarded q)))
      (cond ((= d 1) n)
            ((>= n 0)
             (nonnegative-integer-quotient-unguarded n d))
            (t (+ (- (nonnegative-integer-quotient-unguarded (- n) d))
                  -1))))))

;; Doesn't work in ACL2(r)
(defthm floor-unguarded-correct
  (equal (floor-unguarded x y)
         (floor x y))
  :hints (("Goal" :in-theory (enable floor
                                     floor-unguarded))))

(defund ceiling-unguarded (i j)
  (declare (xargs :guard t))
  (if (and (rationalp i)
           (rationalp j)
           (not (equal j 0)))
      (ceiling i j)
    ;; may be slow:
    (let* ((q (binary-*-unguarded i (unary-/-unguarded j)))
           (n (numerator-unguarded q))
           (d (denominator-unguarded q)))
      (cond ((= d 1) n)
            ((>= n 0)
             (+ (nonnegative-integer-quotient-unguarded n d)
                1))
            (t (- (nonnegative-integer-quotient-unguarded (- n)
                                                          d)))))))

(defthm ceiling-unguarded-correct
  (equal (ceiling-unguarded i j)
         (ceiling i j))
  :hints (("Goal" :in-theory (enable ceiling
                                     ceiling-unguarded))))

(defund mod-unguarded (x y)
  (declare (xargs :guard t))
  (- (fix x) (binary-*-unguarded (floor-unguarded x y) y)))

(defthm mod-unguarded-correct
  (equal (mod-unguarded x y)
         (mod x y))
  :hints (("Goal" :in-theory (enable mod
                                     mod-unguarded))))

(defund endp-unguarded (x)
  (declare (xargs :guard t))
  (atom x))

(defthm endp-unguarded-correct
  (equal (endp-unguarded x)
         (endp x)))

(defund min-unguarded (x y)
  (declare (xargs :guard t))
  (if (<-unguarded x y) x y))

(defthm min-unguarded-correct
  (equal (min-unguarded x y)
         (min x y))
  :hints (("Goal" :in-theory (enable <-unguarded-correct
                                     min-unguarded))))

(defund max-unguarded (x y)
  (declare (xargs :guard t))
  (if (<-unguarded y x) x y))

(defthm max-unguarded-correct
  (equal (max-unguarded x y)
         (max x y))
  :hints (("Goal" :in-theory (enable <-unguarded-correct
                                     max-unguarded))))

(defund integer-length-unguarded (x)
  (declare (xargs :guard t))
  (integer-length (ifix x)))

(defthm integer-length-unguarded-correct
  (equal (integer-length-unguarded x)
         (integer-length x))
  :hints (("Goal" :in-theory (enable integer-length
                                     integer-length-unguarded))))

;; ;; We don't want to evaluate calls to return-last, because that will naturally evaluate the eager arg
;; (defund return-last-unguarded (fn eager-arg last-arg)
;;   (declare (xargs :guard t)
;;            (ignore fn eager-arg))
;;   last-arg)

;; (defthm return-last-unguarded-correct
;;   (equal (return-last-unguarded fn eager-arg last-arg)
;;          (return-last fn eager-arg last-arg))
;;   :hints (("Goal" :in-theory (enable return-last
;;                                      return-last-unguarded))))

(defund =-unguarded (x y)
  (declare (xargs :guard t))
  (equal x y))

(defthm =-unguarded-correct
  (equal (=-unguarded x y)
         (= x y))
  :hints (("Goal" :in-theory (enable =-unguarded))))

;optimize?
(defund nth-unguarded (n l)
  (declare (xargs :guard t))
  (if (true-listp l)
      (nth (nfix n) l)
    (nth (nfix n) (true-list-fix l))))

(defthm nth-unguarded-correct
  (equal (nth-unguarded n l)
         (nth n l))
  :hints (("Goal" :in-theory (enable nth nth-unguarded))))

;TODO use fix functions here?
(defund expt-unguarded (r i)
  (declare (xargs :guard t))
  (cond ((not (integerp i)) 1)
        ((equal 0 i) 1)
        ((= (fix r) 0) 0)
        (t (expt r i))))

(defthm expt-unguarded-correct
  (equal (expt-unguarded r i)
         (expt r i))
  :hints (("Goal" :in-theory (enable expt-unguarded expt))))

(defund binary-append-unguarded (x y)
  (declare (xargs :guard t))
  (if (true-listp x)
      (append x y)
    (append (true-list-fix x) y)))

(defthm binary-append-unguarded-correct
  (equal (binary-append-unguarded x y)
         (binary-append x y))
  :hints (("Goal" :in-theory (enable binary-append-unguarded))))
