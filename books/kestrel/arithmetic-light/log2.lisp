; (Floor of) base-2 logarithm (works on all positive rationals)
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See also lg.lisp and ceiling-of-lg.lisp.

(local (include-book "expt2"))
(local (include-book "plus"))
(local (include-book "floor"))
(local (include-book "divide"))
(local (include-book "times"))
(local (include-book "times-and-divide"))

;; TODO: Without these, some things below are very slow
(local (in-theory (disable <-of-*-and-*-same-linear-3
                           <-of-*-and-*-same-linear-1
                           <-of-*-and-*-same-linear-2
                           ;floor-upper-bound-linear
                           ;my-floor-lower-bound-linear
                           <-of-*-same-linear-special
                           <=-of-*-and-*-same-alt-linear
                           <=-of-*-and-*-same-linear)))

;; Returns the floor of the base 2 logarithm of the positive rational x.  Not meaningful for 0.
;; TODO: Rename log2 to floor-of-log2 ?
;; TODO: Generalize the base?
(defund log2 (x)
  (declare (xargs :guard (and (rationalp x)
                              (< 0 x))
                  :measure (if (and (rationalp x)
                                    (< 0 x))
                               (if (<= 2 x)
                                   (floor x 1)
                                 (if (< x 1)
                                     (floor (/ x) 1)
                                   0))
                             0)))
  (if (not (mbt (and (rationalp x)
                     (< 0 x))))
      0 ; todo: what value should we use here (negative infinity)?
    (if (<= 2 x)
        (+ 1 (log2 (/ x 2)))
      (if (< x 1)
          (+ -1 (log2 (* x 2)))
        ;; x is in [1,2), so it's log2 is 0:
        0))))

(defthm natp-of-log2-type
  (implies (and (<= 1 x)
                (rationalp x))
           (natp (log2 x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable log2))))

(defthm posp-of-log2-type
  (implies (and (<= 2 x)
                (rationalp x))
           (posp (log2 x)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable log2))))

(defthm negative-of-log2-type
  (implies (and (< x 1)
                (< 0 x)
                (rationalp x))
           (< (log2 x) 0))
  :rule-classes :type-prescription
  :hints (("Goal"; :expand (log2 x)
           :induct (log2 x)
           :in-theory (e/d (log2)
                           (;; for speed:
                            <-of-*-and-*-same-linear-4
                            <-of-*-and-*-linear
                            commutativity-of-*)))))

;; Could loop with the definition?
(defthm log2-of-*-of-2
  (implies (and (< 0 x)
                (rationalp x))
           (equal (log2 (* 2 x))
                  (+ 1 (log2 x))))
  :hints (("Goal" :in-theory (enable log2))))

;; Could loop with the definition?
(defthm log2-of-*-of-1/2
  (equal (log2 (* 1/2 x))
         (if (and (rationalp x)
                  (< 0 x))
             ;; usual case:
             (+ -1 (log2 x))
           0))
  :hints (("Goal" :in-theory (enable log2))))

(defthm log2-of-expt
  (implies (integerp i)
           (equal (log2 (expt 2 i))
                  i))
  :hints (("Goal" :in-theory (enable log2 (:i expt) expt-of-+))))

(defthmd log2-of-both-sides
  (implies (equal x y)
           (equal (log2 x) (log2 y))))

(local
 (defun log2-double-induct (x y)
   (declare (xargs :measure (if (and (rationalp x)
                                     (< 0 x))
                                (if (<= 2 x)
                                    (floor x 1)
                                  (if (< x 1)
                                      (floor (/ x) 1)
                                    0))
                              0)))
   (if (not (mbt (and (rationalp x)
                      (< 0 x))))
       (list x y)
     (if (<= 2 x)
         (+ 1 (log2-double-induct (/ x 2) (/ y 2)))
       (if (< x 1)
           (+ -1 (log2-double-induct (* x 2) (* 2 y)))
         ;; x is in [1,2), so it's log2 is 0:
         0)))))

(defthm log2-monotonic-weak
  (implies (and (<= x y)
                (< 0 x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (<= (log2 x) (log2 y)))
  :hints (("Goal" :induct (log2-double-induct x y)
           :in-theory (enable log2))))

;; Unlike power-of-2p, this isn't restricted to integers.  Rename that one?
(defund rat-power-of-2p (x)
  (declare (xargs :guard (and (rationalp x)
                              (< 0 x))))
  (equal (expt 2 (log2 x))
         x))

(defthm equal-of-expt2-and-constant-gen
  (implies (and (syntaxp (and (quotep k)
                              (not (quotep i)) ; avoids loops if (:e expt) is disabled
                              ))
                (integerp i))
           (equal (equal (expt 2 i) k)
                  (and (rat-power-of-2p k) ; gets evaluated
                       (equal i (log2 k)))))
  :hints (("Goal" :in-theory (enable rat-power-of-2p)
           :use ((:instance log2-of-both-sides (x (expt 2 i)) (y k))))))

(defthm log2-monotonic-strong-when-power-of-2p
  (implies (and (< x y)
                (rat-power-of-2p y)
                (< 0 x)
                (< 0 y)
                (rationalp x)
                (rationalp y))
           (< (log2 x) (log2 y)))
  :hints (("Goal" :induct (log2-double-induct x y)
           :in-theory (enable log2 expt-of-+ rat-power-of-2p))))

(defthm equal-of-0-and-log2
  (implies (and (< 0 x)
                (rationalp x))
           (equal (equal 0 (log2 x))
                  (and (<= 1 x)
                       (< x 2))))
  :hints (("Goal" :expand (log2 x)
           :induct (log2 x)
           :in-theory (enable (:i log2)))))

(defthm posp-of-log2
  (implies (and (rationalp x)
                (< 0 x))
           (equal (posp (log2 x))
                  (<= 2 x)))
  :hints (("Goal" :in-theory (enable log2))))

(defthm natp-of-log2
  (implies (and (rationalp x)
                (< 0 x))
           (equal (natp (log2 x))
                  (<= 1 x)))
  :hints (("Goal" ;:cases ((< 1 x) (equal 1 x))
           :in-theory (enable log2 integer-length))))

;; These next two help show that LOG2 is correct:

(defthm <=-of-expt-2-of-log2-linear
  (implies (and (rationalp x)
                (< 0 x))
           (<= (expt 2 (log2 x)) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable log2))))

(defthm <=-of-expt-2-of-+-of-1-and-log2-linear
  (implies (rationalp x)
           (< x (expt 2 (+ 1 (log2 x)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable log2 expt-of-+))))

(defthm <=-of-expt-2-of-+-of-1-and-log2-linear-alt
  (implies (rationalp x)
           (< x (* 2 (expt 2 (log2 x)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable log2 expt-of-+))))

(defthm <-of-*-of-2-and-expt-of-log2-same
  (implies (rationalp x)
           (< x (* 2 (expt 2 (log2 x)))))
  :hints (("Goal" :use (:instance <=-of-expt-2-of-+-of-1-and-log2-linear)
           :in-theory (e/d (expt-of-+)
                           (<=-of-expt-2-of-+-of-1-and-log2-linear)))))

(defthm <-of-expt-2-of-log2-same
  (implies (and (rationalp x)
                (< 0 x))
           (equal (< (expt 2 (log2 x)) x)
                  (not (rat-power-of-2p x))))
  :hints (("Goal" :in-theory (enable log2 rat-power-of-2p))))

(defthm <-of-expt-2-of-log2-same-linear
  (implies (and (not (rat-power-of-2p x))
                (rationalp x)
                (< 0 x))
           (< (expt 2 (log2 x)) x))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (log2)
                                  (<=-of-expt-2-of-log2-linear ; for speed
                                   )))))

;; todo: Gen to any constant
(defthm <-of-log2-and-0
  (implies (and (rationalp x)
                (< 0 x))
           (equal (< (log2 x) 0)
                  (< x 1)))
  :hints (("Goal" :in-theory (enable log2))))

(defthmd <-of-log2-when-unsigned-byte-p
  (implies (and (unsigned-byte-p n x)
                (< 0 x))
           (< (log2 x) n))
  :hints (("Goal" ;:cases ((equal x 0))
           :in-theory (enable log2))))

(defthm <-of-log2-when-unsigned-byte-p-cheap
  (implies (and (unsigned-byte-p n x)
                (< 0 x))
           (< (log2 x) n))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :cases ((equal x 0))
           :in-theory (enable log2))))

;todo: log2 of mask?

(local
  (defun log2i (x i)
  (declare (xargs :measure
                  (if (and (rationalp x) (< 0 x))
                      (if (<= 2 x)
                          (floor x 1)
                        (if (< x 1) (floor (/ x) 1) 0))
                    0)))
  (if (not (mbt (and (rationalp x) (< 0 x))))
      (list x i)
    (if (<= 2 x)
        (+ 1 (log2i (/ x 2) (+ -1 i)))
      (if (< x 1) (+ -1 (log2i (* x 2) (+ 1 i))) 0)))))

;quite powerful
(defthm log2-must-be
  (implies (and (<= (expt 2 i) x)
                (< x (expt 2 (+ 1 i)))
                (rationalp x)
                (integerp i))
           (equal (log2 x)
                  i))
  :hints (("Subgoal *1/4" :cases ((< i 0) (> i 0)))
          ("Goal" :induct (log2i x i)
           :in-theory (enable log2 expt-of-+))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthmd log2-of-+-of--1-when-power-of-2p
    (implies (and (integerp n)
                  (equal n (expt 2 (log2 n))) ; power of 2
                  (<= 2 n) ; avoids log2 of 0
                  )
             (equal (log2 (+ -1 n))
                    (+ -1 (log2 n))))
    :hints (("Goal" :use (:instance log2-must-be
                                    (x (+ -1 n))
                                    (i (+ -1 (log2 n))))
             :in-theory (disable log2-must-be)))))

(local
  (defthmd log2-of-+-of--1-when-not-power-of-2p
    (implies (and (integerp n)
                  (not (equal n (expt 2 (log2 n)))) ; not a power of 2
                  (<= 2 n) ; avoids log2 of 0
                  )
             (equal (log2 (+ -1 n))
                    (log2 n)))
    :hints (("Goal" :use (:instance log2-must-be
                                    (x (+ -1 n))
                                    (i (log2 n)))
           :in-theory (disable log2-must-be)))))

(defthm log2-of-+-of--1
  (implies (and (integerp n)
                (<= 2 n) ; avoids log2 of 0
                )
           (equal (log2 (+ -1 n))
                  (if (equal n (expt 2 (log2 n))) ;power of 2
                      (+ -1 (log2 n))
                    (log2 n))))
  :hints (("Goal" :in-theory (enable log2-of-+-of--1-when-not-power-of-2p
                                     log2-of-+-of--1-when-power-of-2p))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
  (defthmd log2-of-+-of-1-when-almost-power-of-2p
    (implies (and (integerp n)
                  (equal n (+ -1 (expt 2 (+ 1 (log2 n))))) ; almost the next power of 2
                  (<= 1 n)
                  )
             (equal (log2 (+ 1 n))
                    (+ 1 (log2 n))))
    :hints (("Goal" :use (:instance log2-must-be
                                    (x (+ 1 n))
                                    (i (+ 1 (log2 n))))
             :in-theory (disable log2-must-be)))))

(local
  (defthmd log2-of-+-of-1-when-not-almost-power-of-2p
    (implies (and (integerp n)
                  (not (equal n (+ -1 (expt 2 (+ 1 (log2 n)))))) ; not almost the next power of 2
                  (<= 1 n)
                  )
             (equal (log2 (+ 1 n))
                    (log2 n)))
    :hints (("Goal" :use (:instance log2-must-be
                                    (x (+ 1 n))
                                    (i (log2 n)))
             :in-theory (disable log2-must-be)))))

(defthm log2-of-+-of-1
  (implies (and (integerp n)
                (<= 1 n))
           (equal (log2 (+ 1 n))
                  (if (equal n (+ -1 (expt 2 (+ 1 (log2 n))))) ;almost the next power of 2
                      (+ 1 (log2 n))
                    (log2 n))))
  :hints (("Goal" :in-theory (enable log2-of-+-of-1-when-almost-power-of-2p
                                     log2-of-+-of-1-when-not-almost-power-of-2p))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defthm log2-of-floor-by-1
  (implies (and (<= 1 x) ; avoids log2 of 0
                (rationalp x))
           (equal (log2 (floor x 1))
                  (log2 x)))
  :hints (("Goal" :use (:instance log2-must-be
                                  (x (floor x 1))
                                  (i (log2 x)))
           :in-theory (disable log2-must-be))))
