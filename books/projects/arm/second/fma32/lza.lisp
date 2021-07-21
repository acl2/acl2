;; David Russinoff <david.russinoff@arm.com>
;; Cuong Chau <cuong.chau@arm.com>

;; June 2021

(in-package "RTL")

(include-book "fma32")
(include-book "projects/arm/utils/rtl-utils" :dir :system)

;; ======================================================================

(DEFUND LZAGUTS (ADD1 ADD2)
  (LET* ((GEN (LOGAND ADD1 ADD2))
         (PROP (LOGXOR ADD1 ADD2))
         (KILL (BITS (LOGNOT (LOGIOR ADD1 ADD2)) 51 0))
         (PATSUB (BITS (LOGXOR (BITS PROP 52 1) GEN)
                       50 0))
         (PATADD (BITS (LOGXOR (BITS PROP 52 1) KILL)
                       50 0)))
        (BITS (LOGNOT (LOGIOR (LOGAND (BITS PATSUB 49 0)
                                      (BITS PATSUB 50 1))
                              (LOGAND (BITS PATADD 49 0)
                                      (BITS PATADD 50 1))))
              49 0)))

(defthm lza52-lemma
  (equal (lza52 add1 add2 sumexp)
         (let* ((VEC (lzaguts add1 add2))
                (VEC (IF1 (LOG<= SUMEXP 971)
                          (SETBITN VEC 77 (- 972 SUMEXP) 1)
                          VEC)))
           (CLZ77 VEC)))
  :hints (("Goal" :in-theory (enable lza52 lzaguts))))

(def-gl-rule lza-pos-lemma-gl
  :hyp
  (and (bvecp x 52)
       (bvecp y 52)
       (> (+ x y) (expt 2 52))
       (or (not (= (bitn x 51) (bitn y 51)))
           (and (= (bitn x 50) 0)
	        (= (bitn y 50) 0))))
  :concl
  (and (> (lzaGuts x y) 0)
       (or (= (expo (bits (+ x y) 50 0))
              (expo (lzaGuts x y)))
           (= (expo (bits (+ x y) 50 0))
              (1+ (expo (lzaGuts x y)))))
       (or (= (expo (bits (+ x y 1) 50 0))
              (expo (lzaGuts x y)))
           (= (expo (bits (+ x y 1) 50 0))
              (1+ (expo (lzaGuts x y))))))
  :disabledp t
  :g-bindings
  (gl::auto-bindings (:mix (:nat x 52) (:nat y 52))))

(def-gl-rule lza-neg-lemma-gl
  :hyp
  (and (bvecp x 52)
       (bvecp y 52)
       (< (+ x y) (- (expt 2 52) 2))
       (or (equal (bitn x 51) 1)
           (equal (bitn y 51) 1)))
  :concl
  (and (> (lzaGuts x y) 0)
       (or (= (expo (bits (lognot (+ x y)) 50 0))
              (expo (lzaGuts x y)))
           (= (expo (bits (lognot (+ x y)) 50 0))
              (1+ (expo (lzaGuts x y)))))
       (or (= (expo (bits (lognot (+ x y 1)) 50 0))
              (expo (lzaGuts x y)))
           (= (expo (bits (lognot (+ x y 1)) 50 0))
              (1+ (expo (lzaGuts x y))))))
  :disabledp t
  :g-bindings
  (gl::auto-bindings (:mix (:nat x 52) (:nat y 52))))

(def-gl-rule lza-zero-lemma-gl
  :hyp
  (and (bvecp x 52)
       (bvecp y 52)
       (<= (- (expt 2 52) 2) (+ x y))
       (<= (+ x y) (expt 2 52)))
  :concl
  (equal (lzaGuts x y) 0)
  :g-bindings
  (gl::auto-bindings (:mix (:nat x 52) (:nat y 52))))

