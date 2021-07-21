;; David Russinoff <david.russinoff@arm.com>

;; June 2021

(in-package "RTL")

(include-book "fma32")
(include-book "projects/arm/utils/rtl-utils" :dir :system)

(local (arith-5-for-rtl))

;; ======================================================================

(defun gp-alt (x y n)
  (let ((g1 (logand1 (bitn x n) (bitn y n)))
        (p1 (log<> (bitn x n) (bitn y n))))
    (if (zp n)
        (mv g1 p1)
      (mv-let (g p) (gp-alt x y (1- n))
        (mv (setbitn g (1+ n) n (logior1 g1 (logand1 p1 (bitn g (1- n)))))
	    (setbitn p (1+ n) n (logand1 p1 (bitn p (1- n)))))))))

(defthmd gp-alt-lemma-1
  (implies (and (natp n)
                (natp x)
                (natp y))
           (mv-let (g p) (gp-alt x y n)
             (and (= (bitn g n)
                     (if (>= (+ (bits x n 0) (bits y n 0)) (expt 2 (1+ n)))
                         1 0))
                  (= (bitn p n)
                     (if (= (+ (bits x n 0) (bits y n 0)) (1- (expt 2 (1+ n))))
                         1 0)))))
  :hints (("Subgoal *1/2" :nonlinearp t
                          :in-theory (enable bitn-cat)
                          :use (bitn-0-1
			        (:instance bitn-0-1 (x y))
				(:instance bitn-plus-bits (m 0))
				(:instance bitn-plus-bits (x y) (m 0))
				(:instance bits-bounds (i (1- n)) (j 0))
				(:instance bits-bounds (x y) (i (1- n)) (j 0))))))

(defthmd gp-alt-lemma-2
  (implies (and (natp m)
                (natp n)
		(<= n m)
                (natp x)
                (natp y))
           (mv-let (gm pm) (gp-alt x y m)
	     (mv-let (gn pn) (gp-alt x y n)
               (and (= (bitn gm n) (bitn gn n))
	            (= (bitn pm n) (bitn pn n))))))
  :hints (("Goal" :in-theory (enable bitn-cat))))

(def-gl-rule hc52-lemma-gl
  :hyp (and (bvecp x 52) (bvecp y 52))
  :concl (equal (hc52 (logand x y) (logxor x y))
                (gp-alt x y 51))
  :disabledp t
  :g-bindings (gl::auto-bindings (:mix (:nat x 52) (:nat y 52))))

(defthmd hc52-lemma-1
  (implies (and (bvecp x 52) (bvecp y 52) (natp n) (< n 52))
           (mv-let (g p) (hc52 (logand x y) (logxor x y))
             (and (= (bitn g n)
                     (if (>= (+ (bits x n 0) (bits y n 0)) (expt 2 (1+ n)))
                         1 0))
                  (= (bitn p n)
                     (if (= (+ (bits x n 0) (bits y n 0)) (1- (expt 2 (1+ n))))
                         1 0)))))
  :hints (("Goal"
           :in-theory (disable hc52 gp-alt)
           :use (hc52-lemma-gl
                 gp-alt-lemma-1
                 (:instance gp-alt-lemma-2 (m 51))))))

(def-gl-rule hc52-lemma-2
  :hyp
  (and (bvecp x 52) (bvecp y 52))
  :concl
  (mv-let (g p) (hc52 (logand x y) (logxor x y))
    (declare (ignore p))
    (equal (+ x y)
           (logxor (logxor x y)
	           (setbits 0 53 52 1 g))))
  :g-bindings (gl::auto-bindings (:mix (:nat x 52) (:nat y 52)))
  :rule-classes nil)

(def-gl-rule hc52-lemma-3
  :hyp
  (and (bvecp x 52) (bvecp y 52))
  :concl
  (mv-let (g p) (hc52 (logand x y) (logxor x y))
    (equal (+ x y 1)
           (logxor (logxor x y)
	           (logior (setbits 0 53 52 1 g)
		           (setbits 1 53 52 1 p)))))
  :g-bindings (gl::auto-bindings (:mix (:nat x 52) (:nat y 52)))
  :rule-classes nil)

(def-gl-rule hc52-lemma-4
  :hyp (and (bvecp x 52) (bvecp y 52))
  :concl (mv-let
           (g p)
           (hc52 (logand x y) (logxor x y))
           (and (equal (equal (bitn g 51) 1)
                       (<= *2^52* (+ x y)))
                (equal (equal (bitn p 51) 1)
                       (equal (+ x y)
                              (1- *2^52*)))))
  :g-bindings (gl::auto-bindings (:mix (:nat x 52) (:nat y 52)))
  :rule-classes nil)
