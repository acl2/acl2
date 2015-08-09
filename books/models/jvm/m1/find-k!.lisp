; A Faster Calculation of Find-K
; J Strother Moore
; Sun Apr 15 17:09:07 2012

; The *Rogers-tm* starting in state Q0 and *example-tape* takes:
; 291,202,253,588,734,484,219,274,297,505,568,945,357,129,888,612,375,663,883 M1 steps
; which is between 10^56 and 10^57.

; Rest of these comments out of date...

; In the Turing Equivalence of M1, we establish that a certain program *pi*
; simulates a Turing machine computation of length n, i.e., (tmi st tape tm n),
; in (find-k st! tape! pos! tm! w! n), where st!, tape!, pos!, tm!, and w! are the
; M1 representations of st, tape, and tm.  (Pos! is the initial ``read/write
; pointer'' into the M1 representation of the initial tape and w! is a
; bit-width used in the encoding of tm.)

; In the equivalence file we demonstrate a simple Turing machine which doubles
; the number of 1s on the tape.  This machine, shown in Rogers and demonstrated
; in the Equivalence Proof file, takes 78 steps to double 4 (1111).  How long
; does it take M1 to do that same computation?

; As defined for the equivalence proof, k computes a schedule -- a list of
; TICKS of the appropriate length.  That definition of k in principal gives us
; a way to answer the question above.  However, the number of M1 steps required
; to do even simple Turing machine simulations is prohibitive because the
; machine is coded as a bit-string and M1 does less-than, floor, and mod by
; successive subtractions, e.g., an exponentially large number is being
; decremented.

; Because of the recursive method of defining the schedule functions --
; necessary for the M1 code proofs -- it is also simply impractical to compute
; schedules -- or their lengths -- directly from the definitions.  It is
; necessary to produce closed form arithmetic expressions for the most basic
; operations, e.g., less than, floor, mod, etc., before it becomes practical to
; even compute how many steps are needed.

; We do that here. Indeed, we define a function find-k!, prove that it is
; equivalent to the k used in the equivalence proof, and then run it
; on the Rogers machine for the 78-step computation.  The answer to the question
; is that it takes M1:

; 103,979,643,405,139,456,340,754,264,791,057,682,257,947,240,629,585,359,596

; steps to simulate that computation.  That is slightly more than 10^56.

; ---

;(include-book "theorems-a-and-b")
;(certify-book "find-k!" 1)
(in-package "M1")

(in-theory (enable binary-clk+))

(defun fast-lessp-loop-clock (x y)
  (+ (if (< x y) 6 3) (* 13 (acl2::min x y))))

(defthm lessp-loop-clock-lemma
  (implies (and (natp x)
                (natp y))
           (equal (lessp-loop-clock x y)
                  (fast-lessp-loop-clock x y)))
  :hints (("Goal" :in-theory (enable lessp-loop-clock))))

(in-theory (disable lessp-loop-clock))

(defun fast-lessp-clock (ret-pc x y)
  (+ 15 (+ (if (< x y) 6 3) (* 13 (acl2::min x y))) (exit-clock 'lessp ret-pc)))

(defthm fast-lessp-clock-lemma
  (implies (and (natp x)
                (natp y))
           (equal (lessp-clock ret-pc x y)
                  (fast-lessp-clock ret-pc x y)))
  :hints (("Goal" :in-theory (enable lessp-clock))))

(in-theory (disable fast-lessp-clock))

(defun fast-mod-loop-clock (x y)
  (+ (* (+ 12 (fast-lessp-clock '(0 1) x y)) (floor x y))
     (+ 7 (fast-lessp-clock '(0 1) (mod x y) y))))


(defthm fast-mod-loop-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0)))
           (equal (mod-loop-clock x y)
                  (fast-mod-loop-clock x y)))
  :hints (("Goal" :in-theory (enable mod-loop-clock fast-lessp-clock fast-lessp-loop-clock))))

(defthm natp-fast-mod-loop-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0)))
           (natp (fast-mod-loop-clock x y)))
  :hints (("Goal" :in-theory (enable mod-loop-clock fast-lessp-clock fast-lessp-loop-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0)))
                                      (integerp (fast-mod-loop-clock x y))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0)))
                                      (<= 0 (fast-mod-loop-clock x y))))))

(in-theory (disable fast-mod-loop-clock))

(defun fast-mod-clock (ret-pc x y)
  (+ 15 (fast-mod-loop-clock x y) (exit-clock 'mod ret-pc)))

(defthm fast-mod-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0)))
           (equal (mod-clock ret-pc x y)
                  (fast-mod-clock ret-pc x y)))
  :hints (("Goal" :in-theory (enable mod-clock))))

(defthm natp-fast-mod-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0)))
           (natp (fast-mod-clock ret-pc x y)))
  :hints (("Goal" :in-theory (enable mod-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0)))
                                      (integerp (fast-mod-clock ret-pc x y))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0)))
                                      (<= 0 (fast-mod-clock ret-pc x y))))))

(in-theory (disable fast-mod-clock))

(defun fast-floor-loop-clock (x y)
  (+ (* (+ 16 (fast-lessp-clock '(0 2) x y))
        (floor x y))
     (+ 7 (fast-lessp-clock '(0 2) (mod x y) y))))

(defthm fast-floor-loop-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0))
                (natp a))
           (equal (floor-loop-clock x y a)
                  (fast-floor-loop-clock x y)))
  :hints (("Goal" :in-theory (enable floor-loop-clock fast-lessp-clock fast-lessp-loop-clock))))

(defthm natp-fast-floor-loop-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0))
                (natp a))
           (natp (fast-floor-loop-clock x y)))
  :hints (("Goal" :in-theory (enable floor-loop-clock fast-lessp-clock fast-lessp-loop-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0))
                                           (natp a))
                                      (integerp (fast-floor-loop-clock x y))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0))
                                           (natp a))
                                      (<= 0 (fast-floor-loop-clock x y))))))

(in-theory (disable fast-floor-loop-clock))

(defun fast-floor-clock (ret-pc x y)
  (+ 20 (fast-floor-loop-clock x y) (exit-clock 'floor ret-pc)))

(defthm fast-floor-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0))
                (natp a))
           (equal (floor-clock ret-pc x y a)
                  (fast-floor-clock ret-pc x y)))
  :hints (("Goal" :in-theory (enable floor-clock))))

(defthm natp-fast-floor-clock-lemma
  (implies (and (natp x)
                (natp y)
                (not (equal y 0))
                (natp a))
           (natp (fast-floor-clock ret-pc x y)))
  :hints (("Goal" :in-theory (enable floor-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0))
                                           (natp a))
                                      (integerp (fast-floor-clock ret-pc x y))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp y)
                                           (not (equal y 0))
                                           (natp a))
                                      (<= 0 (fast-floor-clock ret-pc x y))))))

(in-theory (disable fast-floor-clock))

(defun fast-log2-loop-clock (x)
  (if (zp x)
      3
      (if (equal x 1)
          8
          (+ 17 (fast-floor-clock '(0 2 2 3) x 2)
             (fast-log2-loop-clock (floor x 2))))))

(defthm fast-log2-loop-clock-lemma
  (implies (and (natp x)
                (natp a))
           (equal (log2-loop-clock x a)
                  (fast-log2-loop-clock x)))
  :hints (("Goal" :in-theory (enable log2-loop-clock))))

(defthm natp-fast-log2-loop-clock-lemma
  (implies (and (natp x)
                (natp a))
           (natp (fast-log2-loop-clock x)))
  :hints (("Goal" :in-theory (enable log2-loop-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp a))
                                      (integerp (fast-log2-loop-clock x))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp a))
                                      (<= 0 (fast-log2-loop-clock x))))))

(in-theory (disable fast-log2-loop-clock))

(defun fast-log2-clock (ret-pc x)
  (+ 15
     (fast-log2-loop-clock x)
     (exit-clock 'log2 ret-pc)))

(defthm fast-log2-clock-lemma
  (implies (and (natp x)
                (natp a))
           (equal (log2-clock ret-pc x a)
                  (fast-log2-clock ret-pc x)))
  :hints (("Goal" :in-theory (enable log2-clock))))

(defthm natp-fast-log2-clock-lemma
  (implies (and (natp x)
                (natp a))
           (natp (fast-log2-clock ret-pc x)))
  :hints (("Goal" :in-theory (enable log2-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp a))
                                      (integerp (fast-log2-clock ret-pc x))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp a))
                                      (<= 0 (fast-log2-clock ret-pc x))))))

(in-theory (disable fast-log2-clock))

(defun fast-expt-loop-clock (n)
  (+ 3 (* 13 n)))

(defthm fast-expt-loop-clock-lemma
  (implies (and (natp x)
                (natp n)
                (natp a))
           (equal (expt-loop-clock x n a)
                  (fast-expt-loop-clock n)))
  :hints (("Goal" :in-theory (enable expt-loop-clock))))

(defthm natp-fast-expt-loop-clock-lemma
  (implies (and (natp x)
                (natp n)
                (natp a))
           (natp (fast-expt-loop-clock n)))
  :hints (("Goal" :in-theory (enable expt-loop-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp n)
                                           (natp a))
                                      (integerp (fast-expt-loop-clock n))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp n)
                                           (natp a))
                                      (<= 0 (fast-expt-loop-clock n))))))

(in-theory (disable fast-expt-loop-clock))

(defun fast-expt-clock (ret-pc n)
  (+ 20 (fast-expt-loop-clock n) (exit-clock 'expt ret-pc)))

(defthm fast-expt-clock-lemma
  (implies (and (natp x)
                (natp n)
                (natp a))
           (equal (expt-clock ret-pc x n a)
                  (fast-expt-clock ret-pc n)))
  :hints (("Goal" :in-theory (enable expt-clock))))

(defthm natp-fast-expt-clock-lemma
  (implies (and (natp x)
                (natp n)
                (natp a))
           (natp (fast-expt-clock ret-pc n)))
  :hints (("Goal" :in-theory (enable expt-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp x)
                                           (natp n)
                                           (natp a))
                                      (integerp (fast-expt-clock ret-pc n))))
                 (:linear
                  :corollary (implies (and (natp x)
                                           (natp n)
                                           (natp a))
                                      (<= 0 (fast-expt-clock ret-pc n))))))

(in-theory (disable fast-expt-clock))


(DEFUN fast-NST-IN-LOOP-CLOCK (CELL W)
  (+ 8
     (fast-expt-clock '(1 5) W)
     (fast-mod-clock '(5) cell (expt 2 W))))

(defthm fast-nst-in-loop-clock-lemma
  (implies (AND (NATP CELL)
                (NATP W))
           (equal (NST-IN-LOOP-CLOCK cell w)
                  (fast-NST-IN-LOOP-CLOCK cell w)))
  :hints (("Goal" :in-theory (enable NST-IN-LOOP-CLOCK))))

(defthm natp-fast-nst-in-loop-clock-lemma
  (implies (AND (NATP CELL)
                (NATP W))
           (natp (fast-NST-IN-LOOP-CLOCK cell w)))
  :hints (("Goal" :in-theory (enable NST-IN-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP CELL)
                                           (NATP W))
                                      (integerp (fast-NST-IN-LOOP-CLOCK cell w))))
                 (:linear
                  :corollary (implies (AND (NATP CELL)
                                           (NATP W))
                                      (<= 0 (fast-NST-IN-LOOP-CLOCK cell w))))))

(in-theory (disable fast-NST-IN-LOOP-CLOCK))


(DEFUN fast-NST-IN-CLOCK (RET-PC CELL W)
  (+ 15
     (fast-NST-IN-LOOP-CLOCK CELL W)
     (exit-clock 'NST-IN RET-PC)))

(defthm fast-NST-IN-CLOCK-lemma
  (implies (AND (NATP CELL)
                (NATP W))
           (equal (NST-IN-CLOCK RET-PC CELL W)
                  (fast-NST-IN-CLOCK RET-PC CELL W)))
  :hints (("Goal" :in-theory (enable NST-IN-CLOCK))))

(defthm natp-fast-NST-IN-CLOCK-lemma
  (implies (AND (NATP CELL)
                (NATP W))
           (natp (fast-NST-IN-CLOCK RET-PC CELL W)))
  :hints (("Goal" :in-theory (enable NST-IN-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP CELL)
                                           (NATP W))
                                      (integerp (fast-NST-IN-CLOCK RET-PC CELL W))))
                 (:linear
                  :corollary (implies (AND (NATP CELL)
                                           (NATP W))
                                      (<= 0 (fast-NST-IN-CLOCK RET-PC CELL W))))))

(in-theory (disable fast-NST-IN-CLOCK))

(DEFUN fast-NSYM-LOOP-CLOCK (CELL W)
  (+ 12
     (fast-expt-clock '(1 0 6) W)
     (fast-floor-CLOCK '(0 6) CELL (EXPT 2 W))
     (fast-MOD-CLOCK '(6) (FLOOR CELL (EXPT 2 W)) 2)))

(defthm NSYM-LOOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (equal (NSYM-LOOP-CLOCK CELL W)
                  (fast-NSYm-LOOP-CLOCK CELL W)))
  :hints (("Goal" :in-theory (enable nsym-LOOP-CLOCK))))

(defthm natp-NSYM-LOOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (natp (fast-NSYm-LOOP-CLOCK CELL W)))
  :hints (("Goal" :in-theory (enable nsym-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (integerp (fast-NSYm-LOOP-CLOCK CELL W))))
                 (:linear
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (<= 0 (fast-NSYm-LOOP-CLOCK CELL W))))))

(in-theory (disable fast-NSYM-LOOP-CLOCK))

(DEFUN FAST-NSYM-CLOCK (RET-PC CELL W)
  (+ 15
     (fast-NSYM-LOOP-CLOCK CELL W)
     (exit-clock 'NSYM RET-PC)))

(defthm fast-nsym-clock-lemma
  (implies (and (natp cell) (natp w))
           (equal (nsym-clock ret-pc cell w)
                  (fast-nsym-clock ret-pc cell w)))
  :hints (("Goal" :in-theory (enable nsym-clock))))

(defthm natp-fast-nsym-clock-lemma
  (implies (and (natp cell) (natp w))
           (natp (fast-nsym-clock ret-pc cell w)))
  :hints (("Goal" :in-theory (enable nsym-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp cell) (natp w))
                                      (integerp (fast-nsym-clock ret-pc cell w))))
                 (:linear
                  :corollary (implies (and (natp cell) (natp w))
                                      (<= 0 (fast-nsym-clock ret-pc cell w))))))

(in-theory (disable fast-nsym-clock))

(DEFUN FAST-NOP-LOOP-CLOCK (CELL W)
  (+ 14
     (fast-EXPT-CLOCK '(1 0 7) (+ 1 W))
     (fast-FLOOR-CLOCK '(0 7)
                      CELL (EXPT 2 (+ 1 W)))
     (fast-MOD-CLOCK '(7)
                    (FLOOR CELL (EXPT 2 (+ 1 W)))
                    8)))

(defthm FAST-NOP-LOOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (equal (NOP-LOOP-CLOCK CELL W)
                  (fast-NOP-LOOP-CLOCK CELL W)))
  :hints (("Goal" :in-theory (enable NOP-LOOP-CLOCK))))

(defthm natp-FAST-NOP-LOOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (natp (fast-NOP-LOOP-CLOCK CELL W)))
  :hints (("Goal" :in-theory (enable NOP-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (integerp (fast-NOP-LOOP-CLOCK CELL W))))
                 (:linear
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (<= 0 (fast-NOP-LOOP-CLOCK CELL W))))))

(in-theory (disable fast-NOP-LOOP-CLOCK))


(DEFUN FAST-NOP-CLOCK (RET-PC CELL W)
  (+ 15
     (fast-NOP-LOOP-CLOCK CELL W)
     (exit-clock 'NOP RET-PC)))

(defthm FAST-NOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (equal (NOP-CLOCK RET-PC CELL W)
                  (fast-NOP-CLOCK RET-PC CELL W)))
  :hints (("Goal" :in-theory (enable NOP-CLOCK))))

(defthm natp-FAST-NOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (natp (fast-NOP-CLOCK RET-PC CELL W)))
  :hints (("Goal" :in-theory (enable NOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (integerp (fast-NOP-CLOCK RET-PC CELL W))))
                 (:linear
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (<= 0 (fast-NOP-CLOCK RET-PC CELL W))))))

(in-theory (disable fast-NOP-CLOCK))

(DEFUN FAST-NST-OUT-LOOP-CLOCK (CELL W)
  (+ 18
     (fast-EXPT-CLOCK '(1 0 8) (+ 4 W))
     (fast-FLOOR-CLOCK '(0 8)
                      CELL (EXPT 2 (+ 4 W)))
     (fast-EXPT-CLOCK '(1 8) W)
     (fast-MOD-CLOCK '(8)
                    (FLOOR CELL (EXPT 2 (+ 4 W)))
                    (EXPT 2 W))))

(defthm FAST-NST-OUT-LOOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (equal (NST-OUT-LOOP-CLOCK CELL W)
                  (fast-NST-OUT-LOOP-CLOCK CELL W)))
  :hints (("Goal" :in-theory (enable NST-OUT-LOOP-CLOCK))))

(defthm natp-FAST-NST-OUT-LOOP-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (natp (fast-NST-OUT-LOOP-CLOCK CELL W)))
  :hints (("Goal" :in-theory (enable NST-OUT-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (integerp (fast-NST-OUT-LOOP-CLOCK CELL W))))
                 (:linear
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (<= 0 (fast-NST-OUT-LOOP-CLOCK CELL W))))))

(in-theory (disable fast-NST-OUT-LOOP-CLOCK))

(DEFUN FAST-NST-OUT-CLOCK (RET-PC CELL W)
  (+ 15
     (fast-NST-OUT-LOOP-CLOCK CELL W)
     (exit-clock 'NST-OUT RET-PC)))

(defthm FAST-NST-OUT-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (equal (NST-OUT-CLOCK RET-PC CELL W)
                  (fast-NST-OUT-CLOCK RET-PC CELL W)))
  :hints (("Goal" :in-theory (enable NST-OUT-CLOCK))))

(defthm natp-FAST-NST-OUT-CLOCK-lemma
  (implies (AND (NATP CELL) (NATP W))
           (natp (fast-NST-OUT-CLOCK RET-PC CELL W)))
  :hints (("Goal" :in-theory (enable NST-OUT-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (integerp (fast-NST-OUT-CLOCK RET-PC CELL W))))
                 (:linear
                  :corollary (implies (AND (NATP CELL) (NATP W))
                                      (<= 0 (fast-NST-OUT-CLOCK RET-PC CELL W))))))

(in-theory (disable fast-NST-OUT-CLOCK))

(DEFUN FAST-NCAR-LOOP-CLOCK (TM W)
  (+ 12
     (fast-EXPT-CLOCK '(1 9) (+ 4 (* 2 W)))
     (fast-MOD-CLOCK '(9) TM (EXPT 2 (+ 4 (* 2 W))))))

(defthm FAST-NCAR-LOOP-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (equal (NCAR-LOOP-CLOCK TM W)
                  (fast-NCAR-LOOP-CLOCK TM W)))
  :hints (("Goal" :in-theory (enable NCAR-LOOP-CLOCK))))

(defthm natp-FAST-NCAR-LOOP-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (natp (fast-NCAR-LOOP-CLOCK TM W)))
  :hints (("Goal" :in-theory (enable NCAR-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (integerp (fast-NCAR-LOOP-CLOCK TM W))))
                 (:linear
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (<= 0 (fast-NCAR-LOOP-CLOCK TM W))))))

(in-theory (disable fast-NCAR-LOOP-CLOCK))

(DEFUN FAST-NCAR-CLOCK (RET-PC TM W)
  (+ 15
     (fast-NCAR-LOOP-CLOCK TM W)
     (exit-clock 'NCAR RET-PC)))

(defthm FAST-NCAR-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (equal (NCAR-CLOCK RET-PC TM W)
                  (fast-NCAR-CLOCK RET-PC TM W)))
  :hints (("Goal" :in-theory (enable NCAR-CLOCK))))

(defthm natp-FAST-NCAR-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (natp (fast-NCAR-CLOCK RET-PC TM W)))
  :hints (("Goal" :in-theory (enable NCAR-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (integerp (fast-NCAR-CLOCK RET-PC TM W))))
                 (:linear
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (<= 0 (fast-NCAR-CLOCK RET-PC TM W))))))

(in-theory (disable fast-NCAR-CLOCK))

(DEFUN FAST-NCDR-LOOP-CLOCK (TM W)
  (+ 13
     (fast-EXPT-CLOCK '(1 10) (+ 4 (* 2 W)))
     (fast-FLOOR-CLOCK '(10)
                      TM (EXPT 2 (+ 4 (* 2 W))))))

(defthm FAST-NCDR-LOOP-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (equal (NCDR-LOOP-CLOCK TM W)
                  (fast-NCDR-LOOP-CLOCK TM W)))
  :hints (("Goal" :in-theory (enable NCDR-LOOP-CLOCK))))

(defthm natp-FAST-NCDR-LOOP-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (natp (fast-NCDR-LOOP-CLOCK TM W)))
  :hints (("Goal" :in-theory (enable NCDR-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (integerp (fast-NCDR-LOOP-CLOCK TM W))))
                 (:linear
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (<= 0 (fast-NCDR-LOOP-CLOCK TM W))))))

(in-theory (disable fast-NCDR-LOOP-CLOCK))

(DEFUN FAST-NCDR-CLOCK (RET-PC TM W)
  (+ 15
     (fast-NCDR-LOOP-CLOCK TM W)
     (exit-clock 'NCDR RET-PC)))

(defthm FAST-NCDR-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (equal (NCDR-CLOCK RET-PC TM W)
                  (fast-NCDR-CLOCK RET-PC TM W)))
  :hints (("Goal" :in-theory (enable NCDR-CLOCK))))

(defthm natp-FAST-NCDR-CLOCK-lemma
  (implies (AND (NATP TM) (NATP W))
           (natp (fast-NCDR-CLOCK RET-PC TM W)))
  :hints (("Goal" :in-theory (enable NCDR-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (integerp (fast-NCDR-CLOCK RET-PC TM W))))
                 (:linear
                  :corollary (implies (AND (NATP TM) (NATP W))
                                      (<= 0 (fast-NCDR-CLOCK RET-PC TM W))))))

(in-theory (disable fast-NCDR-CLOCK))


(DEFUN FAST-CURRENT-SYMN-LOOP-CLOCK (TAPE POS)
  (IF
    (EQUAL (- POS (LOG2 TAPE)) 0)
    (+ 8 (fast-LOG2-CLOCK '(1 0 11) TAPE))
    (+ 20
       (fast-LOG2-CLOCK '(1 0 11) TAPE)
       (fast-EXPT-CLOCK '(1 0 2 11) POS)
       (fast-FLOOR-CLOCK '(0 2 11)
                        TAPE (EXPT 2 POS))
       (fast-MOD-CLOCK '(2 11)
                      (FLOOR TAPE (EXPT 2 POS))
                      2))))

(defthm FAST-CURRENT-SYMN-LOOP-CLOCK-lemma
  (implies (AND (NATP TAPE) (NATP POS))
           (equal (CURRENT-SYMN-LOOP-CLOCK TAPE POS)
                  (FAST-CURRENT-SYMN-LOOP-CLOCK TAPE POS)))
  :hints (("Goal" :in-theory (enable CURRENT-SYMN-LOOP-CLOCK))))

(defthm natp-FAST-CURRENT-SYMN-LOOP-CLOCK-lemma
  (implies (AND (NATP TAPE) (NATP POS))
           (natp (FAST-CURRENT-SYMN-LOOP-CLOCK TAPE POS)))
  :hints (("Goal" :in-theory (enable CURRENT-SYMN-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP TAPE) (NATP POS))
                                      (integerp (FAST-CURRENT-SYMN-LOOP-CLOCK TAPE POS))))
                 (:linear
                  :corollary (implies (AND (NATP TAPE) (NATP POS))
                                      (<= 0 (FAST-CURRENT-SYMN-LOOP-CLOCK TAPE POS))))))

(in-theory (disable FAST-CURRENT-SYMN-LOOP-CLOCK))


(DEFUN FAST-CURRENT-SYMN-CLOCK (RET-PC TAPE POS)
  (+ 15
     (fast-CURRENT-SYMN-LOOP-CLOCK TAPE POS)
     (exit-clock 'CURRENT-SYMN RET-PC)))

(defthm FAST-CURRENT-SYMN-CLOCK-lemma
  (implies (AND (NATP TAPE) (NATP POS))
           (equal (CURRENT-SYMN-CLOCK RET-PC TAPE POS)
                  (FAST-CURRENT-SYMN-CLOCK RET-PC TAPE POS)))
  :hints (("Goal" :in-theory (enable CURRENT-SYMN-CLOCK))))

(defthm natp-FAST-CURRENT-SYMN-CLOCK-lemma
  (implies (AND (NATP TAPE) (NATP POS))
           (natp (FAST-CURRENT-SYMN-CLOCK RET-PC TAPE POS)))
  :hints (("Goal" :in-theory (enable CURRENT-SYMN-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP TAPE) (NATP POS))
                                      (integerp (FAST-CURRENT-SYMN-CLOCK RET-PC TAPE POS))))
                 (:linear
                  :corollary (implies (AND (NATP TAPE) (NATP POS))
                                      (<= 0 (FAST-CURRENT-SYMN-CLOCK RET-PC TAPE POS))))))

(in-theory (disable FAST-CURRENT-SYMN-CLOCK))


(DEFUN FAST-NINSTR1-LOOP-CLOCK (ST SYM TM W NNIL)
  (if (and (natp w) (natp tm))
      (IF
       (EQUAL TM 0)
       3
       (IF
        (EQUAL (- TM NNIL) 0)
        8
        (IF
         (EQUAL (IF (EQUAL (- ST (NST-IN (NCAR TM W) W))
                           0)
                    (- SYM (NSYM (NCAR TM W) W))
                    1)
                0)
         (IF
          (EQUAL (- ST (NST-IN (NCAR TM W) W))
                 0)
          (+
           11
           (+
            (fast-NCAR-CLOCK '(0 1 0 0 2 2 12) TM W)
            (+
             3
             (+
              (fast-NST-IN-CLOCK '(1 0 0 2 2 12)
                                (NCAR TM W)
                                W)
              (+
               7
               (+ (fast-NCAR-CLOCK '(0 1 1 0 2 2 12) TM W)
                  (+ 3
                     (+ (fast-NSYM-CLOCK '(1 1 0 2 2 12)
                                        (NCAR TM W)
                                        W)
                        (+ 6
                           (+ (fast-NCAR-CLOCK '(1 2 2 12) TM W)
                              2))))))))))
          (+ 11
             (+ (fast-NCAR-CLOCK '(0 1 0 0 2 2 12) TM W)
                (+ 3
                   (+ (fast-NST-IN-CLOCK '(1 0 0 2 2 12)
                                        (NCAR TM W)
                                        W)
                      (+ 9
                         (+ (fast-NCAR-CLOCK '(1 2 2 12) TM W)
                            2)))))))
         (IF
          (EQUAL (- ST (NST-IN (NCAR TM W) W))
                 0)
          (+
           11
           (+
            (fast-NCAR-CLOCK '(0 1 0 0 2 2 12) TM W)
            (+
             3
             (+
              (fast-NST-IN-CLOCK '(1 0 0 2 2 12)
                                (NCAR TM W)
                                W)
              (+
               7
               (+
                (fast-NCAR-CLOCK '(0 1 1 0 2 2 12) TM W)
                (+
                 3
                 (+
                  (fast-NSYM-CLOCK '(1 1 0 2 2 12)
                                  (NCAR TM W)
                                  W)
                  (+
                   8
                   (+ (fast-NCDR-CLOCK '(2 2 2 2 12) TM W)
                      (+ 8
                         (fast-NINSTR1-LOOP-CLOCK ST SYM (NCDR TM W)
                                                 W NNIL))))))))))))
          (+
           11
           (+
            (fast-NCAR-CLOCK '(0 1 0 0 2 2 12) TM W)
            (+
             3
             (+
              (fast-NST-IN-CLOCK '(1 0 0 2 2 12)
                                (NCAR TM W)
                                W)
              (+ 11
                 (+ (fast-NCDR-CLOCK '(2 2 2 2 12) TM W)
                    (+ 8
                       (fast-NINSTR1-LOOP-CLOCK ST SYM (NCDR TM W)
                                               W NNIL))))))))))))
      0))

(defthm FAST-NINSTR1-LOOP-CLOCK-lemma
  (implies (AND (NATP ST)
                (NATP SYM)
                (NATP TM)
                (NATP W)
                (EQUAL NNIL (NNIL W)))
           (equal (NINSTR1-LOOP-CLOCK ST SYM TM W NNIL)
                  (FAST-NINSTR1-LOOP-CLOCK ST SYM TM W NNIL)))
  :hints (("Goal" :in-theory (enable NINSTR1-LOOP-CLOCK))))

(defthm natp-FAST-NINSTR1-LOOP-CLOCK-lemma
  (implies (AND (NATP ST)
                (NATP SYM)
                (NATP TM)
                (NATP W)
                (EQUAL NNIL (NNIL W)))
           (natp (FAST-NINSTR1-LOOP-CLOCK ST SYM TM W NNIL)))
  :hints (("Goal" :in-theory (enable NINSTR1-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP ST)
                                           (NATP SYM)
                                           (NATP TM)
                                           (NATP W)
                                           (EQUAL NNIL (NNIL W)))
                                      (integerp (FAST-NINSTR1-LOOP-CLOCK ST SYM TM W NNIL))))
                 (:linear
                  :corollary (implies (AND (NATP ST)
                                           (NATP SYM)
                                           (NATP TM)
                                           (NATP W)
                                           (EQUAL NNIL (NNIL W)))
                                      (<= 0 (FAST-NINSTR1-LOOP-CLOCK ST SYM TM W NNIL))))))

(in-theory (disable FAST-NINSTR1-LOOP-CLOCK))


(DEFUN FAST-NINSTR1-CLOCK (RET-PC ST SYM TM W NNIL)
  (+ 22
      (+ (fast-NINSTR1-LOOP-CLOCK ST SYM TM W NNIL)
          (+ 8
              (exit-clock 'NINSTR1 RET-PC)))))

(defthm FAST-NINSTR1-CLOCK-lemma
  (implies (AND (NATP ST)
                (NATP SYM)
                (NATP TM)
                (NATP W)
                (EQUAL NNIL (NNIL W)))
           (equal (NINSTR1-CLOCK RET-PC ST SYM TM W NNIL)
                  (FAST-NINSTR1-CLOCK RET-PC ST SYM TM W NNIL)))
  :hints (("Goal" :in-theory (enable NINSTR1-CLOCK))))

(defthm natp-FAST-NINSTR1-CLOCK-lemma
  (implies (AND (NATP ST)
                (NATP SYM)
                (NATP TM)
                (NATP W)
                (EQUAL NNIL (NNIL W)))
           (natp (FAST-NINSTR1-CLOCK RET-PC ST SYM TM W NNIL)))
  :hints (("Goal" :in-theory (enable NINSTR1-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP ST)
                                           (NATP SYM)
                                           (NATP TM)
                                           (NATP W)
                                           (EQUAL NNIL (NNIL W)))
                                      (integerp (FAST-NINSTR1-CLOCK RET-PC ST SYM TM W NNIL))))
                 (:linear
                  :corollary (implies (AND (NATP ST)
                                           (NATP SYM)
                                           (NATP TM)
                                           (NATP W)
                                           (EQUAL NNIL (NNIL W)))
                                      (<= 0 (FAST-NINSTR1-CLOCK RET-PC ST SYM TM W NNIL))))))

(in-theory (disable FAST-NINSTR1-CLOCK))


(DEFUN FAST-NEW-TAPE2-LOOP-CLOCK (OP TAPE POS)
  (IF
   (EQUAL (IF (EQUAL OP 0)
              0 (IF (EQUAL (- OP 1) 0) 0 1))
          0)
   (IF
    (EQUAL OP 0)
    (IF
     (EQUAL (- POS (LOG2 TAPE)) 0)
     (IF (EQUAL OP 0)
         (+ 9
            (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
               (+ 10
                  (+ (fast-EXPT-CLOCK '(1 0 1 1 1 13) POS)
                     2))))
         (+ 9
            (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
               (+ 12
                  (+ (fast-EXPT-CLOCK '(1 0 2 1 1 13) (+ POS 1))
                     3)))))
     (IF
      (EQUAL (- (CURRENT-SYMN TAPE POS) OP)
             0)
      (+ 9
         (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
            (+ 6
               (+ (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                          TAPE POS)
                  6))))
      (IF
       (EQUAL (CURRENT-SYMN TAPE POS) 0)
       (+
        9
        (+
         (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
         (+
          6
          (+
           (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                   TAPE POS)
           (+
            7
            (+ (fast-CURRENT-SYMN-CLOCK '(0 2 2 1 13)
                                       TAPE POS)
               (+ 7
                  (+ (fast-EXPT-CLOCK '(1 0 1 2 2 1 13) POS)
                     4))))))))
       (+
        9
        (+
         (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
         (+
          6
          (+
           (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                   TAPE POS)
           (+
            7
            (+ (fast-CURRENT-SYMN-CLOCK '(0 2 2 1 13)
                                       TAPE POS)
               (+ 7
                  (+ (fast-EXPT-CLOCK '(1 0 2 2 2 1 13) POS)
                     5)))))))))))
    (IF
     (EQUAL (- OP 1) 0)
     (IF
      (EQUAL (- POS (LOG2 TAPE)) 0)
      (IF (EQUAL OP 0)
          (+ 14
             (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
                (+ 10
                   (+ (fast-EXPT-CLOCK '(1 0 1 1 1 13) POS)
                      2))))
          (+ 14
             (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
                (+ 12
                   (+ (fast-EXPT-CLOCK '(1 0 2 1 1 13) (+ POS 1))
                      3)))))
      (IF
       (EQUAL (- (CURRENT-SYMN TAPE POS) OP)
              0)
       (+ 14
          (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
             (+ 6
                (+ (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                           TAPE POS)
                   6))))
       (IF
        (EQUAL (CURRENT-SYMN TAPE POS) 0)
        (+
         14
         (+
          (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
          (+
           6
           (+
            (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                    TAPE POS)
            (+
             7
             (+
              (fast-CURRENT-SYMN-CLOCK '(0 2 2 1 13)
                                      TAPE POS)
              (+ 7
                 (+ (fast-EXPT-CLOCK '(1 0 1 2 2 1 13) POS)
                    4))))))))
        (+
         14
         (+
          (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
          (+
           6
           (+
            (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                    TAPE POS)
            (+
             7
             (+
              (fast-CURRENT-SYMN-CLOCK '(0 2 2 1 13)
                                      TAPE POS)
              (+ 7
                 (+ (fast-EXPT-CLOCK '(1 0 2 2 2 1 13) POS)
                    5)))))))))))
     (IF
      (EQUAL (- POS (LOG2 TAPE)) 0)
      (IF (EQUAL OP 0)
          (+ 15
             (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
                (+ 10
                   (+ (fast-EXPT-CLOCK '(1 0 1 1 1 13) POS)
                      2))))
          (+ 15
             (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
                (+ 12
                   (+ (fast-EXPT-CLOCK '(1 0 2 1 1 13) (+ POS 1))
                      3)))))
      (IF
       (EQUAL (- (CURRENT-SYMN TAPE POS) OP)
              0)
       (+ 15
          (+ (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
             (+ 6
                (+ (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                           TAPE POS)
                   6))))
       (IF
        (EQUAL (CURRENT-SYMN TAPE POS) 0)
        (+
         15
         (+
          (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
          (+
           6
           (+
            (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                    TAPE POS)
            (+
             7
             (+
              (fast-CURRENT-SYMN-CLOCK '(0 2 2 1 13)
                                      TAPE POS)
              (+ 7
                 (+ (fast-EXPT-CLOCK '(1 0 1 2 2 1 13) POS)
                    4))))))))
        (+
         15
         (+
          (fast-LOG2-CLOCK '(1 0 1 13) TAPE)
          (+
           6
           (+
            (fast-CURRENT-SYMN-CLOCK '(0 0 2 1 13)
                                    TAPE POS)
            (+
             7
             (+
              (fast-CURRENT-SYMN-CLOCK '(0 2 2 1 13)
                                      TAPE POS)
              (+ 7
                 (+ (fast-EXPT-CLOCK '(1 0 2 2 2 1 13) POS)
                    5)))))))))))))
   (IF
    (EQUAL OP 0)
    (IF
     (EQUAL (- OP 2) 0)
     (IF (EQUAL POS 0)
         15
         16)
     (IF
      (EQUAL (- POS (LOG2 TAPE)) 0)
      (+ 13
         (+ (fast-LOG2-CLOCK '(1 0 2 2 13) TAPE)
            (+ 8
               (+ (fast-EXPT-CLOCK '(1 0 0 1 2 2 13) POS)
                  (+ 8
                     (+ (fast-EXPT-CLOCK '(1 0 1 2 2 13) (+ 1 POS))
                        6))))))
      (+ 13
         (+ (fast-LOG2-CLOCK '(1 0 2 2 13) TAPE)
            9))))
    (IF
     (EQUAL (- OP 1) 0)
     (IF
      (EQUAL (- OP 2) 0)
      (IF (EQUAL POS 0)
          20
          21)
      (IF
       (EQUAL (- POS (LOG2 TAPE)) 0)
       (+ 18
          (+ (fast-LOG2-CLOCK '(1 0 2 2 13) TAPE)
             (+ 8
                (+ (fast-EXPT-CLOCK '(1 0 0 1 2 2 13) POS)
                   (+ 8
                      (+ (fast-EXPT-CLOCK '(1 0 1 2 2 13) (+ 1 POS))
                         6))))))
       (+ 18
          (+ (fast-LOG2-CLOCK '(1 0 2 2 13) TAPE)
             9))))
     (IF
      (EQUAL (- OP 2) 0)
      (IF (EQUAL POS 0)
          21
          22)
      (IF
       (EQUAL (- POS (LOG2 TAPE)) 0)
       (+ 19
          (+ (fast-LOG2-CLOCK '(1 0 2 2 13) TAPE)
             (+ 8
                (+ (fast-EXPT-CLOCK '(1 0 0 1 2 2 13) POS)
                   (+ 8
                      (+ (fast-EXPT-CLOCK '(1 0 1 2 2 13) (+ 1 POS))
                         6))))))
       (+ 19
          (+ (fast-LOG2-CLOCK '(1 0 2 2 13) TAPE)
             9))))))))

(defthm FAST-NEW-TAPE2-LOOP-CLOCK-lemma
  (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
           (equal (NEW-TAPE2-LOOP-CLOCK OP TAPE POS)
                  (FAST-NEW-TAPE2-LOOP-CLOCK OP TAPE POS)))
  :hints (("Goal" :in-theory (enable NEW-TAPE2-LOOP-CLOCK))))

(defthm natp-FAST-NEW-TAPE2-LOOP-CLOCK-lemma
  (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
           (natp (FAST-NEW-TAPE2-LOOP-CLOCK OP TAPE POS)))
  :hints (("Goal" :in-theory (enable NEW-TAPE2-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
                                      (integerp (FAST-NEW-TAPE2-LOOP-CLOCK OP TAPE POS))))
                 (:linear
                  :corollary (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
                                      (<= 0 (FAST-NEW-TAPE2-LOOP-CLOCK OP TAPE POS))))))

(in-theory (disable FAST-NEW-TAPE2-LOOP-CLOCK))


(DEFUN FAST-NEW-TAPE2-CLOCK (RET-PC OP TAPE POS)
  (+ 14
      (+ (fast-NEW-TAPE2-LOOP-CLOCK OP TAPE POS)
          (+ 8
              (exit-clock 'NEW-TAPE2 RET-PC)))))

(defthm FAST-NEW-TAPE2-CLOCK-lemma
  (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
           (equal (NEW-TAPE2-CLOCK RET-PC OP TAPE POS)
                  (FAST-NEW-TAPE2-CLOCK RET-PC OP TAPE POS)))
  :hints (("Goal" :in-theory (enable NEW-TAPE2-CLOCK))))

(defthm natp-FAST-NEW-TAPE2-CLOCK-lemma
  (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
           (natp (FAST-NEW-TAPE2-CLOCK RET-PC OP TAPE POS)))
  :hints (("Goal" :in-theory (enable NEW-TAPE2-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
                                      (integerp (FAST-NEW-TAPE2-CLOCK RET-PC OP TAPE POS))))
                 (:linear
                  :corollary (implies (AND (NATP OP) (NATP TAPE) (NATP POS))
                                      (<= 0 (FAST-NEW-TAPE2-CLOCK RET-PC OP TAPE POS))))))

(in-theory (disable FAST-NEW-TAPE2-CLOCK))

(DEFUN FAST-TMI3-LOOP-CLOCK (ST TAPE POS TM W NNIL N)
  (DECLARE (XARGS :MEASURE (ACL2-COUNT N)))
  (IF
   (ZP N)
   0
   (IF
    (AND (NATP ST)
         (NATP TAPE)
         (NATP POS)
         (NATP TM)
         (NATP W)
         (EQUAL NNIL (NNIL W))
         (< ST (EXPT 2 W)))
    (IF
     (EQUAL (- (NINSTR1 ST (CURRENT-SYMN TAPE POS)
                        TM W NNIL)
               -1)
            0)
     (+ 5
        (+ (fast-CURRENT-SYMN-CLOCK '(1 0 0 14)
                                   TAPE POS)
           (+ 5
              (+ (fast-NINSTR1-CLOCK '(0 0 14)
                                    ST (CURRENT-SYMN TAPE POS)
                                    TM W NNIL)
                 7))))
     (+
      5
      (+
       (fast-CURRENT-SYMN-CLOCK '(1 0 0 14)
                               TAPE POS)
       (+
        5
        (+
         (fast-NINSTR1-CLOCK '(0 0 14)
                            ST (CURRENT-SYMN TAPE POS)
                            TM W NNIL)
         (+
          8
          (+
           (fast-CURRENT-SYMN-CLOCK '(1 0 0 2 14)
                                   TAPE POS)
           (+
            5
            (+
             (fast-NINSTR1-CLOCK '(0 0 2 14)
                                ST (CURRENT-SYMN TAPE POS)
                                TM W NNIL)
             (+
              3
              (+
               (fast-NST-OUT-CLOCK
                '(0 2 14)
                (NINSTR1 ST (CURRENT-SYMN TAPE POS)
                         TM W NNIL)
                W)
               (+
                5
                (+
                 (fast-CURRENT-SYMN-CLOCK '(1 0 0 1 2 14)
                                         TAPE POS)
                 (+
                  5
                  (+
                   (fast-NINSTR1-CLOCK '(0 0 1 2 14)
                                      ST (CURRENT-SYMN TAPE POS)
                                      TM W NNIL)
                   (+
                    3
                    (+
                     (fast-NOP-CLOCK
                      '(0 1 2 14)
                      (NINSTR1 ST (CURRENT-SYMN TAPE POS)
                               TM W NNIL)
                      W)
                     (+
                      4
                      (+
                       (fast-NEW-TAPE2-CLOCK
                        '(1 2 14)
                        (NOP
                         (NINSTR1 ST (CURRENT-SYMN TAPE POS)
                                  TM W NNIL)
                         W)
                        TAPE POS)
                       (+
                        10
                        (fast-TMI3-LOOP-CLOCK
                         (NST-OUT
                          (NINSTR1 ST (CURRENT-SYMN TAPE POS)
                                   TM W NNIL)
                          W)
                         (MV-NTH
                          0
                          (MV-LIST
                           2
                           (NEW-TAPE2
                            (NOP
                             (NINSTR1
                              ST (CURRENT-SYMN TAPE POS)
                              TM W NNIL)
                             W)
                            TAPE POS)))
                         (MV-NTH
                          1
                          (MV-LIST
                           2
                           (NEW-TAPE2
                            (NOP
                             (NINSTR1
                              ST (CURRENT-SYMN TAPE POS)
                              TM W NNIL)
                             W)
                            TAPE POS)))
                         TM W NNIL (- N 1))))))))))))))))))))))
    0)))

(defthm FAST-TMI3-LOOP-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (equal (TMI3-LOOP-CLOCK ST TAPE POS TM W NNIL N)
                  (FAST-TMI3-LOOP-CLOCK ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (e/d (TMI3-LOOP-CLOCK)
                                  (TMI3-LOOP-CLOCK-IS-K*)))))

(defthm natp-FAST-TMI3-LOOP-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (natp (FAST-TMI3-LOOP-CLOCK ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (e/d (TMI3-LOOP-CLOCK)
                                  (TMI3-LOOP-CLOCK-IS-K*))))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (integerp (FAST-TMI3-LOOP-CLOCK ST TAPE POS TM W NNIL N))))
                 (:linear
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (<= 0 (FAST-TMI3-LOOP-CLOCK ST TAPE POS TM W NNIL N))))))

(in-theory (disable FAST-TMI3-LOOP-CLOCK))


(DEFUN FAST-TMI3-CLOCK (RET-PC ST TAPE POS TM W NNIL N)
  (IF
   (EQUAL (MV-NTH 0
                  (MV-LIST 4 (TMI3 ST TAPE POS TM W N)))
          0)
   (+ 26
      (fast-TMI3-LOOP-CLOCK ST TAPE POS TM W NNIL N))
   (+ 26
      (+ (fast-TMI3-LOOP-CLOCK ST TAPE POS TM W NNIL N)
         (+ 15
            (exit-clock 'TMI3 RET-PC))))))

(defthm FAST-TMI3-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (equal (TMI3-CLOCK RET-PC ST TAPE POS TM W NNIL N)
                  (FAST-TMI3-CLOCK RET-PC ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (enable TMI3-CLOCK))))

(defthm natp-FAST-TMI3-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (natp (FAST-TMI3-CLOCK RET-PC ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (enable TMI3-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (integerp (FAST-TMI3-CLOCK RET-PC ST TAPE POS TM W NNIL N))))
                 (:linear
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (<= 0 (FAST-TMI3-CLOCK RET-PC ST TAPE POS TM W NNIL N))))))

(in-theory (disable FAST-TMI3-CLOCK))


(DEFUN FAST-MAIN-LOOP-CLOCK (ST TAPE POS TM W NNIL N)
  (+ 8
     (fast-TMI3-CLOCK '(15)
                     ST TAPE POS TM W NNIL N)))

(defthm FAST-MAIN-LOOP-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (equal (MAIN-LOOP-CLOCK ST TAPE POS TM W NNIL N)
                  (FAST-MAIN-LOOP-CLOCK ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (enable MAIN-LOOP-CLOCK))))

(defthm natp-FAST-MAIN-LOOP-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (natp (FAST-MAIN-LOOP-CLOCK ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (enable MAIN-LOOP-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (integerp (FAST-MAIN-LOOP-CLOCK ST TAPE POS TM W NNIL N))))
                 (:linear
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (<= 0 (FAST-MAIN-LOOP-CLOCK ST TAPE POS TM W NNIL N))))))

(in-theory (disable FAST-MAIN-LOOP-CLOCK))


(DEFUN FAST-MAIN-CLOCK (RET-PC ST TAPE POS TM W NNIL N)
  (IF
   (EQUAL (MV-NTH 0
                  (MV-LIST 4 (TMI3 ST TAPE POS TM W N)))
          0)
   (+ 26
      (fast-MAIN-LOOP-CLOCK ST TAPE POS TM W NNIL N))
   (+ 26
      (+ (fast-MAIN-LOOP-CLOCK ST TAPE POS TM W NNIL N)
         (+ 15
            (exit-clock 'MAIN RET-PC))))))

(defthm FAST-MAIN-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (equal (MAIN-CLOCK RET-PC ST TAPE POS TM W NNIL N)
                  (FAST-MAIN-CLOCK RET-PC ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (enable MAIN-CLOCK))))

(defthm natp-FAST-MAIN-CLOCK-lemma
  (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
           (natp (FAST-MAIN-CLOCK RET-PC ST TAPE POS TM W NNIL N)))
  :hints (("Goal" :in-theory (enable MAIN-CLOCK)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (integerp (FAST-MAIN-CLOCK RET-PC ST TAPE POS TM W NNIL N))))
                 (:linear
                  :corollary (implies (AND (NATP ST) (NATP TAPE) (NATP POS) (NATP TM) (NATP W) (EQUAL NNIL (NNIL W)) (< ST (EXPT 2 W)))
                                      (<= 0 (FAST-MAIN-CLOCK RET-PC ST TAPE POS TM W NNIL N))))))

(in-theory (disable FAST-MAIN-CLOCK))

(defun fast-psi-clock (st tape pos tm w nnil n)
  (+ 2 (fast-main-clock nil st tape pos tm w nnil n)))

(defthm fast-psi-clock-thm
  (implies (and (natp st)
                (natp tape)
                (natp pos)
                (natp tm)
                (natp w)
                (equal nnil (nnil w))
                (< st (expt 2 w)))
           (equal (psi-clock st tape pos tm w nnil n)
                  (fast-psi-clock st tape pos tm w nnil n)))
  :hints (("Goal" :in-theory (enable psi-clock))))

(defthm natp-fast-psi-clock-thm
  (implies (and (natp st)
                (natp tape)
                (natp pos)
                (natp tm)
                (natp w)
                (equal nnil (nnil w))
                (< st (expt 2 w)))
           (natp (fast-psi-clock st tape pos tm w nnil n)))
  :hints (("Goal" :in-theory (enable psi-clock)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (natp st)
                                           (natp tape)
                                           (natp pos)
                                           (natp tm)
                                           (natp w)
                                           (equal nnil (nnil w))
                                           (< st (expt 2 w)))
                                      (integerp (fast-psi-clock st tape pos tm w nnil n))))
                 (:linear
                  :corollary (implies (and (natp st)
                                           (natp tape)
                                           (natp pos)
                                           (natp tm)
                                           (natp w)
                                           (equal nnil (nnil w))
                                           (< st (expt 2 w)))
                                      (<= 0 (fast-psi-clock st tape pos tm w nnil n))))))

(defun find-k! (ST TAPE TM N)
  (LET*
    ((MAP (RENAMING-MAP ST TM))
     (ST-PRIME (CDR (ASSOC ST MAP)))
     (TAPE-PRIME
      (MV-NTH 0
              (MV-LIST 2 (CONVERT-TAPE-TO-TAPEN-POS TAPE))))
     (POS-PRIME
      (MV-NTH 1
              (MV-LIST 2 (CONVERT-TAPE-TO-TAPEN-POS TAPE))))
     (W (MAX-WIDTH TM MAP))
     (TM-PRIME (NCODE (TM-TO-TM1 TM MAP) W)))
    (FAST-PSI-CLOCK ST-PRIME
                  TAPE-PRIME POS-PRIME TM-PRIME W (NNIL W)
                  N)))

(defthm find-k-is-find-k!
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm)
                (natp n))
           (equal (find-k st tape tm n)
                  (find-k! st tape tm n)))
  :hints (("Goal" :in-theory (enable find-k))))

(in-theory (disable (:executable-counterpart find-k)))

(defthm natp-find-k!
  (implies (and (symbolp st)
                (tapep tape)
                (turing-machinep tm)
                (natp n))
           (natp (find-k! st tape tm n)))
  :hints (("Goal" :in-theory (enable find-k)))
  :rule-classes (:type-prescription
                 (:rewrite
                  :corollary (implies (and (symbolp st)
                                           (tapep tape)
                                           (turing-machinep tm)
                                           (natp n))
                                      (integerp (find-k! st tape tm n))))
                 (:linear
                  :corollary (implies (and (symbolp st)
                                           (tapep tape)
                                           (turing-machinep tm)
                                           (natp n))
                                      (<= 0 (find-k! st tape tm n))))))

(defthm m1-simulation-of-rogers-tm-takes-a-long-time
  (let ((k (find-k 'Q0 *example-tape* *rogers-tm* 78)))
    (and
     (equal k
            291202253588734484219274297505568945357129888612375663883)
     (< (expt 10 56) k)
     (< k (expt 10 57))))
  :rule-classes nil)



