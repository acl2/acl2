; Expressing a sum as a ripple-carry adder
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "bitxor")
(include-book "bitor")
(include-book "bitand")
(include-book "bvcat2")
(include-book "unsigned-byte-p")
(include-book "bvplus")
(include-book "rules") ; for GETBIT-OF-PLUS
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt2" :dir :system))
(local (include-book "kestrel/utilities/equal-of-booleans" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/plus-and-minus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/minus" :dir :system))
;; (local (include-book "kestrel/arithmetic-light/times" :dir :system))
;(local (include-book "arith")) ;for PLUS-OF-EXPT-AND-MINUS-OF-EXPT-ONE-LESS

(local (in-theory (disable DEFAULT-+-2 DEFAULT-*-2
                           )))

(defun full-adder-sum (bit1 bit2 carryin)
  (bitxor bit1 (bitxor bit2 carryin)))

(defun full-adder-carry (bit1 bit2 carryin)
  (bitor (bitand bit1 bit2)
         (bitand carryin (bitxor bit1 bit2))))

;returns n+1 bits, one bit of carry followed by n bits of sum
(defund ripple-carry-adder (n
                           x y        ;these are n-bit values
                           carry-in   ;a single bit
                           )
  (if (zp n)
      carry-in ;(used to add the 1 when subtracting since A-B=A+inv(b)+1)
    (let* ((shorter-sum (ripple-carry-adder (+ -1 n) (bvchop (+ -1 n) x) (bvchop (+ -1 n) y) carry-in))
           (carryin (getbit (+ -1 n) shorter-sum)))
      (bvcat2 1 (full-adder-carry (getbit (+ -1 n) x)
                                  (getbit (+ -1 n) y)
                                  carryin)
              1 (full-adder-sum (getbit (+ -1 n) x)
                                (getbit (+ -1 n) y)
                                carryin)
              (+ -1 n) (bvchop (+ -1 n) shorter-sum)))))

(defthm ripple-carry-adder-of-zeros
  (equal (ripple-carry-adder n 0 0 0)
         0)
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))

(defthm ripple-carry-adder-base
  (equal (ripple-carry-adder 0 x y carry-in)
         carry-in)
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))

(defthm ripple-carry-adder-recursive
  (implies (not (zp n))
           (equal (ripple-carry-adder n x y carry-in)
                  (let* ((shorter-sum (ripple-carry-adder (+ -1 n) (bvchop (+ -1 n) x) (bvchop (+ -1 n) y) carry-in))
                         (carryin (getbit (+ -1 n) shorter-sum))
                         (sumin (bvchop (+ -1 n) shorter-sum)))
                    (bvcat2 1 (full-adder-carry (getbit (+ -1 n) x)
                                                (getbit (+ -1 n) y)
                                                carryin)
                            1 (full-adder-sum (getbit (+ -1 n) x)
                                              (getbit (+ -1 n) y)
                                              carryin)
                            (+ -1 n) sumin))))
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))

;(local (include-book "kestrel/bv/arith" :dir :system))



(defthm equal-of-sum-of-low-bits
  (implies (and (unsigned-byte-p n y)
                (posp n)
                (integerp a))
           (equal (equal y (+ a (bvchop (+ -1 n) y)))
                  (equal (* (expt 2 (+ -1 n)) (getbit (+ -1 n) y))
                         a)))
  :hints (("Goal" :in-theory (enable bvcat logapp)
           :use (:instance split-bv (y y)
                           (m (+ -1 n))))))

(defthm equal-of-sum-of-low-bits-alt
  (implies (and (unsigned-byte-p n y)
                (posp n)
                (integerp a)
                (integerp b))
           (equal (equal y (+ a b (bvchop (+ -1 n) y)))
                  (equal (* (expt 2 (+ -1 n)) (getbit (+ -1 n) y))
                         (+ a b))))
  :hints (("Goal" :use (:instance equal-of-sum-of-low-bits (a (+ a b)))
           :in-theory (disable equal-of-sum-of-low-bits))))

(defthm equal-of-sum-of-low-bits-alt2
  (implies (and (unsigned-byte-p n y)
                (posp n)
                (integerp x)
                (integerp a)
                (integerp b))
           (equal (equal (+ x y) (+ a (bvchop (+ -1 n) y) b))
                  (equal (+ x (* (expt 2 (+ -1 n)) (getbit (+ -1 n) y)))
                         (+ a b))))
  :hints (("Goal" :in-theory (enable bvcat logapp)
           :use (:instance split-bv (y y)
                           (m (+ -1 n))))))

(defthm equal-of-sum-of-low-bits-alt2b
  (implies (and (unsigned-byte-p n y)
                (posp n)
                (integerp x)
                (integerp a)
                (integerp b))
           (equal (equal (+ x y) (+ a b (bvchop (+ -1 n) y)))
                  (equal (+ x (* (expt 2 (+ -1 n)) (getbit (+ -1 n) y)))
                         (+ a b))))
  :hints (("Goal" :in-theory (enable bvcat logapp)
           :use (:instance split-bv (y y)
                           (m (+ -1 n))))))

(defthm expt-of-one-less-combine
  (implies (posp n)
           (EQUAL (+ (EXPT 2 (+ -1 N)) (EXPT 2 (+ -1 N)))
                  (EXPT 2 N)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm equal-of-sum-of-low-bits-alt3
  (implies (and (unsigned-byte-p n y)
                (posp n)
                (integerp x)
                (integerp a)
                (integerp b))
           (equal (equal (+ y x) (+ a (bvchop (+ -1 n) y)))
                  (equal (+ x (* (expt 2 (+ -1 n)) (getbit (+ -1 n) y)))
                         (+ a))))
  :hints (("Goal" :in-theory (enable bvcat logapp)
           :use (:instance split-bv (y y)
                           (m (+ -1 n))))))

(defthm unsigned-byte-p-of-RIPPLE-CARRY-ADDER
  (implies (and (natp n)
                (unsigned-byte-p 1 carry-in))
           (unsigned-byte-p (+ 1 n) (RIPPLE-CARRY-ADDER N X Y CARRY-IN)))
  :hints (("Goal" :in-theory (enable RIPPLE-CARRY-ADDER))))

(defthm bound-lemma-for-adder
  (implies (and (UNSIGNED-BYTE-P (+ -1 N) X)
                (UNSIGNED-BYTE-P (+ -1 N) Y)
                (Natp n))
           (< (+ X Y) (EXPT 2 N)))
  :hints (("Goal" :in-theory (enable UNSIGNED-BYTE-P expt))))

(defthmd expt-split
  (implies (and (syntaxp (atom n))
                (natp n))
           (equal (expt 2 N)
                  (+ (expt 2 (+ -1 n)) (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (enable expt))))

(theory-invariant (incompatible (:rewrite expt-split) (:rewrite EXPT-OF-ONE-LESS-COMBINE)))

(defthm bound-lemma-strong
  (implies (and (UNSIGNED-BYTE-P (+ -1 N) X)
                (UNSIGNED-BYTE-P (+ -1 N) Y)
                (Natp n))
           (< (+ X Y)  (+ -1 (EXPT 2 N))))
  :hints (("Goal" :in-theory (e/d (UNSIGNED-BYTE-P expt-split) (EXPT-OF-ONE-LESS-COMBINE)))))

(defthm <-of-expt-cancel-hack
  (implies (posp n)
           (equal (< (+ X (EXPT 2 (+ -1 N)) y) (EXPT 2 N))
                  (< (+ x y) (EXPT 2 (+ -1 N)))))
  :hints (("Goal" :in-theory (e/d (expt) (expt-hack)))))

(local (in-theory (disable RIPPLE-CARRY-ADDER-RECURSIVE)))

(defthm bound-lemma-another
  (implies (posp n)
           (< (+ 1 (BVCHOP (+ -1 N) X)
                 (BVCHOP (+ -1 N) Y))
              (EXPT 2 N)))
  :hints (("Goal" :in-theory (disable bound-lemma-strong)
           :use (:instance bound-lemma-strong (x (BVCHOP (+ -1 N) X))
                           (y (BVCHOP (+ -1 N) Y))))))

(defthm not-equal-of-expt-and-RIPPLE-CARRY-ADDER
  (implies (posp n)
           (not (EQUAL (EXPT 2 N) (RIPPLE-CARRY-ADDER (+ -1 N) X Y 1))))
  :hints (("Goal" :use (:instance unsigned-byte-p-of-RIPPLE-CARRY-ADDER (n (- n 1)) (carry-in 1))
           :in-theory (disable unsigned-byte-p-of-RIPPLE-CARRY-ADDER))))

(defthm <-expt-cancel-1
  (implies (natp n)
           (equal (< (+ a X (EXPT 2 (+ -1 N)) y) (EXPT 2 N))
                  (< (+ a x y) (EXPT 2 (+ -1 N)))))
  :hints (("Goal" :in-theory (enable expt))))

(defthm arith-cancel-a
  (equal (< (+ a b c x e) x)
         (< (+ a b c e) 0)))

(defthm arith-cancel-b
  (equal (< (+ a b c d x) x)
         (< (+ a b c d) 0)))

(defthmd expt-split-linear
  (implies (integerp n)
           (equal (expt 2 n) (+ (expt 2 (+ -1 n)) (expt 2 (+ -1 n)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable expt))))

(defthm <-of-expt-cancellation
  (implies (integerp n)
           (equal (< (+ (EXPT 2 (+ -1 N)) y) (EXPT 2 N))
                  (< y (EXPT 2 (+ -1 N)))))
  :hints (("Goal" :in-theory (enable expt))))

(defthm split-bv-linear-when-top-bit-1
  (implies (and (equal (getbit (+ -1 n) x) 1)
                (posp n)
                (unsigned-byte-p n x))
           (equal x (+ (expt 2 (+ -1 n)) (bvchop (+ -1 n) x))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable bvcat logapp)
           :use (:instance split-bv (y x)
                           (m (+ -1 n))))))


(defthm helper-helper
  (IMPLIES (AND (EQUAL 1 (GETBIT (+ -1 N) Y))
                (UNSIGNED-BYTE-P (+ -1 N) X)
                (UNSIGNED-BYTE-P N Y)
                (EQUAL (+ X (BVCHOP (+ -1 N) Y))
                       (+ -1 (EXPT 2 (+ -1 N))))
                (<= 2 N))
           (EQUAL (+ 1 X Y) (EXPT 2 N)))
  :hints (("Goal" :in-theory (e/d (expt-hack) (EQUAL-OF-SUM-OF-LOW-BITS)) :use (:instance split-bv-linear-when-top-bit-1 (x y)))))

(defthm helper-helper2
  (IMPLIES (AND (EQUAL 1 (GETBIT (+ -1 N) X))
                (EQUAL (EXPT 2 (+ -1 N))
                       (RIPPLE-CARRY-ADDER (+ -1 N)
                                           (BVCHOP (+ -1 N) X)
                                           Y 1))
                (UNSIGNED-BYTE-P N X)
                (UNSIGNED-BYTE-P (+ -1 N) Y)
                (EQUAL (+ Y (BVCHOP (+ -1 N) X))
                       (+ -1 (EXPT 2 (+ -1 N))))
                (<= 2 N))
           (EQUAL (+ 1 X Y) (EXPT 2 N)))
  :hints (("Goal" :in-theory (e/d (expt-hack) (EQUAL-OF-SUM-OF-LOW-BITS)) :use (:instance split-bv-linear-when-top-bit-1 (x x)))))

(defthmd bvplus-becomes-ripple-carry-adder-helper
   (implies (and (natp n)
                 (unsigned-byte-p n x)
                 (unsigned-byte-p n y)
                 (unsigned-byte-p 1 carry))
            (equal (+ carry x y) ;(bvplus (+ 1 n) carry (bvplus (+ 1 n) x y))
                   (ripple-carry-adder n x y carry)))
   :otf-flg t
   :hints (("subgoal *1/2"
            :expand ((RIPPLE-CARRY-ADDER N X Y 0)
                     (RIPPLE-CARRY-ADDER N X Y 1)
                     (RIPPLE-CARRY-ADDER N X Y CARRY))
;            :use (:instance split-bv-linear-when-top-bit-1 (x y))
            :cases ((and (equal 0 carry) (equal 0 (GETBIT (+ -1 N) x)) (equal 0 (GETBIT (+ -1 N) y)))
                    (and (equal 0 carry) (equal 0 (GETBIT (+ -1 N) x)) (equal 1 (GETBIT (+ -1 N) y)))
                    (and (equal 0 carry) (equal 1 (GETBIT (+ -1 N) x)) (equal 0 (GETBIT (+ -1 N) y)))
                    (and (equal 0 carry) (equal 1 (GETBIT (+ -1 N) x)) (equal 1 (GETBIT (+ -1 N) y)))
                    (and (equal 1 carry) (equal 0 (GETBIT (+ -1 N) x)) (equal 0 (GETBIT (+ -1 N) y)))
                    (and (equal 1 carry) (equal 0 (GETBIT (+ -1 N) x)) (equal 1 (GETBIT (+ -1 N) y)))
                    (and (equal 1 carry) (equal 1 (GETBIT (+ -1 N) x)) (equal 0 (GETBIT (+ -1 N) y)))
                    (and (equal 1 carry) (equal 1 (GETBIT (+ -1 N) x)) (equal 1 (GETBIT (+ -1 N) y))))
;            :use ( ;(:instance getbit-of-plus (size n) (y (+ carry y)))
;(:instance getbit-of-plus (size n) (x carry))
;                  (:instance getbit-of-+-bvchop-expand2 (n (+ -1 n)) (y (+ 1(BVCHOP (+ -1 N) Y))))
;                 (:instance getbit-of-+-bvchop-expand2 (n (+ -1 n)))
;                  (:instance split-bv (y x) (n n) (m (+ -1 n)))
 ;                 (:instance split-bv (y y) (n n) (m (+ -1 n)))
;                  )
            :in-theory (e/d (helper-helper
                             ;bvchop-recollapse
                             GETBIT-OF-PLUS
                             BVCHOP-OF-SUM-CASES
                             ;;getbit-of-plus
;                             getbit-of-+-bvchop-expand2
 ;                            getbit-of-+-bvchop-expand3
  ;                           getbit-of-+-bvchop-expand4
                             bvcat logapp
                             bvplus
                             expt-hack)
                            (;EQUAL-OF-SUM-OF-LOW-BITS
;full-adder-sum
                             ;full-adder-carry
                             ;anti-bvplus
                             ;;BVCAT-OF-+-LOW
                             BVCAT-EQUAL-REWRITE-ALT BVCAT-EQUAL-REWRITE
                                         BVCAT-TIGHTEN-UPPER-SIZE
                                         ;BVCAT-OF-*-LOW
                                         ;BVCAT-OF-*-high
                                         ;GETBIT-OF-+-BVCHOP-EXPAND4
                                         ;GETBIT-OF-+-BVCHOP-EXPAND3
                                         ;GETBIT-0-OF-PLUS
                                         BVPLUS-1-BECOMES-BITXOR
                                         ;BVCHOP-1-OF-PLUS
                                         ;BVCAT-OF-+-HIGH
                                         )))
           ;; ("subgoal *1/2" :cases ((and (equal 0 (GETBIT 0 CARRY)) (equal 0 (GETBIT 0 X))(equal 0 (GETBIT 0 y)))
           ;;                                    (and (equal 0 (GETBIT 0 CARRY))(equal 0 (GETBIT 0 X))(equal 1 (GETBIT 0 y)))
           ;;                                    (and (equal 0 (GETBIT 0 CARRY))(equal 1 (GETBIT 0 X))(equal 0 (GETBIT 0 y)))
           ;;                                    (and (equal 0 (GETBIT 0 CARRY))(equal 1 (GETBIT 0 X))(equal 1 (GETBIT 0 y)))
           ;;                                    (and (equal 1 (GETBIT 0 CARRY))(equal 0 (GETBIT 0 X))(equal 0 (GETBIT 0 y)))
           ;;                                    (and (equal 1 (GETBIT 0 CARRY))(equal 0 (GETBIT 0 X))(equal 1 (GETBIT 0 y)))
           ;;                                    (and (equal 1 (GETBIT 0 CARRY))(equal 1 (GETBIT 0 X))(equal 0 (GETBIT 0 y)))
           ;;                                    (and (equal 1 (GETBIT 0 CARRY))(equal 1 (GETBIT 0 X))(equal 1 (GETBIT 0 y)))))
           ("Goal" :induct (RIPPLE-CARRY-ADDER N X Y CARRY)
            :in-theory (e/d (;ripple-carry-adder
                             (:induction ripple-carry-adder)
                             bvplus ;getbit-of-plus
                                                GETBIT-WHEN-VAL-IS-NOT-AN-INTEGER
                                                )
                            ((:definition ripple-carry-adder)
                             ;;anti-bvplus
                             ;BVCAT-OF-+-LOW ;looped
                             ;;<-OF-BVCHOP-HACK ;looped
                             ;; GETBIT-OF-+-BVCHOP-EXPAND4
                             ;; GETBIT-OF-+-BVCHOP-EXPAND3
                             ;GETBIT-0-OF-PLUS
                             BVPLUS-1-BECOMES-BITXOR
                             ;BVCHOP-1-OF-PLUS
                             ;BVCAT-OF-+-HIGH
                             ))
            :do-not '(generalize eliminate-destructors fertilize))))

(defthm ripple-carry-adder-of-bvchop-arg2
  (equal (ripple-carry-adder n (bvchop n x) y carry)
         (ripple-carry-adder n x y carry))
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))

(defthm ripple-carry-adder-of-bvchop-arg3
  (equal (ripple-carry-adder n x (bvchop n y) carry)
         (ripple-carry-adder n x y carry))
  :hints (("Goal" :in-theory (enable ripple-carry-adder))))

;; Can be used for bit-blasting
(defthmd bvplus-becomes-ripple-carry-adder
  (implies (and (natp n)
                (< 0 n))
            (equal (bvplus n x y)
                   (bvchop n (ripple-carry-adder n x y 0))))
   :hints (("Goal" :in-theory (e/d (bvplus) ())
            :use (:instance bvplus-becomes-ripple-carry-adder-helper (carry 0) (x (bvchop n x)) (y (bvchop n y)))
            :do-not '(generalize eliminate-destructors))))



;is this even used?
;; (defthmd bvminus-becomes-ripple-carry-adder
;;   (implies (and (natp n) (integerp x) (integerp y))
;;            (equal (bvminus n x y)
;;                   (ripple-carry-adder n x (bvnot n y) 1)))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :use (;(:instance RIPPLE-CARRY-ADDER-of-bvchop-arg3 (y (+ -1 (- Y))) (carry 1))
;;                  (:instance bvplus-becomes-ripple-carry-adder-helper (carry 1) (x (bvchop n x)) (y (BVNOT N Y)))
;;                  ;(:instance bvplus-becomes-ripple-carry-adder-helper (carry 1) (x (bvchop n x)) (y (+ -1 (- Y))))
;;                  )
;;            :in-theory (e/d (bvchop-of-sum-cases ;BVNOT
;;                             lognot bvplus bvminus-becomes-bvplus-of-bvuminus bvuminus-becomes-flip-bits-and-add-one)
;;                            (RIPPLE-CARRY-ADDER-OF-BVCHOP-ARG3)))))

(defthm full-adder-carry-rewrite
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y)
                (unsigned-byte-p 1 z))
           (equal (full-adder-carry x y z)
                  (getbit 1 (+ x y z))))
  :hints (("Goal" :cases ((and (equal 0 x)(equal 0 y)(equal 0 z))
                          (and (equal 0 x)(equal 0 y)(equal 1 z))
                          (and (equal 0 x)(equal 1 y)(equal 0 z))
                          (and (equal 0 x)(equal 1 y)(equal 1 z))
                          (and (equal 1 x)(equal 0 y)(equal 0 z))
                          (and (equal 1 x)(equal 0 y)(equal 1 z))
                          (and (equal 1 x)(equal 1 y)(equal 0 z))
                          (and (equal 1 x)(equal 1 y)(equal 1 z))))))

;; (defthm full-adder-sum-rewrite
;;   (implies (and (unsigned-byte-p 1 x)
;;                 (unsigned-byte-p 1 y)
;;                 (unsigned-byte-p 1 z))
;;            (equal (full-adder-sum x y z)
;;                   (getbit 0 (+ x y z))))
;;   :hints (("Goal" :in-theory (e/d () (BVXOR-1-BECOMES-BITXOR)))))
