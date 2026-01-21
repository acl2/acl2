; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Mayank Manjrekar <mayank.manjrekar2@arm.com>

(in-package "RTL")

(include-book "imul64")
(include-book "../../ctv-cp")
(include-book "projects/rac/lisp/alt-const-fns-gen" :dir :system)

;;; Correctness of the compress function:
(compress::def-ctv-thmd compress-lemma
  (implies (and (integerp pp0)
                (integerp pp1)
                (integerp pp2)
                (integerp pp3)
                (integerp pp4)
                (integerp pp5)
                (integerp pp6)
                (integerp pp7)
                (integerp pp8)
                (integerp pp9)
                (integerp pp10)
                (integerp pp11)
                (integerp pp12)
                (integerp pp13)
                (integerp pp14)
                (integerp pp15)
                (integerp pp16)
                (integerp pp17)
                (integerp pp18)
                (integerp pp19)
                (integerp pp20)
                (integerp pp21)
                (integerp pp22)
                (integerp pp23)
                (integerp pp24)
                (integerp pp25)
                (integerp pp26)
                (integerp pp27)
                (integerp pp28)
                (= (bits pp9 105 73) 0)
                (= (bits pp9 17 17) 0)
                (= (bits pp9 15 0) 0)
                (= (bits pp8 105 71) 0)
                (= (bits pp8 15 15) 0)
                (= (bits pp8 13 0) 0)
                (= (bits pp7 105 69) 0)
                (= (bits pp7 13 13) 0)
                (= (bits pp7 11 0) 0)
                (= (bits pp6 105 67) 0)
                (= (bits pp6 11 11) 0)
                (= (bits pp6 9 0) 0)
                (= (bits pp5 105 65) 0)
                (= (bits pp5 9 9) 0)
                (= (bits pp5 7 0) 0)
                (= (bits pp4 105 63) 0)
                (= (bits pp4 7 7) 0)
                (= (bits pp4 5 0) 0)
                (= (bits pp3 105 61) 0)
                (= (bits pp3 5 5) 0)
                (= (bits pp3 3 0) 0)
                (= (bits pp28 105 104) 0)
                (= (bits pp28 51 0) 0)
                (= (bits pp27 105 105) 0)
                (= (bits pp27 51 0) 0)
                (= (bits pp26 51 51) 0)
                (= (bits pp26 49 0) 0)
                (= (bits pp25 105 105) 0)
                (= (bits pp25 49 49) 0)
                (= (bits pp25 47 0) 0)
                (= (bits pp24 105 103) 0)
                (= (bits pp24 47 47) 0)
                (= (bits pp24 45 0) 0)
                (= (bits pp23 105 101) 0)
                (= (bits pp23 45 45) 0)
                (= (bits pp23 43 0) 0)
                (= (bits pp22 105 99) 0)
                (= (bits pp22 43 43) 0)
                (= (bits pp22 41 0) 0)
                (= (bits pp21 105 97) 0)
                (= (bits pp21 41 41) 0)
                (= (bits pp21 39 0) 0)
                (= (bits pp20 105 95) 0)
                (= (bits pp20 39 39) 0)
                (= (bits pp20 37 0) 0)
                (= (bits pp2 105 59) 0)
                (= (bits pp2 3 3) 0)
                (= (bits pp2 1 0) 0)
                (= (bits pp19 105 93) 0)
                (= (bits pp19 37 37) 0)
                (= (bits pp19 35 0) 0)
                (= (bits pp18 105 91) 0)
                (= (bits pp18 35 35) 0)
                (= (bits pp18 33 0) 0)
                (= (bits pp17 105 89) 0)
                (= (bits pp17 33 33) 0)
                (= (bits pp17 31 0) 0)
                (= (bits pp16 105 87) 0)
                (= (bits pp16 31 31) 0)
                (= (bits pp16 29 0) 0)
                (= (bits pp15 105 85) 0)
                (= (bits pp15 29 29) 0)
                (= (bits pp15 27 0) 0)
                (= (bits pp14 105 83) 0)
                (= (bits pp14 27 27) 0)
                (= (bits pp14 25 0) 0)
                (= (bits pp13 105 81) 0)
                (= (bits pp13 25 25) 0)
                (= (bits pp13 23 0) 0)
                (= (bits pp12 105 79) 0)
                (= (bits pp12 23 23) 0)
                (= (bits pp12 21 0) 0)
                (= (bits pp11 105 77) 0)
                (= (bits pp11 21 21) 0)
                (= (bits pp11 19 0) 0)
                (= (bits pp10 105 75) 0)
                (= (bits pp10 19 19) 0)
                (= (bits pp10 17 0) 0)
                (= (bits pp1 105 57) 0)
                (= (bits pp1 1 1) 0)
                (= (bits pp0 105 56) 0))
           (equal (compress pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15 pp16 pp17 pp18 pp19 pp20 pp21 pp22 pp23 pp24 pp25 pp26 pp27 pp28)
                  (bits (+ pp0 pp1 pp2 pp3 pp4 pp5 pp6 pp7 pp8 pp9 pp10 pp11 pp12 pp13 pp14 pp15 pp16 pp17 pp18 pp19 pp20 pp21 pp22 pp23 pp24 pp25 pp26 pp27 pp28) 105 0)))
     :expand (compress))

;;; The remaining part of this book uses the compress-lemma to prove the
;;; correctness of imul function.

(local (arith-5-for-rtl))

(local
 (encapsulate (((mana) => *)
               ((manb) => *)
               ((expazero) => *)
               ((expbzero) => *))
   (local (defundd mana () 0))
   (local (defundd manb () 0))
   (local (defundd expazero () 0))
   (local (defundd expbzero () 0))
   (bvecthm bvecp-mana
     (bvecp (mana) 52)
     :hints (("Goal" :in-theory (e/d (mana) ()))))
   (bvecthm bvecp-manb
     (bvecp (manb) 52)
     :hints (("Goal" :in-theory (e/d (manb) ()))))
   (bitthm bitp-expazero
     (bitp (expazero))
     :hints (("Goal" :in-theory (e/d (expazero) ()))))
   (bitthm bitp-expbzero
     (bitp (expbzero))
     :hints (("Goal" :in-theory (e/d (expbzero) ()))))))

#|
(make-event
 (alt-const-fns-gen
  'cp
  '(DEFUN IMUL (MANA MANB EXPAZERO EXPBZERO)
    (LET* ((PP NIL)
           (MULTIPLIER MANB)
           (MULTIPLIER (BITS (ASH MULTIPLIER 1) 52 0))
           (:PP (IMUL-LOOP-0 0 MULTIPLIER MANA PP))
           (:IA (IF1 EXPAZERO 0 MANB))
           (IB (IF1 EXPBZERO 0 MANA))
           (:IB (SETBITN IB 53 52
                (LOGAND1 (LOGNOT1 EXPAZERO)
                 (LOGNOT1 EXPBZERO))))
           (SUM 0))
     (COMPRESS (AG 0 PP)
      (AG 1 PP)
      (BITS (ASH (AG 2 PP) 2) 105 0)
      (BITS (ASH (AG 3 PP) 4) 105 0)
      (BITS (ASH (AG 4 PP) 6) 105 0)
      (BITS (ASH (AG 5 PP) 8) 105 0)
      (BITS (ASH (AG 6 PP) 10) 105 0)
      (BITS (ASH (AG 7 PP) 12) 105 0)
      (BITS (ASH (AG 8 PP) 14) 105 0)
      (BITS (ASH (AG 9 PP) 16) 105 0)
      (BITS (ASH (AG 10 PP) 18) 105 0)
      (BITS (ASH (AG 11 PP) 20) 105 0)
      (BITS (ASH (AG 12 PP) 22) 105 0)
      (BITS (ASH (AG 13 PP) 24) 105 0)
      (BITS (ASH (AG 14 PP) 26) 105 0)
      (BITS (ASH (AG 15 PP) 28) 105 0)
      (BITS (ASH (AG 16 PP) 30) 105 0)
      (BITS (ASH (AG 17 PP) 32) 105 0)
      (BITS (ASH (AG 18 PP) 34) 105 0)
      (BITS (ASH (AG 19 PP) 36) 105 0)
      (BITS (ASH (AG 20 PP) 38) 105 0)
      (BITS (ASH (AG 21 PP) 40) 105 0)
      (BITS (ASH (AG 22 PP) 42) 105 0)
      (BITS (ASH (AG 23 PP) 44) 105 0)
      (BITS (ASH (AG 24 PP) 46) 105 0)
      (BITS (ASH (AG 25 PP) 48) 105 0)
      (BITS (ASH (AG 26 PP) 50) 105 0)
      (BITS (ASH IB 52) 105 0)
      (BITS (ASH IA 52) 105 0))))))
|#

(local
 (encapsulate nil
   (set-ignore-ok t)
   (defundd pp nil
     (b* ((pp nil)
          (multiplier (manb))
          (multiplier (bits (ash multiplier 1) 52 0)))
       (imul-loop-0 0 multiplier (mana) pp)))
   (defundd ia nil (if1 (expazero) 0 (manb)))
   (defundd ib nil
     (b* ((ib (if1 (expbzero) 0 (mana))))
       (setbitn ib 53 52
                (logand1 (lognot1 (expazero))
                         (lognot1 (expbzero))))))
   (defundd cp nil
     (compress (ag 0 (pp))
               (ag 1 (pp))
               (bits (ash (ag 2 (pp)) 2) 105 0)
               (bits (ash (ag 3 (pp)) 4) 105 0)
               (bits (ash (ag 4 (pp)) 6) 105 0)
               (bits (ash (ag 5 (pp)) 8) 105 0)
               (bits (ash (ag 6 (pp)) 10) 105 0)
               (bits (ash (ag 7 (pp)) 12) 105 0)
               (bits (ash (ag 8 (pp)) 14) 105 0)
               (bits (ash (ag 9 (pp)) 16) 105 0)
               (bits (ash (ag 10 (pp)) 18) 105 0)
               (bits (ash (ag 11 (pp)) 20) 105 0)
               (bits (ash (ag 12 (pp)) 22) 105 0)
               (bits (ash (ag 13 (pp)) 24) 105 0)
               (bits (ash (ag 14 (pp)) 26) 105 0)
               (bits (ash (ag 15 (pp)) 28) 105 0)
               (bits (ash (ag 16 (pp)) 30) 105 0)
               (bits (ash (ag 17 (pp)) 32) 105 0)
               (bits (ash (ag 18 (pp)) 34) 105 0)
               (bits (ash (ag 19 (pp)) 36) 105 0)
               (bits (ash (ag 20 (pp)) 38) 105 0)
               (bits (ash (ag 21 (pp)) 40) 105 0)
               (bits (ash (ag 22 (pp)) 42) 105 0)
               (bits (ash (ag 23 (pp)) 44) 105 0)
               (bits (ash (ag 24 (pp)) 46) 105 0)
               (bits (ash (ag 25 (pp)) 48) 105 0)
               (bits (ash (ag 26 (pp)) 50) 105 0)
               (bits (ash (ib) 52) 105 0)
               (bits (ash (ia) 52) 105 0)))
   (defthmd imul-lemma
     (equal (cp)
            (imul (mana)
                  (manb)
                  (expazero)
                  (expbzero)))
     :hints
     (("Goal" :in-theory nil
              :do-not '(preprocess)
              :clause-processor (expand-reduce-cp clause '(nil cp pp ia ib imul)
                                                  state))))))
;; ======================================================================

(local
 (encapsulate
   ()

   (local
    (defthm aux-1
      (implies (and (natp i)
                    (< i j))
               (equal (ag i (imul-loop-0 j y x pp))
                      (ag i pp)))
      :hints (("Goal" :in-theory (e/d (imul-loop-0)
                                      (bits-bits
                                       bits-cat-constants
                                       acl2::default-lognot
                                       acl2::default-less-than-1
                                       bvecp-bitn-1
                                       bits-tail-gen))))))

   (local
    (defthm aux-2a
      (and (implies (integerp i)
                    (equal (bitn (* 2 x) i)
                           (bitn x (1- i))))
           (implies (integerp x)
                    (and (equal (bits (+ y (* *2^54* x))
                                      53 0)
                                (bits y 53 0))
                         (equal (bits (+ y (* *2^55* x))
                                      54 0)
                                (bits y 54 0)))))
      :hints (("Goal" :in-theory (e/d (bitn-def bits fl mod)
                                      (acl2::default-floor-1
                                       acl2::default-times-1
                                       acl2::default-times-2
                                       acl2::default-mod-1
                                       acl2::default-mod-ratio
                                       acl2::default-plus-1))))))

   (local
    (def-gl-rule aux-2b
      :hyp (bvecp x 52)

      :concl (and (equal (bits (+ 18014398509481983 (- x)) 52 0)
                         (- 9007199254740991 x))
                  (equal (bits (+ 18014398509481983 (* -2 x)) 52 0)
                         (- 9007199254740991 (* 2 x))))
      :g-bindings (gl::auto-bindings (:nat x 52))))

   (local
    (defthmd imul-loop-0-to-pp4p-aux-1
      (implies (and (bvecp x 52)
                    (bvecp y 52)
                    (equal 2y (ash y 1))
                    (natp i)
                    (<= i 26))
               (equal (ag i (imul-loop-0 i 2y x pp))
                      (case i
                        (0 (pp4p i x y 53))
                        (26 (/ (- (pp4p i x y 53)
                                  *2^106*)
                               (expt 2 (* 2 (1- i)))))
                        (t (/ (pp4p i x y 53)
                              (expt 2 (* 2 (1- i))))))))
      :hints (("Goal"
               :expand (:free (y) (imul-loop-0 i y x pp))
               :use ((:instance bitn-plus-bits
                      (x y)
                      (m (1- (* 2 i)))
                      (n (1+ (* 2 i))))
                     (:instance bitn-plus-bits
                      (x y)
                      (m (1- (* 2 i)))
                      (n (* 2 i))))
               :in-theory (e/d (pp4p
                                nbit
                                bmux4p
                                mag
                                bitn-bits
                                bvecp-bits-0
                                ;; bits-lognot
                                lognot
                                cat
                                bvecp)
                               (acl2::default-times-1
                                acl2::default-times-2))))))

   (local
    (defthm aux-3
      (equal (ag 26 (imul-loop-0 25 y x pp))
             (ag 26 (imul-loop-0 26 y x pp)))
      :hints (("Goal"
               :expand (:free (i pp) (imul-loop-0 i y x pp))
               :in-theory (e/d (imul-loop-0)
                               (bits-bits
                                bits-cat-constants
                                acl2::default-lognot
                                acl2::default-less-than-1
                                bvecp-bitn-1
                                bits-tail-gen))))))

   (local
    (defthmd imul-loop-0-to-pp4p-aux-2
      (implies (and (bvecp x 52)
                    (bvecp y 52)
                    (equal 2y (ash y 1))
                    (natp i)
                    (natp j)
                    (< j i)
                    (<= i 26))
               (equal (ag i (imul-loop-0 j 2y x pp))
                      (case i
                        (0 (pp4p i x y 53))
                        (26 (/ (- (pp4p i x y 53)
                                  *2^106*)
                               (expt 2 (* 2 (1- i)))))
                        (t (/ (pp4p i x y 53)
                              (expt 2 (* 2 (1- i))))))))
      :hints (("Goal" :in-theory (e/d (imul-loop-0
                                       imul-loop-0-to-pp4p-aux-1)
                                      (bits-bits
                                       bits-cat-constants
                                       bvecp-bitn-1
                                       bits-tail-gen))))))

   (defthmd imul-loop-0-to-pp4p
     (implies (and (bvecp x 52)
                   (bvecp y 52)
                   (equal 2y (ash y 1))
                   (natp i)
                   (natp j)
                   (<= j i)
                   (<= i 26))
              (equal (ag i (imul-loop-0 j 2y x pp))
                     (case i
                       (0 (pp4p i x y 53))
                       (26 (/ (- (pp4p i x y 53)
                                 *2^106*)
                              (expt 2 (* 2 (1- i)))))
                       (t (/ (pp4p i x y 53)
                             (expt 2 (* 2 (1- i))))))))
     :hints (("Goal" :use (imul-loop-0-to-pp4p-aux-1
                           imul-loop-0-to-pp4p-aux-2))))))

(local
 (defun sum-pp (m)
   (if (zp m)
       0
     (if (= m 1)
         (ag 0 (pp))
       (+ (* (expt 2 (* 2 (- m 2)))
             (ag (1- m) (pp)))
          (sum-pp (1- m)))))))

(local (in-theory (disable (sum-pp))))

(local
 (defthmd sum-pp-pp
   (implies (and (natp m) (<= m 27))
            (equal (sum-pp m)
                   (if (= m 27)
                       (- (sum-pp4p (mana) (manb) m 53)
                          *2^106*)
         (sum-pp4p (mana) (manb) m 53))))
   :hints (("Goal" :in-theory (enable pp
                                      imul-loop-0-to-pp4p
                                      bvecp)))))

(local
 (defthmd sum-pp-rewrite
   (equal (sum-pp 27)
    (+ *2^106* (* (mana) (manb))))
   :hints (("Goal" :in-theory (enable sum-pp-pp booth4-corollary-3 bvecp)))))

(local
 (defundd sa ()
   (if1 (expazero)
        (mana)
        (+ *2^52* (mana)))))

(local
 (defundd sb ()
   (if1 (expbzero)
        (manb)
        (+ *2^52* (manb)))))

(local
 (bvecthm bvecp-sa
   (bvecp (sa) 53)
   :hints (("Goal" :in-theory (enable sa bvecp)))))

(local
 (bvecthm bvecp-sb
   (bvecp (sb) 53)
   :hints (("Goal" :in-theory (enable sb bvecp)))))

(local
 (defthmd sa*sb-to-sum-pp
   (equal (* (sa) (sb))
          (+ (sum-pp 27)
             (* *2^52* (+ (ia) (ib)))
             (- *2^106*)))
   :hints (("Goal" :in-theory (enable sum-pp-rewrite
                                      sa sb
                                      ia ib
                                      cat
                                      bvecp)))))

(local
 (bvecthm bvecp-pp-i
   (implies (and (natp i) (< i 26))
            (bvecp (ag i (pp)) 57))
   :hints (("Goal" :in-theory (enable bvecp
                                      pp
                                      imul-loop-0-to-pp4p
                                      pp4p
                                      cat)))))

(local
 (bvecthm bvecp-pp-26
   (bvecp (ag 26 (pp)) 56)
   :hints (("Goal" :in-theory (enable bvecp
                                      pp
                                      imul-loop-0-to-pp4p
                                      pp4p
                                      cat)))))

(local
 (defthmd comp-1
   (equal (+ *2^106* (* (sa) (sb)))
    (+ (ag 0 (pp))
       (ag 1 (pp))
       (* (expt 4 1) (ag 2 (pp)))
       (* (expt 4 2) (ag 3 (pp)))
       (* (expt 4 3) (ag 4 (pp)))
       (* (expt 4 4) (ag 5 (pp)))
       (* (expt 4 5) (ag 6 (pp)))
       (* (expt 4 6) (ag 7 (pp)))
       (* (expt 4 7) (ag 8 (pp)))
       (* (expt 4 8) (ag 9 (pp)))
       (* (expt 4 9) (ag 10 (pp)))
       (* (expt 4 10) (ag 11 (pp)))
       (* (expt 4 11) (ag 12 (pp)))
       (* (expt 4 12) (ag 13 (pp)))
       (* (expt 4 13) (ag 14 (pp)))
       (* (expt 4 14) (ag 15 (pp)))
       (* (expt 4 15) (ag 16 (pp)))
       (* (expt 4 16) (ag 17 (pp)))
       (* (expt 4 17) (ag 18 (pp)))
       (* (expt 4 18) (ag 19 (pp)))
       (* (expt 4 19) (ag 20 (pp)))
       (* (expt 4 20) (ag 21 (pp)))
       (* (expt 4 21) (ag 22 (pp)))
       (* (expt 4 22) (ag 23 (pp)))
       (* (expt 4 23) (ag 24 (pp)))
       (* (expt 4 24) (ag 25 (pp)))
       (* (expt 4 25) (ag 26 (pp)))
       (* (expt 2 52) (+ (ia) (ib)))))
   :hints (("Goal"
            :expand ((:free (m) (sum-pp m)))
            :in-theory (enable sa*sb-to-sum-pp)))))

(local
 (defun find-k (n)
   (b* ((n (unquote n)))
     (if (= n (expt 2 (expo n)))
         `((k . ,(kwote (expo n))))
       nil))))

(local-defthm bits-shift-up-1-const
  (implies (and (integerp i)
                (syntaxp (quotep n))
                (bind-free (find-k n) (k))
                (integerp k)
                (integerp j)
                (equal n (expt 2 k)))
           (equal (bits (* n x) i j)
                  (bits x (- i k) (- j k))))
  :hints (("Goal" :in-theory (e/d () ())
                  :use (bits-shift-up-1))))

(local-defthm bitn-shift-up-1-const
  (implies (and (syntaxp (quotep n))
                (bind-free (find-k n) (k))
                (integerp k)
                (integerp j)
                (equal n (expt 2 k)))
           (equal (bitn (* n x) j)
                  (bitn x (- j k))))
  :hints (("Goal" :in-theory (e/d (bitn) (bits-n-n-rewrite))
                  :use (:instance bits-shift-up-1 (i j)))))

(local-defthm bits-of-neg-ind
  (implies (and (integerp x)
                (integerp n)
                (integerp p)
                (< n 0))
           (equal (bits x p n)
                  (* (expt 2 (- n)) (bits x p 0))))
  :hints (("Goal" :in-theory (e/d () ())
                  :use ((:instance bits-plus-bits
                         (x x) (n p) (m n) (p 0))))))

(local-defthm bitn-pp-1-is-0
  (implies (and (natp i)
                (< 0 i)
                (<= i 26))
           (equal (bitn (ag i (pp)) 1) 0))
  :hints (("Goal" :in-theory (e/d (pp
                                   imul-loop-0-to-pp4p
                                   pp4p
                                   cat bvecp
                                   bits-plus-mult-2-meta
                                   bitn)
                                  (bits-n-n-rewrite)))))

(local-defthm bits-ia-53-52-0
  (And (equal (bits (ia) 53 52) 0)
       (equal (bits (ia) 53 0) (ia)))
  :hints (("Goal" :in-theory (e/d (ia bvecp-bits-0) ()))))

(local-defthm bitn-ib-53-0
  (and (equal (bitn (ib) 53) 0)
       (equal (bits (ib) 53 0) (ib)))
  :hints (("Goal" :in-theory (e/d (ib cat bvecp) ()))))

(local-defthm bvecp-ag-0-56
  (bvecp (ag 0 (pp)) 56)
  :hints (("Goal" :in-theory (e/d (pp
                                   imul-loop-0-to-pp4p
                                   pp4p) ()))))

(local-defthm sa*sb-bvecp
  (bvecp (* (sa) (sb)) 106)
  :hints (("Goal" :in-theory (e/d (bvecp
                                   sa sb) ())
                  :nonlinearp t)))

(local-defthm cp-sum-pp
  (equal (* (sa) (sb))
         (cp))
  :hints (("Goal" :in-theory (e/d (cp
                                   bitn-bits
                                   bvecp-bits-0
                                   bits-plus-mult-2-meta
                                   bitn-shift-up-alt)
                                  ())
                  :use (comp-1
                        (:instance compress-lemma
                         (pp0 (ag 0 (pp)))
                         (pp1 (ag 1 (pp)))
                         (pp2   (* 4 (AG 2 (PP))))
                         (pp3  (* 16 (AG 3 (PP))))
                         (pp4  (* 64 (AG 4 (PP))))
                         (pp5  (* 256 (AG 5 (PP))))
                         (pp6  (* 1024 (AG 6 (PP))))
                         (pp7  (* 4096 (AG 7 (PP))))
                         (pp8  (* 16384 (AG 8 (PP))))
                         (pp9  (* 65536 (AG 9 (PP))))
                         (pp10 (* 262144 (AG 10 (PP))))
                         (pp11 (* 1048576 (AG 11 (PP))))
                         (pp12 (* 4194304 (AG 12 (PP))))
                         (pp13 (* 16777216 (AG 13 (PP))))
                         (pp14 (* 67108864 (AG 14 (PP))))
                         (pp15 (* 268435456 (AG 15 (PP))))
                         (pp16 (* 1073741824 (AG 16 (PP))))
                         (pp17 (* 4294967296 (AG 17 (PP))))
                         (pp18 (* 17179869184 (AG 18 (PP))))
                         (pp19 (* 68719476736 (AG 19 (PP))))
                         (pp20 (* 274877906944 (AG 20 (PP))))
                         (pp21 (* 1099511627776 (AG 21 (PP))))
                         (pp22 (* 4398046511104 (AG 22 (PP))))
                         (pp23 (* 17592186044416 (AG 23 (PP))))
                         (pp24 (* 70368744177664 (AG 24 (PP))))
                         (pp25 (* 281474976710656 (AG 25 (PP))))
                         (pp26 (BITS (* 1125899906842624 (AG 26 (PP))) 105 0))
                         (pp27 (BITS (* 4503599627370496 (IB)) 105 0))
                         (pp28 (BITS (* 4503599627370496 (IA)) 105 0)))))))

(local-defthm lemma-to-be-instantiated
  (equal (* (+ (if1 (expazero) 0 (expt 2 52)) (mana))
            (+ (if1 (expbzero) 0 (expt 2 52)) (manb)))
         (imul (mana) (manb) (expazero) (expbzero)))
  :hints (("Goal" :in-theory (e/d (sa sb
                                   imul-lemma) (cp-sum-pp))
                  :use (cp-sum-pp))))

(defthm computeprod-correct
  (implies (and (bvecp mana 52)
                (bvecp manb 52)
                (bitp expazero)
                (bitp expbzero))
           (equal (imul mana manb expazero expbzero)
                  (* (+ (if1 expazero 0 (expt 2 52)) mana)
                     (+ (if1 expbzero 0 (expt 2 52)) manb))))
  :hints (("Goal" :in-theory (e/d () ())
                  :use ((:functional-instance lemma-to-be-instantiated
                         (mana (lambda () (if (and (bvecp mana 52)
                                                   (bvecp manb 52)
                                                   (bitp expazero)
                                                   (bitp expbzero))
                                              mana (mana))))
                         (manb (lambda () (if (and (bvecp mana 52)
                                               (bvecp manb 52)
                                               (bitp expazero)
                                               (bitp expbzero))
                                              manb (manb))))
                         (expazero (lambda () (if (and (bvecp mana 52)
                                                       (bvecp manb 52)
                                                       (bitp expazero)
                                                       (bitp expbzero))
                                                  expazero (expazero))))
                         (expbzero (lambda () (if (and (bvecp mana 52)
                                                       (bvecp manb 52)
                                                       (bitp expazero)
                                                       (bitp expbzero))
                                                  expbzero (expbzero)))))))))
