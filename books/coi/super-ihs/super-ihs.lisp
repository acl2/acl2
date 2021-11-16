; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
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

(in-package "ACL2")

(include-book "hacks")
(include-book "eric")
(include-book "c-functions")
(include-book "lshu")
(include-book "min-max")
(include-book "meta")

;(in-theory (disable len))

(encapsulate
 ()
 (local
  (defthm sbp-loghead-helper
    (implies (and (< m n)
                  (integerp n)
                  (integerp m)
                  (< 0 n)
                  (< 0 m)
                  )
             (equal (signed-byte-p n (loghead m v))
                    (signed-byte-p n 0)))
    :hints (("goal" :use (:instance unsigned-byte-p-loghead (size1 (1- n)) (size m) (i v))
             :in-theory (e/d (signed-byte-p unsigned-byte-p integer-range-p ) (unsigned-byte-p-loghead) )))))

; I think the strict < in (< m n) is necessary.  Consider (signed-byte-p 4 (loghead 4 15)) = nil
 (defthm sbp-loghead
   (implies (< m n)
            (equal (signed-byte-p n (loghead m v))
                   (and (integerp n)
                        (< 0 n))))
   :hints (("Goal" :use (sbp-loghead-helper)))))

(defthm logcar-logxor
  (implies (and (integerp a) (integerp b))
           (equal (logcar (logxor a b))
                  (b-xor (logcar a) (logcar b))))
  :hints (("goal" :in-theory (enable
                              LOGOPS-RECURSIVE-DEFINITIONS-THEORY
                              simplify-bit-functions))))

(defthm logxor-lognot-one
  (implies (and (integerp a)
                (integerp b))
           (equal (logxor (lognot a) b)
                  (lognot (logxor a b)))))

;could prove from the -one version but logxor-rewrite is on now...
(defthm logxor-lognot-two
  (implies (and (integerp a)
                (integerp b))
           (equal (logxor a (lognot b))
                  (lognot (logxor a b)))))

(defthm logxor-neg
  (implies (and (integerp a)
                (integerp b))
           (equal (< (logxor a b) 0)
                  (not (eq (< a 0) (< b 0)))))
  :hints (("goal" :in-theory (enable BINARY-LOGEQV
                                     BINARY-LOGXOR
                                     LOGORC1
                                     LOGAND-LOGIOR
                                     LOGAND-NEG
                                     ))))

(defthm integerp-logand
  (integerp (logand x y)))

(defthm integerp-logxor
  (integerp (logxor x y)))

(defthm integerp-logior
  (integerp (logior x y)))

(defthm integerp-logext
  (integerp (logext x y)))

(defthm rationalp-logand
  (rationalp (logand x y)))

(defthm rationalp-logxor
  (rationalp (logxor x y)))

(defthm rationalp-logior
  (rationalp (logior x y)))

(defthm rationalp-logext
  (rationalp (logext x y)))

;; (defthm logbitp-too-big-helper
;;   (implies
;;    (and
;;     (unsigned-byte-p n x)
;;     (< 0 n) ;; extraneous
;;     (integerp n) ;; extraneous
;;     (integerp x)  ;; extraneous
;;     (integerp m)
;;     (<= n m))
;;    (not (logbitp m x)))
;;   :hints (("Goal"
;;            :induct (sub1-sub1-logcdr-induction n m x)
;;            :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)))
;;   :rule-classes nil)





(defthm logbitp-too-big
  (implies (and (unsigned-byte-p n x) ;n is a free variable
                (<= n (ifix m)))
           (not (logbitp m x)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (ifix ;LOGBITP-WITH-NON-INTEGER ;UNSIGNED-BYTE-p
                                        )
                                  (LOGBITP-N-UNSIGNED-BYTE-P-N
                                   OPEN-LOGCONS))
           :use (:instance LOGBITP-N-UNSIGNED-BYTE-P-N (n m)))))

(defthm usbp-logext-narrower
  (implies (and (< m n)
                (unsigned-byte-p m v)
                (integerp n)
                (integerp m)
                (< 0 n)
                (< 0 m)
                )
           (unsigned-byte-p m (logext n v)))
  :hints (("goal" :in-theory (enable logext))))

;we already have rules to rewrite to b-ior and b-and in this case
(defthmd perhaps-<=-1-is-usb1?
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (and (<= (logior x y) 1)
                (<= (logand x y) 1) ;this case doesn't need such strong hyps?
                )))

;see also SIGNED-BYTE-P-LOGEXT
(defthm signed-byte-p-of-logext
  (equal (signed-byte-p n (logext n x))
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :use (:instance SIGNED-BYTE-P-LOGEXT (i x) (size n) (size1 n))
           :in-theory (disable SIGNED-BYTE-P-LOGEXT))))

;add this one to the RTL library?
(defthm logxor-cancel2
  (equal (logxor b (logxor b a))
         (ifix a)
         )
  :hints (("goal" :in-theory (disable LOGXOR-REWRITE)
           :use (:instance commutativity-of-logxor
                           (i b) (j (logxor b a))))))


(defthm sbp32-negation
  (implies (signed-byte-p 32 x)
           (equal (signed-byte-p 32 (- x))
                  (not (equal x -2147483648))))
:hints (("goal" :in-theory (enable integer-range-p signed-byte-p))))

;eric's attempt to improve that rule.  not quite right..
;; (defthm sbp32-negation
;;   (implies (signed-byte-p 32 (- x))
;;            (if (acl2-numberp x)
;;                (if (equal x 2147483648)
;;                    nil
;;                  (and (signed-byte-p 32 x)
;;                       (NOT (EQUAL X -2147483648))))
;;              t))
;;   :rule-classes nil
;;   :hints (("goal" :in-theory (enable integer-range-p signed-byte-p))))




;; (thm
;;  (implies (zp size)
;;           (equal (logext size i)
;;                  -1))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable logext LOGAPP))))


;bzo do more on this
(defthm signed-byte-p-logext-better
  (implies (and (>= size1 size)
                (> size 0)
                (integerp size)
                )
           (equal (signed-byte-p size1 (logext size i))
                  (integerp size1)
                  ))
  :hints (("Goal" :in-theory (disable signed-byte-p-logext)
           :use (signed-byte-p-logext))))

(in-theory (disable signed-byte-p-logext)) ;we'll use signed-byte-p-logext-better instead


;; (defthm logbitp-when-i-is-not-an-integerp
;;   (implies (not (integerp i))
;;            (equal (logbitp i j)
;;                   (not (equal 0 (logcar j)))))
;;   :hints (("Goal" :in-theory (enable logbitp
;;                                      oddp-to-logcar
;;                                      )
;;            :do-not '(generalize eliminate-destructors)
;;            )))





(defthm logext-+-expt
  (implies (and (integerp x)
                (integerp n)
                (< 0 n)
                )
           (equal (logext n (+ x (expt 2 n)))
                  (logext n x)))
  :hints (("goal" :in-theory (e/d (LRDT
                                     open-logcons)
                                  (LOGCONS-OF-0
                                   )))))

(local (in-theory (enable open-logcons)))

(local (in-theory (disable logcons-of-0)))

;move
(defthm logext-ignores-subtraction-of-expt
  (implies (and (integerp x)
                (integerp n)
                (< 0 n)
                )
           (equal (logext n (+ x (- (expt 2 n))))
                  (logext n x)))
  :hints (("goal" :in-theory (enable LRDT))))


;move
(defthm logext-ignores-subtraction-of-expt-alt
  (implies (and (integerp x) (integerp n) (< 0 n))
           (equal (logext n (+ (- (expt 2 n)) x))
                  (logext n x)))
  :hints
  (("goal" :use logext-ignores-subtraction-of-expt
    :in-theory (disable logext-ignores-subtraction-of-expt))))



;bzo move this stuff.  where should it go?

;We leave this function enabled and let rules about logext fire.
(defun unsigned-to-signed (n x)
  (declare (xargs :guard-hints (("Goal" :in-theory (enable INTEGERP-+-MINUS-*))))
           (type (integer 1 *) n)
           (type integer x))
  (logext n x))

;bzo is this really right?
;We leave this function enabled and let rules about loghead fire.
(defun signed-to-unsigned (n x)
  (declare (xargs :guard
                  (and (integerp n)
                       (>= n 0)
                       (integerp x))))
  (loghead n x))

;improve
;see LOGEXTU-AS-LOGHEAD
(defthm loghead--of--logext-when-unsigned-byte-p
  (implies (and (unsigned-byte-p n x)
                (< 0 n))
           (equal (loghead n (logext n x))
                  x))
  :hints (("Goal" ; :use (:instance LOGHEAD-+-EXPT-constant-version (k (expt 2 n)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;loghead
                            INTEGERP-+-MINUS-* ;bzo why is this disabled?
                            SIGNED-BYTE-P
                            UNSIGNED-BYTE-P
                            INTEGER-RANGE-P
                            ;logext
                            )
                           (
;                            expt2*
                            SIGN-LOGEXT-AS-LOGBITP)))))

;improve
;see LOGEXT-LOGHEAD
(defthm logext--of--loghead-when-signed-byte-p
  (implies (and (signed-byte-p n x)
                (< 0 n))
           (equal (logext n (loghead n x))
                  x))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (;loghead
                            INTEGERP-+-MINUS-* ;bzo why is this disabled?
                            SIGNED-BYTE-P

                            UNSIGNED-BYTE-P
                            INTEGER-RANGE-P
                            ;logext
                            )
                           (SIGN-LOGEXT-AS-LOGBITP)))))


;improve
;go the other way too?
(defthmd loghead-equal-rewrite
  (implies (and ; (< 0 n)
            (signed-byte-p n x)
            (unsigned-byte-p n k)
            )
           (equal (equal (loghead n x) k)
                  (if (and (integerp n)
                           (< 0 n))
                      (if (signed-byte-p n x)
                          (equal x (logext n k))
                        nil)
                    (equal 0 k)))))

;move like this?
;bzo rename
(defthm loghead-equal-rewrite-constant-case
  (implies (and (syntaxp (quotep k))
                (< 0 n)
                (signed-byte-p n x)
                (unsigned-byte-p n k))
           (equal (equal (loghead n x) k)
                  (equal x (logext n k)))))






(defthm signed-byte-p-from-bounds-free-one
  (implies (and (<= x free1)
                (<= free1 (+ -1 (expt 2 (+ -1 n))))
                (<= free2 x)
                (<= (- (expt 2 (+ -1 n))) free2)
                )
           (equal (signed-byte-p n x)
                  (and (integerp x)
                       (< 0 n)
                       (integerp n)
                       )))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P SIGNED-BYTE-P))))

(defthm signed-byte-p-from-bounds-free-two
  (implies (and (<= x free1)
                (<= free1 (+ -1 (expt 2 (+ -1 n))))
                (< free2 x)
                (<= (+ -1 (- (expt 2 (+ -1 n)))) free2)
                )
           (equal (signed-byte-p n x)
                  (and (integerp x)
                       (< 0 n)
                       (integerp n)
                       )))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P SIGNED-BYTE-P))))

(defthm signed-byte-p-from-bounds-free-three
  (implies (and (< x free1)
                (<= free1 (expt 2 (+ -1 n)))
                (<= free2 x)
                (<= (- (expt 2 (+ -1 n))) free2)
                )
           (equal (signed-byte-p n x)
                  (and (integerp x)
                       (< 0 n)
                       (integerp n)
                       )))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P SIGNED-BYTE-P))))

(defthm signed-byte-p-from-bounds-free-four
  (implies (and (< x free1)
                (<= free1 (expt 2 (+ -1 n)))
                (< free2 x)
                (<= (+ -1 (- (expt 2 (+ -1 n)))) free2) ;do we really want the -1 here?
                )
           (equal (signed-byte-p n x)
                  (and (integerp x)
                       (< 0 n)
                       (integerp n)
                       )))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P SIGNED-BYTE-P))))




;old versions:
(defthmd sb-free-backchain
  (implies (and (<= x k)
                (<= k (1- (expt 2 (1- n))))
                (<= m x)
                (equal m (- (expt 2 (1- n)))) ;this is strange
                (integerp n)
                (< 0 n)
                (integerp x)
                )
           (signed-byte-p n x))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P
                                     SIGNED-BYTE-P))))

(defthmd sb-free-backchain1
  (implies (and (< x k)
                (<= k (1- (expt 2 (1- n))))
                (<= m x)
                (equal m (- (expt 2 (1- n))))
                (integerp n)
                (< 0 n)
                (integerp x)
                )
           (signed-byte-p n x))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P
                                     SIGNED-BYTE-P))))


;(def-axiom *axiom*-usbp-over-ash
;  (implies (and (integerp v)
;                (integerp n)
;                (integerp m)
;                (< 0 m)
;                (< n m)
;                (unsigned-byte-p (- m n) v))
;           (unsigned-byte-p m (ash v n))))


;; from IHS library, where it is a local thm that depends   <-- out-of-date comment?
;; on an axiom.  We prove it here.
(defthm unsigned-byte-p-logapp-better
  (implies (and (<= size1 size)
                (<= 0 j) ;bzo drop?
                (INTEGERP SIZE1)
                (<= 0 SIZE1)
                )
           (equal (unsigned-byte-p size (logapp size1 i j))
                  (and (integerp size)
                       (<= 0 size)
                       (if (integerp j)
                           (unsigned-byte-p (- size size1) j)
                         t))))
  :otf-flg t
  :hints (("Goal" :use ((:instance unsigned-byte-p-logapp (j (ifix j)))
                        )
           :in-theory (e/d (FALSIFY-UNSIGNED-BYTE-P)
                           ( unsigned-byte-p-logapp)))))

(in-theory (disable unsigned-byte-p-logapp))

(defthm ash-<=-to-sbp
  (implies (and (signed-byte-p (- 32 N) V)
                (integerp v)
                (integerp n)
                )
           (and (<= (ASH V N) 2147483647)
                (<= -2147483648 (ASH V N))))
  :hints (("goal"

           :in-theory (disable ASH-AS-LOGTAIL
                               signed-byte-p-ash
                               )
           :use ((:instance signed-byte-p-ash (x v) (n 32) (m n))))))

;(defthm logext-of-ash
;  (implies (and (integerp n)
;                (integerp m)
;                (integerp v)
;                (< m n)
;                (< 0 n)
;                )
;           (equal (logext n (ash v m))
;                  (ash (logext (- n m) v) m))))

;bzo improve this?
;move this
;shouldn't have had to disable so much?
(defthm logext-bounds-2
  (implies (< 0 n) ;drop?
           (and (<  (logext n val) (expt 2 (1- n)))
                (<= (- (expt 2 (1- n))) (logext n val))))
  :rule-classes (:rewrite (:linear
                           :trigger-terms ((logext n val))))
  :hints (("goal" :use ((:instance signed-byte-p-logext (size1 n) (size n) (i val)))
           :in-theory (e/d (integer-range-p
                            signed-byte-p)
                           (signed-byte-p-of-logext
                            SIGNED-BYTE-P-LOGEXT-BETTER
                            LOGEXT-BOUND
                            signed-byte-p-logext)))))


;; ;gross
;; ;trying disabled
;; (defthmd logior-fact
;;   (implies (and (unsigned-byte-p 24 a)
;;                 (unsigned-byte-p 24 b)
;;                 )
;;            (<= (logior a b) 16777215))
;;   :hints (("goal" :in-theory (e/d (unsigned-byte-p) (unsigned-byte-p-logior))
;;            :use (:instance unsigned-byte-p-logior (i a) (j b) (size 24)))))

;; ;gross
;; ;trying disabled
;; (defthmd nother-fact
;;   (implies (and (unsigned-byte-p 15 a)
;;                 (unsigned-byte-p 24 b))
;;            (<= (LOGIOR a b) 16777215))
;;   :hints (("goal" :in-theory (e/d (unsigned-byte-p integer-range-p) (unsigned-byte-p-logior))
;;            :use logior-fact)))

;trying disabled
;bzo drop or move?
(defthmd bitp-signed-byte-p-32
  (implies (bitp x)
           (signed-byte-p 32 x))
; Added by Matt K. April 2016 upon addition of type-set bit for {1}.
; (Bitp$inline was formerly already disabled here.)
  :hints (("Goal" :in-theory (enable bitp))))


(encapsulate
 ()

 (local
  (defthm negative-bound-loghead-rewrite
    (implies (and (integerp x)
                  (< x 0)
                  (< (- (expt 2 32)) x))
             (equal (loghead 32 x) (+ x (expt 2 32))))
    :hints (("goal" :in-theory (enable loghead)))))

 (local
  (defthm positive-bound-loghead-rewrite
    (implies (and (integerp x)
                  (<= 0 x)
                  (< x (expt 2 32)))
             (equal (loghead 32 x) x))
    :hints (("goal" :in-theory (enable loghead)))))

;make a similar rule to loghead-equal-rewrite-constant-case?
 (defthm loghead-non-zero-type
   (implies (and (integerp den)
                 (<= den (1- (expt 2 31)))
                 (<= (- (expt 2 31)) den)
                 (not (equal den 0)))
            (< 0 (loghead 32 den)))
   :hints (("goal" :cases ((< den 0)))))
 )

;bzo - why was this necessary in 2.9.2?
(local (include-book "rtl/rel9/arithmetic/expo" :dir :system)) ; rel8 -> rel9, MattK, 10/2013
(local (in-theory (disable expo-shift-general))) ;was looping!


;move
(defthm unsigned-byte-p-of-logcar
  (equal (unsigned-byte-p n (logcar x))
         (and (integerp n)
              (if (< 0 n)
                  t
                (if (< n 0)
                    nil
                  (equal 0 (logcar x))
                  ))))
  :hints (("Goal" :in-theory (enable expt-less-1 ;enable this elsewhere
                                     unsigned-byte-p
                                     integer-range-p))))

;move
(defthm signed-byte-p-of-logcar
  (equal (signed-byte-p n (logcar x))
         (if (equal n 1)
             (equal (logcar x) 0)
           (and (integerp n)
                (< 0 n))))
  :hints (("Goal" :in-theory (enable <-1-EXPT
                                     logcar
                                     signed-byte-p
                                     integer-range-p))))





;i made this rule go the other way, but it looped with SIGN-LOGEXT-AS-LOGBITP
;consider making that rule go the other way?
(defthm logbitp-test-of-top-bit
  (implies (and (signed-byte-p (+ 1 n) y)
                (integerp n))
           (equal (< y 0)
                  (logbitp n y)
                  ))
  :hints (("Goal" :in-theory (enable signed-byte-p logbitp))))

(defthm logbitp-test-of-top-bit-alt
  (implies (and (signed-byte-p (+ 1 n) y)
                (integerp n))
           (equal (< 0 y)
                  (and (not (logbitp n y))
                       (not (equal 0 y)))
                  ))
  :hints (("Goal" :in-theory (enable signed-byte-p logbitp))))






;loops with LOGCDR-LOGHEAD
(defthmd loghead-logcdr
  (equal (loghead n (logcdr x))
         (if (and (integerp n) (<= 0 n))
             (logcdr (loghead (+ 1 n) x))
           0)))

(defthm logbitp-+-loghead-simple
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n1)
                (< n1 n2))
           (equal (logbitp n1 (+ x (loghead n2 y)))
                  (logbitp n1 (+ x y)))))





;Rules like signed-byte-p-when-subtracting-big-power-of-2 came from an attempt to stay in the world of signed-byte-p and unsigned-byte-p without
;appealing to the arithmetic properties of those functions.

(defthm signed-byte-p-when-subtracting-big-power-of-2
  (equal (signed-byte-p n (+ (- (expt 2 (+ -1 n))) Y))
         (and (if (acl2-numberp y)
                  (unsigned-byte-p n y)
                t)
              (integerp n)
              (< 0 n)
              ))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     signed-byte-p))))

(defthm signed-byte-p-when-subtracting-big-power-of-2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (- (expt 2 (+ -1 n))))
                )
           (equal (signed-byte-p n (+ k Y))
                  (and (integerp n)
                       (< 0 n)
                       (if (acl2-numberp y)
                           (unsigned-byte-p n y)
                         t))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     signed-byte-p))))

(defthm signed-byte-p-when-adding-big-power-of-2
  (equal (signed-byte-p n (+ (expt 2 (+ -1 n)) y))
         (and (integerp n)
              (< 0 n)
              (if (acl2-numberp y)
                  (or (equal y (- (expt 2 n)))
                      (and (unsigned-byte-p n (- y))
                           (not (equal 0 y))))
                nil)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     signed-byte-p))))

(defthm signed-byte-p-when-adding-big-power-of-2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n))))
           (equal (signed-byte-p n (+ k y))
                  (and (integerp n)
                       (< 0 n)
                       (if (acl2-numberp y)
                           (or (equal y (- (expt 2 n)))
                               (and (unsigned-byte-p n (- y))
                                    (not (equal 0 y))))
                         nil))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     signed-byte-p))))


(defthm *ark*-logand-b-and
  (and (equal (logand (b-and x y) z)
              (b-and (b-and x y) (logcar z)))
       (equal (logand z (b-and x y))
              (b-and (b-and x y) (logcar z))))
  :hints (("goal" :in-theory (enable LOGAND-BIT-1))))

(defthm *ark*-logand-b-ior
  (and (equal (logand (b-ior x y) z)
              (b-and (b-ior x y) (logcar z)))
       (equal (logand z (b-ior x y))
              (b-and (b-ior x y) (logcar z))))
  :hints (("goal" :in-theory (enable LOGAND-BIT-1))))

(defthm *ark*-logand-b-xor
  (and (equal (logand (b-xor x y) z)
              (b-and (b-xor x y) (logcar z)))
       (equal (logand z (b-xor x y))
              (b-and (b-xor x y) (logcar z))))
  :hints (("goal" :in-theory (enable LOGAND-BIT-1))))

(defthm *ark*-logand-logcar
  (and (equal (logand (logcar x) y)
              (b-and (logcar x) (logcar y)))
       (equal (logand y (logcar x))
              (b-and (logcar x) (logcar y))))
  :hints (("goal" :in-theory (enable LOGAND-BIT-1))))

;improve this by not requiring (unsigned-byte-p 1 x)?
(defthm logxor-1
  (implies (unsigned-byte-p 1 x)
           (equal (logxor 1 x)
                  (b-not x)))
  :hints (("goal" :in-theory (enable logxor* b-not unsigned-byte-p))))

(defthm ifix-logxor
  (equal (ifix (logxor x y))
         (logxor x y)))

;think more about how we want to handle claims about bit vectors of length 1.  do we prefer to normalize all the claims to claims about 0, or do we
;want to leave  (equal (logcar x) 1) to get ACL2 to substitute 1 for (logcar x)? -ews
;eric saw something similar to this at AMD.
(defthm equal-logcar-1
  (equal (equal (logcar x) 1)
         (not (equal (logcar x) 0)))
  :hints (("goal" :in-theory (enable))))



;or just say logcar does nothing when applied to a single bit?
(defthm logcar-of-b-xor
  (equal (logcar (b-xor x y))
         (b-xor x y))
  :hints (("goal" :in-theory (enable b-xor))))

;or just say logcar does nothing when applied to a single bit?
(defthm logcar-of-b-and
  (equal (logcar (b-and x y))
         (b-and x y))
  :hints (("goal" :in-theory (enable b-and))))







(defthm logext-bound-2
  (and (<= (- (expt 2 31)) (logext 32 x))
       (<= (logext 32 x) (1- (expt 2 31))))
  :hints (("goal" :in-theory (disable SIGNED-BYTE-P-OF-LOGEXT
                                      signed-byte-p-logext-better
                                      signed-byte-p-logext
                                      )
           :use ((:instance signed-byte-p-logext (i x) (size1 32) (size 32)))))
  :rule-classes (:linear))

(defthm logext-bound-rewrite-1
  (<= -2147483648 (logext 32 x)))

(defthm logext-bound-rewrite-2
  (<= (logext 32 x) 2147483647))

;make a rewrite rule too?
(defthm logext-bound-upper
  (implies (and (<= 0 x)
                (integerp x)
                (integerp n)
                (< 0 n))
           (<= (logext n x) x))
  :rule-classes :linear
  :hints (("goal" :in-theory (e/d (SIGNED-BYTE-P) (logext-identity
                                                   logext-does-nothing-rewrite
                                                   signed-byte-p-logext
                                                   SIGNED-BYTE-P-OF-LOGEXT
                                                   SIGNED-BYTE-P-LOGEXT-BETTER))
           :use ((:instance logext-identity (size n) (i x))
                 (:instance SIGNED-BYTE-P-LOGEXT (size1 n) (size n) (i x))))))


;bzo trying to prove this from scratch may point out more lemmas to be generalized
(defthm logbitp-loghead-better
  (equal (logbitp pos (loghead size i))
         (if (< (nfix pos) (ifix size))
             (logbitp (nfix pos) i)
             nil))
  :hints (("Goal" :use (:instance logbitp-loghead)
           :in-theory (e/d () ( logbitp-loghead)))))

(in-theory (disable logbitp-loghead))

(defthm logbit-loghead-better
  (equal (logbit pos (loghead size i))
         (if (< (nfix pos) (ifix size))
             (logbit (nfix pos) i)
           0))
  :hints (("Goal" :use (:instance logbit-loghead (pos (nfix pos)))
           :in-theory (disable logbit-loghead))))

(in-theory (disable LOGBIT-LOGHEAD))  ;we have LOGBIT-LOGHEAD-better

;this is a strange way to write a rule...
;; (defthmd b-and-constant
;;   (implies (and (not (equal x k))
;;                 (syntaxp (quotep k))
;;                 (equal k 0)
;;                 (unsigned-byte-p 1 x)
;;                 (unsigned-byte-p 1 y))
;;            (and (equal (b-and x y)
;;                        y)
;;                 (equal (b-and y x)
;;                        y)))
;;   :hints (("goal" :in-theory (enable b-and unsigned-byte-p))))



;;;




(defthm logcar-logapp-better
  (equal (logcar (logapp size i j))
         (if (and (< 0 size)
                  (integerp size))
             (logcar i)
           (logcar j)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logapp))))

(in-theory (disable logcar-logapp))

(defthm logbitp-logapp-better
  (equal (logbitp pos (logapp size i j))
         (if (< (nfix pos) (nfix size))
             (logbitp (nfix pos) i)
           (logbitp (- (nfix pos) (nfix size)) j)))
;  :hints (("Goal" :in-theory (enable logapp)))
  :hints (("Goal" :use (:instance logbitp-logapp (pos (nfix pos)) (i (ifix i)) (j (ifix j)))
           :in-theory (e/d () ( logbitp-logapp)))))




;bzo mostly subsumed by logext-of-logext?
(defthm logext-of-logext-same
  (equal (logext size (logext size i))
         (logext size i))
  :hints (("Goal" :in-theory (e/d (logext)
                                  (EQUAL-LOGAPP-X-Y-Z
                                   EQUAL-LOGAPP-X-Y-Z-CONSTANTS
                                   ;;LOGHEAD-LOGAPP
                                   )))))



(defthm logext-+-logext-better-alt
  (equal (logext size (+ (logext size j) i))
         (logext size (+ (ifix j) i)))
  :hints (("Goal" :use (:instance  logext-+-logext-better)
           :in-theory (disable  logext-+-logext-better))))






(defthm logbitp-of-product-with-2
  (implies (integerp x) ;drop?
           (equal (logbitp n (* 2 x))
                  (and (logbitp (nfix (+ -1 n)) x)
                       (integerp n)
                       (< 0 n))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable FLOOR-NORMALIZES-TO-HAVE-J-BE-1 EXPONENTS-ADD-UNRESTRICTED logbitp))))

(defthm logbitp-of-product-with-1/2
  (implies (integerp x) ;drop
           (equal (logbitp n (* 1/2 x))
                  (if (evenp x)
                      (logbitp (+ 1 (nfix n)) x)
                    nil ;if x is odd, x/2 isn't an int and so logbitp treats it as 0
                  )))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (FLOOR-NORMALIZES-TO-HAVE-J-BE-1 EXPONENTS-ADD-UNRESTRICTED logbitp) ()))))

(defthm logbitp-of-*-expt-2-special
  (implies (and (integerp x)
                (<= 0 n)
                )
           (equal (logbitp n (binary-* (expt 2 n) x))
                  (logbitp 0 x)
                  ))
  :hints (("Goal" :in-theory (e/d ( EXPONENTS-ADD-UNRESTRICTED unary-/-of-expt loghead expt-gather
                                                (:induction expt)
                                                zip
                                                )
                                  (expt-minus exponents-add))
           :do-not '(generalize eliminate-destructors))))

(defthm logbitp-of-*-expt-2-special-const
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (integerp x)
                (<= 0 n)
                )
           (equal (logbitp n (binary-* k x))
                  (logbitp 0 x)
                  ))
  :hints (("Goal" :use (:instance  logbitp-of-*-expt-2-special (n (expo k)))
           :in-theory (disable  logbitp-of-*-expt-2-special))))



;;; begin stuff from proofs-common/@logops-spoof.lisp

;Previously, we included books/ihs/@logops.  That book causes a *lot* of stuff to be disabled (and some stuff to
;be enabled).  We consider that book to be pathological because it disables almost everything in the world (by
;essentially doing (in-theory nil)).  We don't need the @logops book, but since removing it might have caused
;problems with lots of stuff suddenly being enabled, Eric created this book to do exactly the enabling and
;disabling that including @logops did.

;Feel free to edit this stuff  Some of these disables (e.g., ones for functions we never reason about) probably
;have no affect on subsequent proofs.

;stuff enabled or added by the @logops book:
(in-theory (enable
;            (:EXECUTABLE-COUNTERPART IMMEDIATE-FORCE-MODEP) ;trying without this...
;            (:INDUCTION EXPT) ;trying without this
            ))


;stuff disabled by the @logops book:
;bzo remove stuff from this!
(in-theory (disable
            (:FORWARD-CHAINING INTEGERP-*-MEANS)
            (:DEFINITION LOGENDP)
            (:DEFINITION B-MAJ)
            (:LINEAR LOGCDR-LOGEND-ACL2-COUNT)
            (:LINEAR LOGCDR-LOGEND-ACL2-COUNT-3)
            (:INDUCTION LOGLISTR--2)
            (:INDUCTION LOGLIST-FWD-R--2)
            (:INDUCTION LOGLIST-BWD-R--2)
            (:INDUCTION LOGLIST-LOGNOT-INDUCTION)
            (:DEFINITION LOGLIST-LOGLISTR)
            (:INDUCTION LOGLIST-LOGLISTR)
            (:INDUCTION LOGLIST-LOGHEAD)
            (:REWRITE B-XOR-B-NOT)
            (:REWRITE B-XOR-CONSTANT)
            (:REWRITE B-NOT-OPEN-0)
            (:REWRITE B-NOT-OPEN-1)
            (:REWRITE BFIX-B-FUNCTIONS)
            (:REWRITE COMMUTATIVITY2-OF-B-FUNCTIONS)
            (:REWRITE EQUAL-B-NOT-LOGCAR)
            (:REWRITE MOVE---TO-CONSTANT-IN-EQUAL)
            (:REWRITE INTEGERP-/)
            (:REWRITE INTEGERP-*-CONSTANT-MEANS-1)
            (:REWRITE EXPT-LESS-1)
            (:REWRITE <-1-EXPT)
            (:REWRITE INTEGERP-*-1/2*X*EXPT-BRIDGE)
            (:REWRITE INTEGERP-*-1/2*X*EXPT-BRIDGE2)
            (:REWRITE EQUAL-I+-*2)
            (:REWRITE EQUAL-I+-+-*2-*2)
            (:FORWARD-CHAINING UNSIGNED-BYTE-P-B-XOR)
            (:REWRITE UNSIGNED-BYTE-P-B-XOR)
            (:FORWARD-CHAINING UNSIGNED-BYTE-P-B-AND)
            (:REWRITE UNSIGNED-BYTE-P-B-AND)
            (:FORWARD-CHAINING UNSIGNED-BYTE-P-B-IOR)
            (:REWRITE UNSIGNED-BYTE-P-B-IOR)
;            (:REWRITE EQUAL-K-B-AND)
;            (:REWRITE EQUAL-K-B-IOR)
            (:FORWARD-CHAINING UNSIGNED-BYTE-P-LOGCAR)
            (:REWRITE UNSIGNED-BYTE-P-LOGCAR)
            (:REWRITE LOGCAR-IDENTITY)
;            (:REWRITE LOGCAR-LOGNOT)
;            (:REWRITE LOGCAR-LOGAND)
;            (:REWRITE LOGCAR-LOGIOR)
;            (:REWRITE LOGCAR--)
 ;           (:REWRITE LOGCAR-EXPT)
  ;          (:REWRITE LOGCAR-*-1/2-EXPT)
            (:REWRITE EQUAL-LOGCONS-0)
;            (:REWRITE LOGCAR-ASH-POS)
;            (:REWRITE LOGCAR-ASH-NEG)
;            (:REWRITE UNSIGNED-BYTE-P-LOGCDR-RW)
            (:FORWARD-CHAINING UNSIGNED-BYTE-P-LOGCDR-FC)
;            (:REWRITE SIGNED-BYTE-P-LOGCDR-RW)
            (:FORWARD-CHAINING SIGNED-BYTE-P-LOGCDR-FC)
            (:REWRITE LOGCDR-EVENP-*)
;            (:REWRITE LOGCDR-ASH)
            (:REWRITE LOGCDR-*-1/2-EXPT)
            (:REWRITE LOGCDR-EXPT)
            (:REWRITE LOGCDR---EXPT)
            (:REWRITE LOGCDR-+1)
            (:REWRITE LOGCDR-+3)
            (:REWRITE LOGCDR-+2)
            (:REWRITE LOGCDR-*-X-EXPT-BRIDGE)
            (:REWRITE LOGCDR---*2)
            (:REWRITE LOGCDR-BITOP)
            (:REWRITE LOGCDR--)
            (:REWRITE EQUAL-LOGCDR-CONSTANT-BRIDGE)
            (:REWRITE LOGCDR-+--1-EXPT)
            (:REWRITE UNSIGNED-BYTE-P-+-EASY)
            (:FORWARD-CHAINING UNSIGNED-BYTE-P-+-EASY-FC)
            (:REWRITE UNSIGNED-BYTE-P-+-BRIDGE2)
 ;           (:REWRITE SIGNED-BYTE-P-+)
;            (:REWRITE SIGNED-BYTE-P-UNSIGNED-BYTE-P)
;            (:REWRITE UNSIGNED-BYTE-P-SUBTYPE)
;            (:REWRITE SIGNED-BYTE-P-SUBTYPE)
            (:REWRITE SBP-BOUND) ;think about this...
            (:REWRITE SBP-BOUND-1)
            (:REWRITE UNSIGNED-BYTE-P-LOGCDR-BRIDGE5)
            (:FORWARD-CHAINING SIGNED-BYTE-P--1)
            (:REWRITE SIGNED-BYTE-P--2)
;            (:REWRITE UNSIGNED-BYTE-P-ASH-NEG)
 ;           (:REWRITE UNSIGNED-BYTE-P-ASH-POS)
            (:REWRITE UNSIGNED-BYTE-P-1+)
            (:REWRITE UNSIGNED-BYTE-P-+-BRIDGE)
            (:REWRITE SIGNED-BYTE-P-+----SIMPLE)
            (:REWRITE UNSIGNED-BYTE-P-+-EXPT---SIMPLE)
            (:REWRITE UNSIGNED-BYTE-P-+-EXPT---SIMPLE-REWRITE)
            (:REWRITE UNSIGNED-BYTE-P-LOGBIT)
            (:REWRITE UNSIGNED-BYTE-P-B-FUNCTIONS)
            (:REWRITE LOGAPP-LOGIOR)
            (:REWRITE LOGAPP-LOGAND)
            (:REWRITE LOGAPP-LOGNOT)
;            (:FORWARD-CHAINING UNSIGNED-BYTE-P-LOGHEAD-FC) ;when i uncomment this i get an error when certifying
            (:REWRITE LOGHEAD-*4)
            (:REWRITE LOGHEAD-+-LOGIOR)
            (:REWRITE EQUAL-LOGHEAD-ASH-POS)
            (:REWRITE LOGHEAD-+-LOGEXT)
            (:REWRITE EQUAL-LOGHEAD-ALMOST-0)
            (:REWRITE EQUAL-LOGHEAD-LOGNOT-ALL-ONES)
            (:REWRITE LOGHEAD-LOGNOT-IN-+)
            (:REWRITE EQUAL-LOGHEAD-0-SBP)
;            (:REWRITE EQUAL-LOGHEAD-+-SIMPLE)
            (:REWRITE EQUAL-LOGHEAD-0-SBP-V2)
            (:REWRITE LOGHEAD-NEG-LOGEXT)
            (:REWRITE LOGHEAD-LOGNOT-LOGHEAD)
            (:REWRITE LOGHEAD-LOGNOT-ASH-POS)
            (:REWRITE LOGHEAD-LOGNOT-LOGEXT)
            (:REWRITE LOGHEAD-LOGNOT-ASH-POS-LOGEXT)
            (:REWRITE LOGHEAD-ASH-NEG)
            (:REWRITE LOGHEAD-LOGAPP-2)
            (:REWRITE LOGTAIL-LOGIOR)
            (:REWRITE LOGTAIL-LOGAND)
            (:REWRITE LOGTAIL-LOGNOT)
            (:DEFINITION EXPT2*)
            (:REWRITE SIGNED-BYTE-P-LOGNOT)
            (:FORWARD-CHAINING SIGNED-BYTE-P-LOGNOT)
            (:REWRITE LOGNOT-LOGIOR)
            (:REWRITE LOGAND-LOGIOR-2)
            (:FORWARD-CHAINING SIGNED-BYTE-P-LOGAND)
            (:REWRITE MY-LOGEXTU-AS-LOGHEAD)
            (:REWRITE EQUAL-LOGAND-EXPT)
            (:REWRITE EQUAL-LOGAND-EXPT-REWRITE)
            (:REWRITE LOGAND---EXPT)
            (:REWRITE LOGAND---EXPT-REWRITE)
            (:REWRITE EQUAL-0-LOGAND-BIT)
            (:REWRITE EQUAL-BIT-LOGAND-BIT)
            (:REWRITE LOGAND-LOGAND-CONST)
            (:REWRITE EQUAL-LOGAND-ASH-0)
            (:REWRITE *ASH*-EQUAL-LOGAND-ASH-POS-0)
            (:REWRITE EQUAL-LOGAND---EXPT---EXPT)
            (:REWRITE LOGAND---EXPT-V2)
            (:REWRITE LOGAND---EXPT-REWRITE-V2)
            (:REWRITE EQUAL-LOGAND---EXPT-0)
            (:REWRITE EQUAL-LOGAND---EXPT-0-REWRITE)
            (:REWRITE LOGAND-ASSOCIATIVE)
            (:REWRITE LOGAND-DUPLICATE-1)
            (:FORWARD-CHAINING SIGNED-BYTE-P-LOGIOR)
            (:REWRITE LOGIOR-AS-B-IOR)
            (:REWRITE EQUAL-LOGIOR-SINGLE-BIT)
            (:REWRITE LOGIOR-LOGIOR-CONST)
            (:REWRITE EQUAL-LOGIOR-CONST-CONST)
            (:REWRITE LOGIOR-EXPT-ASH-LOGHEAD-BRIDGE-BRIDGE)
            (:REWRITE |+-LOGIOR-ASH|)
            (:REWRITE |+-LOGIOR-ASH-V2|)
            (:REWRITE LOGIOR-LOGNOT)
            (:REWRITE LOGOR-LOGNOT-1)
            (:REWRITE LOGNOT-LOGAND)
            (:REWRITE LOGNAND-REWRITE)
            (:REWRITE LOGNOR-REWRITE)
            (:REWRITE LOGEQV-REWRITE)
            (:REWRITE LOGXOR-REWRITE)
            (:REWRITE B-XOR-REWRITE)
            (:REWRITE B-EQV-REWRITE)
            (:REWRITE B-NOR-REWRITE)
            (:REWRITE B-NAND-REWRITE)
            (:REWRITE B-ANDC1-REWRITE)
            (:REWRITE B-ANDC2-REWRITE)
            (:REWRITE B-ORC1-REWRITE)
            (:REWRITE B-ORC2-REWRITE)
;            (:REWRITE ASSOCIATIVITY-OF-BIT-FUNCTIONS)
            (:REWRITE SIMPLIFY-BIT-FUNCTIONS-2)
            (:REWRITE B-AND-B-IOR)
;            (:REWRITE ASH-ASH-RIGHT-TO-ASH)
            (:REWRITE ASH--1)
            (:REWRITE LOGBITP-LOGEXT)
            (:REWRITE LOGBITP-+-LOGEXT)
            (:REWRITE TOP-BIT-MEANS-<)
            (:REWRITE LOGBITP-LOGIOR)
            (:REWRITE LOGBITP-LOGAND)
            (:REWRITE LOGBIT-LOGBITP-1)
            (:REWRITE LOGBIT-LOGBITP-2)
            (:REWRITE LOGBITP-ASH)
            (:REWRITE LOGBITP-N-UNSIGNED-BYTE-P-N)
            (:REWRITE LOGBITP-+-LOGHEAD)
            (:REWRITE LOGBITP-+-LOGEXT-BRIDGE)
            (:REWRITE LOGBITP---*2)
            (:REWRITE LOGBITP-+--1---*2)
            (:REWRITE LOGBITP--)
            (:REWRITE LOGBITP---LOGEXT)
            (:REWRITE LOGBITP-+---LOGEXT)
            (:REWRITE LOGBITP-+-+---LOGEXT)
            (:REWRITE NEGATE-AS-BITS-REVERSE)
            (:REWRITE NEGATE-AS-BITS-REVERSE-BRIDGE)
            (:REWRITE LOGBITP-+-EXPT-1-N-REWRITE)
            (:REWRITE LOGBITP-+-EXPT-N-REWRITE)
            (:REWRITE LOGBITP-+-TOO-BIG)
            (:REWRITE SIGN-BIT-DIFFERENCE-AS-<)
            (:REWRITE LOGBITP-+---EXPT)
            (:REWRITE LOGBITP-+---EXPT-REWRITE)
            (:REWRITE EXPT-BOUND-AS-LOGBITP)
            ;(:REWRITE LOGBIT-LOGIOR)
            ;(:REWRITE LOGBIT-LOGAND)
            ;(:REWRITE LOGBIT-LOGXOR)
;            (:REWRITE LOGBIT-ASH)
;            (:REWRITE LOGBIT-CARRY-SIMPLE)
            (:REWRITE LOGBIT-CARRY-+1)
            (:FORWARD-CHAINING SIGNED-BYTE-P-LOGEXT-FC)
            (:REWRITE LOGEXT-BOUND)
            (:REWRITE LOGHEAD-+-LOGIOR-ASH-LOGEXT-BRIDGE)
            (:REWRITE LOGEXT-OPEN-LOGBIT-SIGN-KNOWN)
            (:REWRITE ASH-PLUS-DOWNTO-1-OR-0)
            (:REWRITE ASH-EXPT-NEG)
            (:REWRITE ASH-TO-0)
            (:REWRITE ASH-PLUS-DOWNTO-1-OR-0-BRIDGE)
            (:REWRITE ASH-LOGEXT-DOWNTO-1-OR-0)
            (:REWRITE ASH-SBP-DOWNTO-1-OR-0-BRIDGE)
            (:REWRITE ASH--1-NEG)
            (:REWRITE EQUAL-ASH-EXPT-0-FACT)
            (:REWRITE EQUAL-ASH-EXPT-0-FACT-REWRITE)
            (:REWRITE ASH-SBP-DOWNTO-1-OR-0-BRIDGE2)
            (:REWRITE EQUAL-ASH-+---EXPT--1)
            (:REWRITE EQUAL-ASH-+---EXPT--1-REWRITE)
            (:REWRITE ASH-LOGEXT-NEG)
            (:REWRITE ASH-LOGAND)
            (:REWRITE ASH-AS-LOGBIT)
            (:REWRITE ASH-NEG-LOGNOT)
            (:REWRITE ASH-LOGAPP)
            (:REWRITE FLOOR-*-1/2-EXPT-2)
            (:REWRITE ASH-LOGCDR-1)
            (:REWRITE FLOOR-1-HELPER)
            (:REWRITE SIGN-+-LOGEXT-LOGEXT-AS-LOGBITP)
            (:REWRITE SIGN-LOGEXT-AS-LOGBITP)
            (:REWRITE EQUAL-BIT-1)
;            (:REWRITE LOGBITP-OF-BIT-BRIDGE)
            (:REWRITE UNSIGNED-BYTE-P-+-*4-BRIDGE)
            (:REWRITE EQUAL-NEGATION-SAME-SIGN)
            ))

;;;


;; begin stuff from guard-lemmas.lisp

;  Note: The IHS libraries contain many FORCED hyps, which sometimes
;  cause problems.  These FORCEes were inserted during the original
;  implementation of these books in an old version of ACL2.
;  Unfortunately we have never had the time to go back and get rid of
;  them.  The temporary solution is simply to disable forcing except
;  in cases where it is absolutely needed.

;(in-theory (disable (force))) ;bzo? trying without...



;;; The true-listp guard to nth and update-nth is used elswhere,
;;; There are two versions, which are identical except that our
;;; guard is that the index is in the list, not that the list is true.


;(defun replace-nth (n val list)
;  (declare (xargs :guard (and (integerp n) (<= 0 n)  (< n (len list)))
;                  :guard-hints (("goal" :in-theory (enable len)))))
;  (if (zp n) (cons val (cdr list)) (cons (car list) (replace-nth (1- n) val (cdr list)))))

;(defun pick (n list)
;  (declare (xargs :guard (and (integerp n) (>= n 0) (< n (len list)))
;                  :guard-hints (("goal" :in-theory (enable len)))))
;  (if (zp n)
;      (car list)
;      (pick (- n 1) (cdr list))))

;(defthm pick-replace-nth
;  (implies
;   (and (integerp n1) (integerp n2) (<= 0 n1) (<= 0 n2))
;   (equal (pick n1 (replace-nth n2 v l))
;          (if (= n1 n2) v (pick n1 l))))
;  :hints (("goal" :in-theory (enable len))))


;; Guard proof helpers

;; some lemmas that assist in the proof of the guards
;; for the JEM1 ALU demo
;where do we use this?
;; Changed after Version 6.1 by Matt Kaufmann to replace obsolete the-error by
;; the-check.
;; Removed 11/2021 by Matt Kaufmann with the addition of the-check to
;; guard-holcers.
;(defthm the-check-noop
;  (equal (the-check g y x)
;         x)
;  :hints (("goal" :in-theory (enable the-check))))

;this rule seems to be expensive
(defthm logand-bound
  (implies (and (signed-byte-p 32 x)
                (signed-byte-p 32 y))
           (and (<= (- (expt 2 31)) (LOGAND x y))
                (<= (logand x y) (1- (expt 2 31)))))
  :hints (("goal" :in-theory (disable SIGNED-BYTE-P-LOGAND signed-byte-p-logops)
           :use ((:instance signed-byte-p-logand (i x) (j y) (size 32)))))
  :rule-classes (:linear))

(defthm lognot-bound
  (implies (signed-byte-p 32 x)
           (and (<= (- (expt 2 31)) (LOGNOT x))
                (<= (lognot x) (1- (expt 2 31)))))
  :hints (("goal" :in-theory (disable SIGNED-BYTE-P-LOGnot signed-byte-p-logops)
           :use ((:instance signed-byte-p-lognot (i x) (size 32)))))
  :rule-classes (:linear))

(defthm logeqv-bound
  (implies (and (signed-byte-p 32 x)
                (signed-byte-p 32 y))
           (and (<= (- (expt 2 31)) (logeqv x y))
                (<= (logeqv x y) (1- (expt 2 31)))))
  :hints (("goal" :in-theory (disable signed-byte-p-logops)
           :use ((:instance signed-byte-p-logops (i x) (j y) (size 32)))))
  :rule-classes (:linear))

;bzo generalize some of these (search this file for 32)
(defthmd logior-bound
  (implies
   (and
    (signed-byte-p 32 x)
    (signed-byte-p 32 y))
   (and
    (<= (- (expt 2 31)) (LOGIOR x y))
    (<= (logior x y) (1- (expt 2 31)))))
  :hints (("goal" :in-theory (disable  signed-byte-p-logops)
           :use ((:instance signed-byte-p-logops (i x) (j y) (size 32)))))
  :rule-classes (:linear))

(defthm logxor-bound
  (implies
   (and
    (signed-byte-p 32 x)
    (signed-byte-p 32 y))
   (and
    (<= (- (expt 2 31)) (LOGXOR x y))
    (<= (logxor x y) (1- (expt 2 31)))))
  :hints (("goal" :in-theory (disable  signed-byte-p-logops)
           :use ((:instance signed-byte-p-logops (i x) (j y) (size 32)))))
  :rule-classes :linear)

;why not rewrite to b-xor in this case?
(defthm logxor-bit-bound
  (implies
    (and (unsigned-byte-p 1 x) (unsigned-byte-p 1 y))
  (and
   (<= 0 (logxor x y))
   (<= (logxor x y) 1)))
  :hints (("goal" :in-theory (disable UNSIGNED-BYTE-P-LOGXOR)
           :use ((:instance unsigned-byte-p-logxor (i x) (j y) (size 1)))))
  :rule-classes :linear)





;why not just rewrite to b-or in this case?
(defthmd logior-bound1
  (implies (and (unsigned-byte-p 1 i)
                (unsigned-byte-p 1 j))
           (<= (logior i j) 1))
  :hints (("goal" :use ((:instance UNSIGNED-BYTE-P-LOGIOR (i i) (j j) (size 1)))
           :in-theory (disable UNSIGNED-BYTE-P-LOGIOR)))
  :rule-classes (:rewrite :linear))


;ungeneral?
(DEFTHM LOGAND-BOUND-rewrite-1
  (IMPLIES (AND (SIGNED-BYTE-P 32 X)
                (SIGNED-BYTE-P 32 Y))
           (<= -2147483648 (LOGAND X Y))))

;ungeneral?
(DEFTHM LOGAND-BOUND-rewrite-2
  (IMPLIES (AND (SIGNED-BYTE-P 32 X)
                (SIGNED-BYTE-P 32 Y))
           (<= (LOGAND X Y) 2147483647)))


;The out rules in the next series may not handle all these cases,
;so it has been left it in this file, but commented out


;; (defthmd logior-bound-rewrite-1
;;   (implies (and (signed-byte-p 32 x)
;;                 (signed-byte-p 32 y))
;;            (<= -2147483648 (logior x y)))
;;   :hints (("Goal" :in-theory (enable logior-bound))))

;; (DEFTHMd LOGIOR-BOUND-rewrite-1a
;;   (IMPLIES (AND (SIGNED-BYTE-P 32 X)
;;                 (SIGNED-BYTE-P 32 Y))
;;            (< -2147483649 (LOGIOR X Y)))
;;   :hints (("Goal" :in-theory (enable logior-bound))))

;; (DEFTHMd LOGIOR-BOUND-rewrite-2
;;   (IMPLIES (AND (SIGNED-BYTE-P 32 X)
;;                 (SIGNED-BYTE-P 32 Y))
;;            (<= (LOGIOR X Y) 2147483647))
;;   :hints (("Goal" :in-theory (enable logior-bound))))

;; (DEFTHMd LOGIOR-BOUND-rewrite-2a
;;   (IMPLIES (AND (SIGNED-BYTE-P 32 X)
;;                 (SIGNED-BYTE-P 32 Y))
;;            (< (LOGIOR X Y) 2147483648))
;;     :hints (("Goal" :in-theory (enable logior-bound))))

;; ;make this an equal rule?
;; (DEFTHMd LOGIOR-BOUND-rewrite-4
;;   (IMPLIES (AND (unSIGNED-BYTE-P 16 x)
;;                 (unSIGNED-BYTE-P 16 y))
;;            (<= (LOGIOR X Y) 65535))
;;   :hints (("goal" :use ((:instance UNSIGNED-BYTE-P-LOGIOR (i x) (j y) (size 16)))
;;            :in-theory (disable UNSIGNED-BYTE-P-LOGIOR))))

;; (DEFTHMd LOGIOR-BOUND-rewrite-5
;;   (IMPLIES (AND (unSIGNED-BYTE-P 4 x)
;;                 (unSIGNED-BYTE-P 4 y))
;;            (<= (LOGIOR X Y) 15))
;;   :hints (("goal" :use ((:instance UNSIGNED-BYTE-P-LOGIOR (i x) (j y) (size 4)))
;;            :in-theory (disable UNSIGNED-BYTE-P-LOGIOR))))

;; (defthmd logxor-bound-rewrite-1
;;   (implies (and (signed-byte-p 32 x)
;;                 (signed-byte-p 32 y))
;;            (<= -2147483648 (logxor x y))))

;; (defthmd logxor-bound-rewrite-2
;;   (implies (and (signed-byte-p 32 x)
;;                 (signed-byte-p 32 y))
;;            (<= (logxor x y) 2147483647)))



(defthmd ash--15-hack
  (implies (unsigned-byte-p 16 v)
           (<= (ash v -15) 1))
  :hints (("goal" :use (:instance ash-bound3a (s -15) (b 2) (x v))
           :in-theory (disable ash-bound3a))))

(defthmd ash--8-hack
  (implies (unsigned-byte-p 16 v)
           (<= (ash v -8) 255))
  :hints (("goal" :use (:instance ash-bound3a (s -8) (b 256) (x v))
           :in-theory (disable ash-bound3a))))

;(in-theory (enable INTEGERP-+-MINUS-*))

(defthmd logior-bound-rewrite-7
  (implies (and (unsigned-byte-p 8 x)
                (unsigned-byte-p 8 y))
           (<= (logior x y) 255))
  :hints (("goal" :use ((:instance unsigned-byte-p-logior (i x) (j y) (size 8)))
           :in-theory (disable unsigned-byte-p-logior))))

;;; begin stuff from ihs-new.lisp

;; BY: This book is rather fragile.  For example, it seems previously to have
;;     been certified with EXPT enabled, but it is currently disabled, so I
;;     had to deal with that throughout.


;drop?
(in-theory (enable append))


;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logcdr
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


(in-theory (enable logcdr-*-1/2-expt)) ;disable?

;bzo go back and remove the disables of these (and many more of the enabled rules in this file!) from @logops-spoof
(in-theory (enable logcdr-expt))
(in-theory (enable logcdr---expt))

(local (in-theory (enable open-logcons)))

;strange lemma name.
(defthmd *ark*-+*
  (implies (and (not (zip a))
                (not (equal a -1))
                (not (zip b)))
           (equal (+ a b)
                  (logcons
                   (b-xor (logcar a) (logcar b))
                   (+ (b-and (logcar a) (logcar b))
                      (logcdr a) (logcdr b)))))
  :hints (("goal" :induct (logcdr-logcdr-induction a b)
           ;:do-not '(generalize eliminate-destructors)
           :in-theory (e/d (LOGOPS-RECURSIVE-DEFINITIONS-THEORY b-and b-xor open-logcons)

; Modified April 2016 by Matt K. upon the addition of a type-set bit for the
; set {1}.  (Same change made in books/misc/mult.lisp.)

                           (BITP-COMPOUND-RECOGNIZER))
)))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; signed-byte-p, unsigned-byte-p
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;



(in-theory (enable unsigned-byte-p-+-easy))

;consider enabling SIGNED-BYTE-P-+

;should BACKCHAIN-SIGNED-BYTE-P-TO-UNSIGNED-BYTE-P be enabled?

;bzo clean this up
;generalize!
(defthmd *ark*-signed-byte-p-+-bridge
  (implies (and (unsigned-byte-p 16 x)
                (unsigned-byte-p 16 y))
           (signed-byte-p 32 (+ x y))))

(defthmd *ark*-signed-byte-p-31-23-bridge
  (implies (unsigned-byte-p 23 x)
           (signed-byte-p 31 (1+ x))))

(in-theory (enable UNSIGNED-BYTE-P-LOGCDR-BRIDGE5))

(defthmd signed-byte-p-32-bridge
  (implies (and (unsigned-byte-p 16 x)
                (unsigned-byte-p 16 y))
           (signed-byte-p 32 (+ 1 x y))))

(defthmd signed-byte-p-32-bridge2
  (implies (and (signed-byte-p 16 x)
                (signed-byte-p 16 y))
           (signed-byte-p 32 (+ x (- y))))
  :hints (("Goal" :in-theory (enable (:DEFINITION SIGNED-BYTE-P)))))


;kill?
(defthmd signed-byte-p-32-+-bridge
  (implies
   (and
    (unsigned-byte-p 16 y)
    (unsigned-byte-p 16 z))
   (signed-byte-p 32 (+ 65536 y (- z))))
  :hints (("Goal" :in-theory (enable (:DEFINITION SIGNED-BYTE-P)))))

(defthmd unsigned-byte-p-+--expt-17-bridge
  (implies (signed-byte-p 17 x)
           (not (unsigned-byte-p 16 (+ -65536 x))))
  :hints (("goal" :in-theory (enable unsigned-byte-p signed-byte-p))))


;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; loghead
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

;trying without this...
;; (defthm loghead-24-16-bridge
;;   (implies (unsigned-byte-p 16 x)
;;            (equal (loghead 24 x)
;;                   x)))

;Prove a bound on (loghead n x) perhaps?
(defthmd equal-loghead-7-65535
  (not (equal (loghead 7 x) 65535))
  :hints (("goal" :in-theory (enable loghead))))

(in-theory (enable loghead-*4))

(in-theory (enable loghead-+-logior))

(in-theory (enable equal-loghead-ash-pos))

;(in-theory (enable loghead-almost))

;drop?
(defthmd loghead-31-logcdr-bridge
  (implies (unsigned-byte-p 16 x)
           (equal (loghead 31 (logcdr x))
                  (logcdr x)))
  :hints (("goal" :in-theory (enable logcdr loghead unsigned-byte-p))))

(in-theory (enable loghead-+-logext))

(in-theory (enable equal-loghead-almost-0))


;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logand
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


;Non-standard way to write a rule!

(defthmd *ark*-logand-bit-constant
  (implies (and (not (equal x k))
                (syntaxp (quotep k))
                (equal k 0)
                (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y)
                (integerp y))
           (equal (logand x y)
                  y))
  :hints (("goal" :in-theory (enable logcons logand loghead unsigned-byte-p))))

(in-theory (enable ifix-logand))

(in-theory (enable equal-logand-expt))

(in-theory (enable equal-logand-expt-rewrite))

(in-theory (enable equal-0-logand-bit))

(in-theory (enable equal-bit-logand-bit))

;improve this theorem?
(in-theory (enable logand-logand-const))

(in-theory (enable logand-bfix))

(in-theory (enable equal-logand---expt---expt))

(in-theory (enable logior-as-b-ior))

(in-theory (enable EQUAL-LOGIOR-SINGLE-BIT))

;generalize this?
(in-theory (enable logior-logior-const))

(in-theory (enable equal-logior-const-const))

(in-theory (disable logior-expt-ash-loghead-bridge))

;(in-theory (enable logior-as-+)) ;drop?

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logxor
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

;do we really want to do this?
(in-theory (enable logxor-rewrite))


;drop? since we have logxor-rewrite?
(defthmd logior-logxor
  (implies (and (integerp x)
                (integerp y))
           (and (equal (logior z (logxor x y))
                       (logior z
                               (logior (logand x (lognot y))
                                       (logand (lognot x) y))
                               ))
                (equal (logior (logxor x y) z)
                       (logior (logior (logand x (lognot y))
                                       (logand (lognot x) y))
                               z))))
  :hints (("goal" :in-theory (enable logxor-rewrite))))


;drop? since we have logxor-rewrite?
(defthmd logxor-logior
  (implies
   (and
    (integerp x)
    (integerp y)
    (integerp z))
   (and
    (equal
     (logxor (logior x y) z)
     (logior (logand (logior x y) (lognot z))
             (logand (lognot (logior x y)) z)))
    (equal
     (logxor z (logior x y))
     (logior (logand (logior x y) (lognot z))
             (logand (lognot (logior x y)) z)))))
  :hints (("goal" :in-theory (enable logxor-rewrite))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; ash
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(in-theory (enable ifix-ash))

(in-theory (enable ash-as-logtail))  ;do we want this enabled or not?

;; added this one.
;drop?
(defthmd *ark*-fold-in-two-crock
  (implies (and (acl2-numberp x)
                (integerp m))
           (equal (* 2 x (expt 2 (+ -1 m)))
                  (* x (expt 2 m))))
  :hints (("Goal" :in-theory (enable expt))))

(defthm *ark*-ash-neg-of-unsigned-byte-p-bridge
  (implies (and (< n 0)
                (unsigned-byte-p (- n) x)
                (integerp n)
                )
           (equal (ash x n)
                  0)))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logbitp, logbit
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(in-theory (enable logbitp-logext))
(in-theory (enable logbitp-+-logext))
(in-theory (enable logbitp-+-simple))
(in-theory (enable logbitp-+-simple2))
(in-theory (enable logbitp-+-usb-v1))
(in-theory (enable logbitp-+-usb-v2))
(in-theory (enable logbitp-+-usb-v3))
(in-theory (enable logbitp-+-usb-v4))

;(in-theory (disable overflow-bits)) ;drop?

(in-theory (enable logbitp-logior))

(in-theory (enable logbitp-logand))

(in-theory (enable LOGBITP-ASH))

(in-theory (enable logbitp-+-logext-bridge))

(in-theory (enable logbit-ash))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; ash - part 2
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(in-theory (enable ash-plus-downto-1-or-0))

;; not wanted usually!
(defthmd *ark*-ash-pos-loghead-cheater
  (implies
   (and
    (integerp x)
    (integerp p)
    (<= 0 p)
    (integerp n)
    (< 0 n)
    (equal (logcar x) 0))
   (equal (ash (loghead n x) p)
          (ash (loghead (1- n) (logcdr x)) (1+ p))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY expt)
           :induct (sub1-induction p))))


(defthmd *ark*-ash-pos-loghead-cheater2
  (implies
   (and
    (integerp x)
    (integerp p)
    (<= 0 p)
    (integerp n)
    (< 0 n)
    (equal (logcar x) 1))
   (equal (ash (1+ (loghead n x)) p)
          (ash (1+ (loghead (1- n) (logcdr x))) (1+ p))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY expt expt2* EXPONENTS-ADD-UNRESTRICTED)
           :induct (sub1-induction p))))

(in-theory (enable ash-plus-downto-1-or-0-bridge))

(in-theory (enable ash-logext-downto-1-or-0))

(in-theory (enable ash-sbp-downto-1-or-0-bridge))

             ;; interesting.  Probably needed just for the FCP models? - what did this comment refer to?



(in-theory (enable ash-sbp-downto-1-or-0-bridge2))

(defthmd ash-logxor
  (implies
   (and
    (integerp x)
    (integerp y))
   (equal
    (ash (logxor x y) n)
    (ash (logior (logand x (lognot y))
                 (logand (lognot x) y))
         n)))
   :hints (("goal" :in-theory (enable logxor-rewrite))))

(defthm ash-logand-neg
  (implies (and (<= n 0) ;drop?
                (integerp x)
                (integerp y)
                (integerp n)
                )
           (equal (ash (logand x y) n)
                  (logand (ash x n) (ash y n))))
  :hints (("goal" :induct (add1-induction n)
           :in-theory (enable LOGTAIL-LOGAND))))


(encapsulate
 ()
 (local (defthm ash-leaves-one-bit-left-helper
          (implies (and (<= 0 n)
                        (unsigned-byte-p (1+ n) x)
                        (integerp n)
                        )
                   (equal (ash x (- n))
                          (logbit n x)))
          :rule-classes nil
          :hints (("goal" :induct (sub1-logcdr-induction n x)
                   :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY expt logbit)))))


 (defthm ash-leaves-one-bit-left
   (implies (and (<= n 0)
                 (unsigned-byte-p (1+ (- n)) x)
                 (integerp n)
                 )
            (equal (ash x n)
                   (logbit (- n) x)))
   :hints (("goal" :use (:instance ash-leaves-one-bit-left-helper (n (- n)))))))


;; NOTE:  The opposite direction of loghead-ash-pos!!
(defthm ash-neg-loghead
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (<= 0 n1)
                (< n2 0))
           (equal (ash (loghead n1 x) n2)
                  (if (<= n1 (- n2))
                      0
                    (loghead (+ n1 n2) (ash x n2)))))
  :hints (("goal" :induct (add1-sub1-logcdr-induction n2 n1 x)
           :in-theory (enable
                       max))))
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; floor
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(in-theory (enable floor-*-1/2-expt-2))

(in-theory (enable sign-+-logext-logext-as-logbitp))

(in-theory (enable sign-logext-as-logbitp))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; hacks
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

;(in-theory (disable single-bit-logops))

(in-theory (enable equal-negation-same-sign))

;move some hyps to the conclusion?
(defthm signed-byte-p-of-logtail
  (implies (and (integerp x)
                (integerp n2)
                (<= 0 n2)
                )
           (equal (signed-byte-p n1 (logtail n2 x))
                  (if (zp n1)
                      nil
                    (signed-byte-p (+ n1 n2) x))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :use (:instance logtail-lessp (pos n2) (i x) (j (/ (expt 2 n1) 2)))
           :do-not-induct t
           :in-theory (e/d (signed-byte-p
                              integerp-*-1/2-expt
                              exponents-add-unrestricted
;exponents-add
                              ) (MOVE-NEGATED-TERM-TO-OTHER-SIDE-OF-<-TERM-1-ON-RHS ;; ?
                                 )))))


;this is better than UNSIGNED-BYTE-P-LOGAND, so we disable that
;move this up the include-book hierarchy?
(defthm usbp-over-logand
  (implies (or (unsigned-byte-p m x)
               (unsigned-byte-p m y))
           (unsigned-byte-p m (logand x y)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p INTEGER-RANGE-P))))

(in-theory (disable UNSIGNED-BYTE-P-LOGAND))


(in-theory (disable LOGEXTU-AS-LOGHEAD))

;simplify rhs?
;consider the other case
(defthm loghead-of-logext
  (implies (<= final-size ext-size)
           (equal (loghead final-size (logext ext-size i))
                  (if (integerp ext-size)
                      (loghead final-size i)
                    (loghead final-size (logext 1 (logcar i)))
                    )))
  :hints (("Goal" :use (:instance logextu-as-loghead))))

;bzo move,
;generalize: rewrite a claim about signed-byte-p of a constant to a claim about the index.
(defthm signed-byte-p-of-1
  (equal (signed-byte-p n 1)
         (and (integerp n)
              (< 1 n)))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

;bzo we could need a rule like this for subtracting 2, subtracting 3, etc.
;(and the rules for those cases would get grosser) I bet that subtracting 1
;covers most of the cases we'll see in practice.this rule gives us a little
;flexibility around the ends of the unsigned-byte-p range without just
;opening up to arithmetic
(defthm unsigned-byte-p-of-one-less-than-x
  (implies (syntaxp (not (quotep x))) ;prevents loops (i think because acl2 unifies say, the constant 42 with the pattern (+ -1 x)
           (equal (unsigned-byte-p n (+ -1 x))
                  (and (integerp n)
                       (<= 0 n)
                       (or (equal x (expt 2 n))
                           (and (unsigned-byte-p n x)
                                (not (equal 0 x)))))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))



;generalize this
;trying disabled
(defthmd logior-unsigned-byte-p-16-one
  (implies (and (unsigned-byte-p 16 x)
                (unsigned-byte-p 16 y))
           (unsigned-byte-p 16 (logior x y))))

;trying disabled
(defthmd logior-unsigned-byte-p-16-two
  (implies (and (unsigned-byte-p 16 x)
                (unsigned-byte-p 16 y))
           (<= (logior x y) 65535))
  :hints (("Goal" :in-theory (disable UNSIGNED-BYTE-P-LOGIOR)
           :use (:instance logior-unsigned-byte-p-16-one))))

;bzo improve UNSIGNED-BYTE-P-LOGIOR

;bzo FLOOR-MINUS forces!

;I don't like how the RHS mentions loghead, but it seems like the easiet thing for now.  Maybe it should mention logext instead?
(defthm logext-minus
  (implies (acl2-numberp size)
           (equal (logext size (- i))
                  (if (equal 0 (loghead (+ -1 size) i)); (integerp (* i (/ (expt 2 (- size 1)))))
                      (logext size i)
                    (- (logext size i)))))
  :hints (("Goal" :in-theory (enable logext logapp loghead expt2 imod ifloor logbitp))))

;; (defthm plus-of-logapp-suck-in
;;   (implies (unsigned-byte-p 16 (+ x y))
;;            (equal (+ x (logapp 16 y j))
;;                   (if (unsigned-byte-p 16 y)
;;                       (logapp 16 (+ x y) j)
;;                     (+ (loghead 16 y) (- y) (logapp 16 (+ x y) j)) ;this seems strange
;;                     )))
;;   :hints (("Goal" :in-theory (enable logapp))))

;bzo might this loop with something?
;bzo move
;prove versions which have ash instead of logapp?
(defthm plus-of-logapp-suck-in
  (implies (unsigned-byte-p n (+ x y))
           (equal (+ x (logapp n y j))
                  (if (unsigned-byte-p n y)
                      (logapp n (+ x y) j)
                    (+ (loghead n y) (- y) (logapp n (+ x y) j)) ;this seems strange
                    )))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm plus-of-logapp-suck-in-alt
  (implies (unsigned-byte-p n (+ x z y))
           (equal (+ x z (logapp n y j))
                  (if (unsigned-byte-p n y)
                      (logapp n (+ x z y) j)
                    (+ (loghead n y) (- y) (logapp n (+ x z y) j)) ;this seems strange
                    )))
  :hints (("Goal" :use (:instance plus-of-logapp-suck-in (x (+ x z)))
           :in-theory (disable plus-of-logapp-suck-in))))


(defthm plus-minus-half-collect
  (implies (and (rationalp x)
                (rationalp y))
           (equal (+ (- (* 1/2 x))
                     (- (* 1/2 x))
                     y)
                  (+ (- x)
                     y))))

(encapsulate
 ()
 (local (defthm loghead-of-prod-of-logext-helper
          (implies (and (integerp i)
                        (integerp n)
                        (< 0 n))
                   (equal (loghead n (* i (logext n j)))
                          (loghead n (* i (ifix j)))))
          :hints (("Goal" ; :use (:instance  loghead-of-prod-lemma (x (logapp 31 a -1)) (y k))
                   :in-theory (e/d (logext
                                    EXPONENTS-ADD-UNRESTRICTED
                                    loghead logapp
                                    imod
                                    logbitp
                                    oddp
                                    evenp
                                    ifix
                                    mod-stretch-base
                                    mod-stretch-base-2
                                    )
                                   (loghead-of-prod-lemma
                                    mod-cancel
                                    evenp-collapse
                                    ))))))

 (defthm loghead-of-prod-of-logext
   (implies (integerp i)
            (equal (loghead n (* i (logext n j)))
                   (loghead n (* i (ifix j)))))
   :hints (("Goal" :use (:instance loghead-of-prod-of-logext-helper)
            :in-theory (disable loghead-of-prod-of-logext-helper)))))

(defthm logtail-of-loghead-becomes-logbit
  (implies (and (equal m (+ -1 n))
                (integerp n)
                (< 0 n)
                )
           (equal (logtail m (loghead n x))
                  (logbit m x)))
  :hints (("Goal" :in-theory (e/d (logtail-loghead-better)
                                  (loghead-logtail)))))

(defthm loghead-split
  (implies (and (integerp n)
                (< 0 n)
                )
           (equal (loghead n x)
                  (logapp (+ -1 n) (loghead (+ -1 n) x) (logbit (+ -1 n) x))))
  :rule-classes nil)


(encapsulate
 ()
 (local (defthm logapp-equal-logapp-rewrite-helper
          (implies (and (integerp size)
                        (<= 0 size)
                        )
                   (equal (equal (logapp size i j) (logapp size i2 j2))
                          (and (equal (ifix j) (ifix j2))
                               (equal (loghead size i)
                                      (loghead size i2)))))))


 (defthm logapp-equal-logapp-rewrite
   (equal (equal (logapp size i j) (logapp size i2 j2))
          (and (equal (ifix j) (ifix j2))
               (or (not (integerp size))
                   (< size 0)
                   (equal (loghead size i)
                          (loghead size i2)))))
   :hints (("Goal" :use (:instance  logapp-equal-logapp-rewrite-helper)
            :in-theory (disable logapp-equal-logapp-rewrite-helper
                                equal-logapp-x-y-z
                                equal-logapp-x-y-z-constants)))))

;has no ifix in the conclusion to cause case splits
(defthmd logapp-equal-logapp-rewrite-no-split
  (implies (and (integerp j)
                (integerp j2))
           (equal (equal (logapp size i j)
                         (logapp size i2 j2))
                  (and (equal j j2)
                       (or (not (integerp size))
                           (< size 0)
                           (equal (loghead size i)
                                  (loghead size i2))))))
  :hints (("Goal" :in-theory (enable logapp-equal-logapp-rewrite))))


(defthmd loghead-split-special
  (implies (and (syntaxp (equal x 'x))
                (integerp n)
                (< 0 n)
                )
           (equal (loghead n x)
                  (logapp (+ -1 n) (loghead (+ -1 n) x) (logbit (+ -1 n) x))))
 :hints (("Goal" :use (:instance  loghead-split))))

;kill the 16 version
;keep this disabled.
(defthmd equal-of-logheads-split
  (implies (and (integerp n)
                (< 0 n)
                )
           (equal (equal (loghead n x) (loghead n y))
                  (and (equal (loghead (+ -1 n) x) (loghead (+ -1 n) y))
                       (equal (logbit (+ -1 n) x) (logbit (+ -1 n) y))
                       )))
  :hints (("Goal" :in-theory (e/d (
                                   loghead-split-special
                       ) ()))))



(encapsulate
 ()
 (local (defthm equal-of-two-logexts-rewrite-helper
          (implies (integerp n)
                   (equal (equal (logext n a)
                                 (logext n b))
                          (if (< 0 n)
                              (equal (loghead n a)
                                     (loghead n b))
                            (equal (logcar a)
                                   (logcar b))
                            )))
          :hints (("Goal" :in-theory (e/d (logext
                                           loghead-split-special
                                           logbit
                                           equal-of-logheads-split)
                                          ())))))

;kill the 16 version
;allow the two logext calls to have different size parameters?
 (defthm equal-of-two-logexts-rewrite
   (equal (equal (logext n a)
                 (logext n b))
          (if (and (< 0 n)
                   (integerp n))
              (equal (loghead n a)
                     (loghead n b))
            (equal (logcar a)
                   (logcar b))))))


;use nary for stuff like this?
;; (defthm loghead-of-product-of-logext
;;   (implies (and (integerp i)
;;                 (integerp j)
;;                 )
;;            (equal (loghead size (* i (logext size j)))
;;                   (loghead size (* i j))))
;;   :hints (("Goal" :in-theory (disable META-RULE-ERIC
;;                                       LOGHEAD-IDENTITY
;;                                       LOGHEAD-DOES-NOTHING-REWRITE
;;                                       LOGHEAD-LOGHEAD-BETTER)
;;            :use ((:instance LOGHEAD-LOGHEAD-BETTER (size1 size) (size size) (i  (* i (logext size j))))
;;                  ;(:instance LOGHEAD-LOGHEAD-BETTER (size1 size) (size size) (i  (* i j)))
;;                  ))
;;           ))



;based on a theorem from robert krug
;long proof -try to extract some lemmas - maybe about floor?
;try enabling less stuff - might lead to nice lemmas
;prove this from a version about loghead?
(defthm logext-of-product-of-logext
  (implies (and (integerp i)
                (integerp j)
                )
           (equal (logext size (* i (logext size j)))
                  (logext size (* i j))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logext loghead logapp imod expt2 mod logbitp oddp) (evenp))))
  :otf-flg t)

(defthm logext-of-product-of-logext-alt
  (implies (and (integerp i)
                (integerp j)
                )
           (equal (logext size (* (logext size j) i))
                  (logext size (* i j)))))

(defthm ash-of-logtail-does-nothing-rewrite
  (equal (equal (ash (logtail n z) n) z)
         (and (integerp z)
              (if (<= 0 n)
                  (equal 0 (loghead n z))
                (equal (ash z n) z) ; bzo ;figure out what this should simplify to and prove a rule, then rephrase this rule
                )))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (floor-normalizes-to-have-j-be-1
                            logtail
                            loghead
                            ash)
                           ( ;(:type-prescription floor)
                            (:type-prescription floor)
                            )))))

;decide how to handle ash!  always open up?
(defthm logtail-of-ash
  (IMPLIES (<= 0 N)
           (EQUAL (LOGTAIL N (ASH Y N))
                  (ifix Y)
                  ))
  :hints (("Goal" :in-theory (enable logtail ash))))








;is this okay?
;more like this?
(defthm b-not-equal-0-rewrite
  (equal (equal 0 (b-not x))
         (equal 1 x))
  :hints (("Goal" :in-theory (enable b-not))))

(defthm b-not-equal-1-rewrite
  (equal (equal 1 (b-not x))
         (not (equal 1 x)))
  :hints (("Goal" :in-theory (enable b-not))))



;do we already have something like this (perhaps about any bitp being either 0 or 1)
(defthm unsigned-byte-p-1-choices
  (implies (unsigned-byte-p 1 b)
           (or (equal b 0)
               (equal b 1)))
  :rule-classes nil)




;; ;generalize!
;; (defthm loghead-of-prod-of-logext
;;   (implies (and (integerp i)
;;                 (natp size))
;;            (equal (loghead size (* i (logext size j)))
;;                   (loghead size (* i (ifix j)))))
;;   :hints (("Goal" ; :use (:instance  loghead-of-prod-lemma (x (logapp 31 a -1)) (y k))
;;            :in-theory (e/d (logext ;logapp
;;                             loghead logapp imod
;;                             logbitp
;;                             oddp
;;                             evenp
;;                             ifix
;;                             )
;;                            (loghead-of-prod-lemma
;;                             mod-cancel
;;                             evenp-collapse
;;                             )))))


;; (defthm loghead-of-prod-of-logext
;;   (implies (integerp i)
;;            (equal (loghead n (* i (logext n j)))
;;                   (loghead n (* i (ifix j)))))
;;   :hints (("Goal" ; :use (:instance  loghead-of-prod-lemma (x (logapp 31 a -1)) (y k))
;;            :in-theory (e/d (logext
;;                             loghead logapp
;;                             imod
;;                             logbitp
;;                             oddp
;;                             evenp
;;                             ifix
;;                             mod-stretch-base
;;                             mod-stretch-base-2
;;                             EXPONENTS-ADD-UNRESTRICTED
;;                             )
;;                            (loghead-of-prod-lemma
;;                             mod-cancel
;;                             evenp-collapse
;;                             )))))




(defthm logext-of-prod-of-loghead
  (implies (integerp i)
           (equal (logext 32 (* i (loghead 32 j)))
                  (logext 32 (* i (ifix j))))))

(in-theory (enable LOGHEAD-LOGAPP-2))



;bzo replace ash-logext-neg
;loops with LOGEXT-ASH
(defthmd ash-logext
  (implies (and (< 0 m)
                (integerp n)
                (integerp x)
                (integerp m)
                (< 0 n)

                (< 0 (+ n m)))
           (equal (ash (logext n x) m)
                  (logext (+ n m)
                          (ash x m))))
  :hints
  (("goal" :in-theory (enable lrdt))))

(defthm ash-plus-constant-suck-in
  (implies (and (unsigned-byte-p k a)
                (natp k)
                (integerp b))
           (equal (+ a (ASH b k))
                  (logapp k a b)))
  :hints (("Goal" :in-theory (e/d (ASH-AS-LOGAPP)
                                  (LOGAPP-0-PART-2-BETTER)))))


;(in-theory (disable imod ifloor))


(defthm <-of-logtail
  (implies (and (integerp size)
                (<= 0 size)
                (integerp b)
                ;(natp b)
                (integerp x) ;(natp x)
                )
           (equal (< B (LOGTAIL SIZE X))
                  (and (not (equal B (LOGTAIL SIZE X)))
                       (< (* b (expt 2 size)) x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable LOGTAIL IFLOOR eric2 eric1))))

;(in-theory (enable mod-cancel))

;bzo
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm logapp-<
  (implies (and (integerp size) ;(natp size)
                (integerp a) ;(natp a)
                (integerp b);(natp b)
                (integerp x)
                ;(<= 0 x)
                )
           (equal (< (logapp size a b) x)
                  (or (< b (logtail size x))
                      (and (equal b (logtail size x))
                           (< (loghead size a) (loghead size x))))))
  :hints (("Goal" ; :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (LOGAPP
                              imod ifloor
                              LOGTAIL
                              mod-cancel
                              loghead)
                           ()))))

;bzo clean up rhs?
(defthm logapp-<=
  (implies (and (integerp size) ;(natp size)
                (integerp a) ;(natp a)
                (integerp b) ;(natp b)
                (integerp x)
      ;(<= 0 x)
                )
           (equal (< x (logapp size a b))
                  (not (or (equal (logapp size a b) x)
                           (< b (logtail size x))
                           (and (equal b (logtail size x))
                                (< (loghead size a) (loghead size x)))))))
  :hints (("Goal" :use (:instance  logapp-<)
           :in-theory (disable EQUAL-LOGAPP-X-Y-Z
                               EQUAL-LOGAPP-X-Y-Z-CONSTANTS
                               logapp-<))))

;; (DEFTHM PLUS-OF-LOGAPP-SUCK-IN-gen
;;   (IMPLIES (and (UNSIGNED-BYTE-P k (+ X Y))
;;                 (natp k))
;;            (EQUAL (+ X (LOGAPP k Y J))
;;                   (IF (UNSIGNED-BYTE-P k Y)
;;                       (LOGAPP k (+ X Y) J)
;;                       (+ (LOGHEAD k Y)
;;                          (- Y)
;;                          (LOGAPP k (+ X Y) J)))))
;;   :HINTS
;;   (("Goal" :IN-THEORY (ENABLE LOGAPP))))



;prove without enabling ifloor?

(defthmd ash-logcdr-1-better
  (implies (integerp x)
           (equal (ASH (LOGCDR x) 1)
                  (if (evenp x)
                      x
                    (+ -1 x))))
  :hints (("Goal" :in-theory (enable ash logcdr ifloor))))

(in-theory (disable ash-logcdr-1))

(defthm logcdr-logapp
  (equal (logcdr (logapp size i j))
         (if (zp size)
             (logcdr j)
           (logapp (+ -1 size) (logcdr i) j)))
  :hints (("Goal" :in-theory (e/d (zp) ( logtail-logapp))
           :use (:instance logtail-logapp  (size1 (nfix size)) (i i) (j j) (size 1)))))

;decide whether we want facts about logbitp or logbit? i think we should use logbit, since maybe it can substitute?

(defthm hackyy
  (implies (rationalp i)
           (equal (< (* 32768 I) 65536)
                  (< i (/ 65536 32768)))))


;; ;bzo gen
;; ;bzo move
;; (defthm floor-hack
;;   (IMPLIES (AND (< X 65536)
;;                 (<= 0 X)
;;                 (INTEGERP X)
;;                 )
;;            (equal (FLOOR X 32768) ;FLOOR-BY-TWICE-HACK took a term out of the normal form
;;                   (if (< X 32768)
;;                       0
;;                     1))))


;; ;see lemma rtl1
;; (defthm floor-hack-gen
;;   (IMPLIES (AND (< X (expt 2 (+ 1 n)))
;;                 (integerp n)
;;                 (< 0 n)
;;                 (<= 0 X)
;;                 (INTEGERP X)
;;                 )
;;            (equal (FLOOR X (expt 2 n)) ;FLOOR-BY-TWICE-HACK took a term out of the normal form
;;                   (if (< X (expt 2 n))
;;                       0
;;                     1))))


;bzo trying with a backchain-limit, since the ungeneral version of this seemed expensive
(defthm usb-tighten
  (implies (and (not (logbitp (+ -1 n) x))
                (integerp n)
                (< 0 n))
           (equal (unsigned-byte-p n x)
                  (unsigned-byte-p (+ -1 n) x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p
                                   INTEGER-RANGE-P
                                   logbitp
                                   EXPONENTS-ADD-UNRESTRICTED ;shouldn't be needed?
                                   )
                                  (FLOOR-BY-TWICE-HACK)))))

;; (defthm usb-tighten
;;   (implies (not (logbitp 15 x))
;;            (equal (unsigned-byte-p 16 x)
;;                   (unsigned-byte-p 15 x)))
;;   :rule-classes ((:rewrite :backchain-limit-lst (0)))
;;   :hints (("Goal" :in-theory (e/d (unsigned-byte-p
;;                                      INTEGER-RANGE-P
;;                                      logbitp)
;;                                   (FLOOR-BY-TWICE-HACK)))))

;think more about this
;looped!
(defthmd loghead-when-know-top-bit
  (implies (and (equal (logbit m x) b) ;using m so that this will be sure to match
                (equal m (+ -1 n))
                (integerp n)
                (< 0 n)
                )
           (equal (loghead n x)
                  (logapp (+ -1 n) (loghead (+ -1 n) x) b)))
;  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil nil)))
  )

;; ;think about this
;; (defthm loghead-tighten
;;   (implies (and (equal (logbit 14 x) b)
;; ;                (integerp x);(natp x)
;; ;                (bitp b)
;;                 )
;;            (equal (loghead 15 x)
;;                   (logapp 14 (loghead 14 x) b)
;;                   )))

;do we really want this enabled?
;caused problems.  disabling.
(defthmd loghead-when-know-top-bit-two
  (implies (and (syntaxp (not (quotep x))) ;if x is a constant, don't use this rule (prevents loops)
                (logbitp (+ -1 n) x) ;will the (+ -1 n) here get computed when n is a constant?
                (integerp n)
                (< 0 n)
                )
           (equal (loghead n x)
                  (logapp (+ -1 n) (loghead (+ -1 n) x) 1)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil nil))))

;do we really want this enabled?
;caused problems.  disabling.
(defthmd loghead-when-know-top-bit-three
  (implies (and (syntaxp (not (quotep x))) ;if x is a constant, don't use this rule (prevents loops)
                (not (logbitp (+ -1 n) x)) ;will the (+ -1 n) here get computed when n is a constant?
                (integerp n)
                (< 0 n)
                )
           (equal (loghead n x)
                  (logapp (+ -1 n) (loghead (+ -1 n) x) 0)))
  :rule-classes ((:rewrite :backchain-limit-lst (nil 1 nil nil)))
  :hints (("Goal" :in-theory (enable loghead-when-know-top-bit))))

;Note the backchain limit.
(defthm logtail-leaves-single-bit
  (implies (and (unsigned-byte-p (+ 1 n) x)
                (integerp n)
                (<= 0 n))
           (equal (logtail n x)
                  (logbit n x)))
  :rule-classes ((:rewrite :backchain-limit-lst (1 nil nil)))
  :hints (("Goal" :in-theory (enable logtail logbit unsigned-byte-p integer-range-p logbitp ifloor))))

;gen
(defthm ash-suck-in-special
  (implies (integerp x)
           (equal (+ 3 (ash x 1))
                  (+ 1 (ash (+ 1 x) 1))))
  :hints (("Goal" :in-theory (enable ash ifix))))

;trying disabled, since this causes a case split ...
(defthmd unsigned-byte-p-of-one-more-than-x
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (acl2-numberp x)
                (natp n))
           (equal (unsigned-byte-p n (+ 1 x))
                  (or (equal x -1)
                      (and (unsigned-byte-p n x)
                           (not (equal x (+ -1 (expt 2 n))))))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     integer-range-p))))



(defthm logtail-shift-16
  (implies (integerp x)
           (equal (logtail 16 (* 65536 x))
                  x))
  :hints (("Goal" :in-theory (enable logtail ifloor))))


(defthm evenp-of-mod
  (implies (evenp y) ;handle other case (that is, the case when y is an odd integer)?
           (equal (evenp (mod x y))
                  (evenp x)
                  ))
  :hints (("Goal" :cases ((integerp y))
           :in-theory (e/d (mod)))))

;generalize to handle addends other than 1 with corresponding predicates (like "multiple of 4" than even)?
;prove without using elimination?
;bzo gen
;; (defthm logtail-of-one-more-when-even
;;   (implies (and (evenp x)
;;                 (integerp n)
;;                 (<= 0 n)
;;                 )
;;            (equal (logtail n (+ 1 x))
;;                   (logtail n x)))
;;   :hints (("Goal" :in-theory (e/d (logtail ifloor ifix) (FLOOR-BY-TWICE-HACK)))))

(defthm logtail-of-one-more-when-even
  (implies (and (evenp x)
;                (integerp n)
 ;               (<= 0 n)
                )
           (equal (logtail 16 (+ 1 x))
                  (logtail 16 x)))
  :hints (("Goal" :in-theory (e/d (logtail ifloor ifix) (FLOOR-BY-TWICE-HACK)))))

;loops with defn logapp!
(defthmd sum-with-shift-becomes-logapp
  (implies (and (unsigned-byte-p k a)
                (natp k)
                (integerp b))
           (equal (+ a (* (expt 2 k) b))
                  (logapp k a b)))
  :hints (("Goal" :in-theory (e/d (ash)( ASH-PLUS-CONSTANT-SUCK-IN
                                         EQUAL-LOGAPP-X-Y-Z))
           :use (:instance ash-plus-constant-suck-in))))

;loops with defn logapp!
(defthmd sum-with-shift-becomes-logapp-constant-version
  (implies (and (syntaxp (quotep j))
                (power2p j)
                (<= 0 j)
                (unsigned-byte-p (expo j) a)
                (integerp b)
                )
           (equal (+ a (* j b))
                  (logapp (expo j) a b)))
  :hints (("Goal" :in-theory (e/d (ash ;POWER2P
                                       )
                                  (FLOOR-BY-TWICE-HACK sum-with-shift-becomes-logapp
                                                       EXPO-COMPARISON-REWRITE-TO-BOUND
                                                       EXPO-COMPARISON-REWRITE-TO-BOUND-2))
           :use (:instance sum-with-shift-becomes-logapp (k (expo j))))))

(defthm loghead-plus-ash
  (implies (integerp i)
           (equal (loghead n (+ i (ash b n)))
                  (loghead n i)))
  :hints (("Goal" :in-theory (e/d (loghead imod ash) (mod-cancel)))))


;weird rule?
;gen?
(defthm logapp-linear
  (implies (and (unsigned-byte-p 16 i)
                (unsigned-byte-p 16 j))
           (equal (logapp 16 i b)
                  (+ (logapp 16 j b) (- j) i)))
  :rule-classes :linear)

;disable?
;add quotep hyp?
(defthm signed-byte-p-of-one-less-than-x
  (implies (integerp x)
           (equal (signed-byte-p n (+ -1 x))
                  (and (integerp n)
                       (< 0 n)
                       (or (equal x (expt 2 (+ -1 n)))
                           (and (signed-byte-p n x)
                           (not (equal x (- (expt 2 (+ -1 n))))))))))
  :hints (("Goal" :in-theory (enable signed-byte-p
                                     integer-range-p ;prove a rule for integer-range-p of (+ 1 x)
                                     ))))



(defthm logbitp-of-one-less-case-1
  (implies (and (equal (loghead n x) 0)
                (integerp x);(natp x)
;                (integerp n);(natp n)
                )
           (equal (logbitp n (+ -1 x))
                  (not (logbitp n x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logbitp loghead ;floor
                                    imod
    ;oddp evenp expt
                                    )
                           (evenp-collapse)))))

;wow! generalization actually worked!
(defthm floor-of-minus-1-case-1
  (implies (and (not (integerp (* x (/ k))))
                (integerp x)
;                (<= 0 x)
                (integerp k)
                (<= 0 k)
                )
           (equal (floor (+ -1 x) k)
                  (floor x k))))

(defthm logbitp-of-one-less-case-2
  (implies (and (not (equal (loghead n x) 0))
                (integerp x) ;(natp x)
;                (natp n)
                )
           (equal (logbitp n (+ -1 x))
                  (logbitp n x)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logbitp loghead ;floor
                                    imod
    ;oddp evenp expt
                                    )
                           (evenp-collapse)))))

(defthm logbitp-of-one-less
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (integerp x))
           (equal (LOGBITP n (+ -1 X))
                  (if (equal (loghead n x) 0)
                      (not (LOGBITP n X))
                    (LOGBITP n X))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (LOGBITP LOGHEAD ;floor
                                    imod
;oddp EVENP expt
                                    )
                           (EVENP-COLLAPSE)))))

;(in-theory (disable MOD-CANCEL))

(local (in-theory (enable imod ifloor)))

(defthm logtail-of-one-less-than-x
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (integerp x)
                (<= 0 n))
           (equal (logtail n (+ -1 x))
                  (if (equal (loghead n x) 0)
                      (+ -1 (logtail n x))
                    (logtail n x))))
  :hints (("Goal" :in-theory (enable logtail
                                     loghead
                                     UNSIGNED-BYTE-P
                                     INTEGER-RANGE-P ;prove a rule for integer-range-p of (+ 1 x)
                                     ))))

;bzo gen!
;replace other version? huh?

(defthmd logext-of-one-less-than-x
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (integerp x)
;(signed-byte-p 32 x) ;drop
                )
           (equal (logext 32 (+ -1 x))
                  (if (equal (logext 32 x) (- (expt 2 31)))
                      2147483647
                    (+ -1 (logext 32 x)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable logext
                                     UNSIGNED-BYTE-P
                                     INTEGER-RANGE-P ;prove a rule for integer-range-p of (+ 1 x)
                                     ))))


;(in-theory (disable helper-4))






(DEFTHMd EQUAL-+-HACK-gen
  (IMPLIES (AND ;(rationalp x) ;(INTEGERP X)
     ;(rationalp y) ;(INTEGERP Y)
     ;(rationalp z) ;(INTEGERP Z)
     ;(SYNTAXP (QUOTEP X))
     ;(SYNTAXP (QUOTEP Y))
            (acl2-numberp n)
            )
           (EQUAL (EQUAL 3 (+ (- J) N))
                  (EQUAL (+ 3 j) N))))






;(include-book "arithmetic-3/bind-free/top" :dir :system) looped!

(DEFTHM EQUAL-CONSTANT-+-blah
  (IMPLIES (AND (syntaxp (QUOTEP C1))
                (syntaxp (QUOTEP C2))
                (rationalp x)
                (rationalp c1)
                (rationalp c2)
                (rationalp y)
                )
           (EQUAL (EQUAL (+ C1 X) (+ C2 y))
                  (EQUAL (+ X (- C1 C2)) y))))


(defthm hacky
 (implies (rationalp x)
          (equal (+ (- x) (* 3 x))
                 (* 2 x))))




(defthm loghead-of-sum-of-prod-of-logext
  (implies (and (integerp i)
                (integerp k)
                )
           (equal (loghead n (+ k (* i (logext n j))))
                  (loghead n (+ k (* i (ifix j))))))
  :hints (("Goal"  :use (:instance loghead-of-prod-of-logext)
           :in-theory (disable loghead-of-prod-of-logext
                               ;LOGHEAD-+-CANCEL-BETTER
                               ))))

(defthm loghead-of-sum-of-prod-of-logext-blah
  (implies (and (integerp i)
                (integerp i2)
                (integerp k)
                )
           (equal (loghead n (+ k (* i i2 (logext n j))))
                  (loghead n (+ k (* i i2 (ifix j))))))
  :hints (("Goal" :use (:instance loghead-of-sum-of-prod-of-logext (i (* i i2)))
           :in-theory (disable loghead-of-sum-of-prod-of-logext))))

;bzo remove or generalize these?

(defthm removeme4
  (implies (and (integerp a)
                (integerp c))
           (equal (LOGHEAD n (+ a (- (LOGEXT n b)) c))
                  (LOGHEAD n (+ a (- (ifix b)) c)))))

(defthm removeme7
  (implies (and (integerp k)
                (integerp a))
           (equal (loghead n (+ a (- (* k (logext n b)))))
                  (loghead n (+ a (- (* k (ifix b))))))))

;;Note the overflow case:
;;(truncate (- (expt 2 31)) -1) is equal to (expt2 31), which is not a signed-byte-p 32.
;bzo gen
(defthm signed-byte-p-of-truncate
  (implies (and (signed-byte-p 32 i)
                (integerp j))
           (equal (signed-byte-p 32 (truncate i j))
                  (not (and (equal j -1)
                            (equal i (- (expt 2 31))))))
           )
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :nonlinearp t
           :cases ((and (<= i 0) (< j 0))
                   (and (<= i 0) (< 0 j))
                   (and (<= i 0) (= 0 j))
                   (and (< 0 i)(<= j 0))
                   (and (< 0 i)(< 0 j))
                   (and (< 0 i)(< j 0)))
           :in-theory (e/d (signed-byte-p) (LOGBITP-TEST-OF-TOP-BIT-ALT ;for acl2 3.0
                                            )))))




;; ;gen? make a fw-chaining rule to usb of size 1?
;; (defthmd bitp-unsigned-byte-p-24
;;   (implies (bitp x)
;;            (unsigned-byte-p 24 x))
;;   :hints (("goal" :in-theory (enable unsigned-byte-p bitp))))


(defthmd bitp-range
  (implies (bitp x)
           (and (<= x 1)
                (<= 0 x)))
  :hints (("goal" :in-theory (enable bitp))))






;or prove that logcar of a single bit does nothing
(defthm logcar-of-logbit
  (equal (logcar (logbit n x))
         (logbit n x))
  :hints (("Goal" :in-theory (enable logbit))))

;bzo gen
(defthm logtail-shift-hack
  (implies (integerp x)
           (equal (logtail 16 (* 32768 x))
                  (logtail 1 x)))
  :hints (("Goal" :in-theory (enable logtail ifloor ifix))) )




(defthmd hackz
  (implies (natp i)
           (equal (+ (/ a)
                     (* I (/ a)))
                  (/ (+ 1 i) a))))

(defthm hackzz
  (implies (natp i)
           (equal (+ (/ (+ 1 I))
                     (* I (/ (+ 1 I))))
                  1))
  :hints (("Goal" :in-theory (disable DISTRIBUTIVITY-ALT)
           :use (:instance hackz (a (+ 1 i))))))

(defthmd no-integerps-between-0-and-1
  (implies (and (< 0 i)
                (< i 1))
           (not (integerp i))))

(defthmd no-integerps-between-0-and-minus-1
  (implies (and (< i 0)
                (< -1 i))
           (not (integerp i))))

(defthm integerp-of-unary-/-when-integer-p
  (IMPLIES (INTEGERP Y)
           (EQUAL (INTEGERP (/ Y))
                  (or (equal 0 y)
                      (equal 1 y)
                      (equal -1 y)
                      )))
  :hints (("Goal" :in-theory (enable  no-integerps-between-0-and-1
                                      no-integerps-between-0-and-minus-1)
           :cases ((< 1 y) (< y -1)))))

(defthm arithhack2
  (implies (rationalp y)
           (equal (< 1 (/ Y))
                  (if (< 0 y)
                      (< Y 1)
                    (< 1 Y)
                    ))))

(encapsulate
 ()
 (local (defthm floor-of-one-more-case-1
          (implies (and (integerp x) ; (natp x)
                        (<= 0 x)
                        (integerp y)
                        (<= 0 y)
                        (equal 0 (mod (+ 1 x) y)))
                   (equal (FLOOR (+ 1 X) y)
                          (+ 1 (FLOOR X y))))
          :hints (("Goal" :in-theory (disable floor-equal-rewrite)
                   :use (:instance floor-equal-rewrite (n (+ -1 (+ (/ Y) (* X (/ Y))))) (x (/ x y)))))))

 (local (defthm floor-of-one-more-case-2
          (implies (and (natp x)
                        (natp y)
                        (not (equal 0 (mod (+ 1 x) y))))
                   (equal (FLOOR (+ 1 X) y)
                          (FLOOR X y)))
          :hints (("Goal" :in-theory (disable floor-equal-rewrite)))))

;generalize?
 (defthm floor-of-one-more
   (implies (and (syntaxp (not (quotep x))) ;prevents ACL2 from unifying this  (FLOOR (+ 1 X) y) with, say,  (FLOOR 65535 y)
                 (natp x)
                 (natp y))
            (equal (FLOOR (+ 1 X) y)
                   (if (equal 0 (mod (+ 1 x) y)) ;(integerp (/ (+ 1 x) y))
                       (+ 1 (FLOOR X y))
                     (FLOOR X y))))
   :hints (("Goal" :in-theory (disable MOD-=-0 ;bzo was forcing!
                                       )))))

(defthm mod-helper-1
  (IMPLIES (AND (INTEGERP X)
                (INTEGERP N)
                (<= 0 N)
                (<= 0 X)
                (NOT (INTEGERP (+ (/ (EXPT 2 N))
                                  (* X (/ (EXPT 2 N)))))))
           (NOT (EQUAL (MOD X (EXPT 2 N))
                       (+ -1 (EXPT 2 N))))))

(defthm one-two-multiples-fit
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (<= 0 c)
                (integerp c)
                (<= i c)
                (integerp (/ i c)))
           (or (equal i c)
               (equal i 0)))
  :rule-classes nil
  :hints (("Goal" :use (:instance no-integerps-between-0-and-1 (i (/ i c))))))

(defthmd mod-helper-2
  (IMPLIES (AND (INTEGERP X)
                (INTEGERP c)
                (< 0 c)
                (<= 0 X)
                (INTEGERP (+ (/ c)
                             (* X (/ c)))))
           (EQUAL (MOD X c)
                  (mod -1 c)))
  :hints (;gross!  subgoal hint after elimination!
          ("subgoal 1.1" :use (:instance one-two-multiples-fit (i (+ 1 i))))
          ("Goal" :in-theory (enable ;mod
                                     ))))

;this can cause a case split
(defthmd logbitp-of-one-more
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (integerp x)
                (integerp n)
                (<= 0 n)
                (<= 0 x)
                )
           (equal (logbitp n (+ 1 x))
                  (if (equal (loghead n x) (+ -1 (expt 2 n)))
                      (not (logbitp n x))
                    (logbitp n x))))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (LOGBITP LOGHEAD ;floor
                                    mod-helper-2
                     ;oddp EVENP expt
                                    imod
                                    ;mod
                                    )
                           (EVENP-COLLAPSE ;mod-cancel
                            )))))

;this can cause a case split
(defthmd logbit-of-one-more
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (integerp x)
                (integerp n)
                (<= 0 n)
                (<= 0 x)
                )
           (equal (logbit n (+ 1 x))
                  (if (equal (loghead n x) (+ -1 (expt 2 n)))
                      (b-not (logbit n x))
                    (logbit n x))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable logbit logbitp-of-one-more))))

;; (thm
;;  (implies (and (natp x) (natp y))
;;           (implies (EQUAL (LOGHEAD 15 X) (LOGHEAD 14 Y))
;;                    (equal (logbit 14 x) 0)))
;;  :otf-flg t
;;  :hints (("Goal" :in-theory (enable ;loghead logbit
;;                                     ))))


(defthmd other-way
  (IMPLIES (AND (INTEGERP X)
                (EQUAL (MOD X 16384) (MOD X 32768)))
           (INTEGERP (* 1/2 (FLOOR X 16384)))))


(defthm floor-linear-1
  (implies (rationalp x)
           (<= (floor x 1) x))
  :rule-classes :linear)

;; (DEFTHM FLoor-WEAKLY-MONOTONIC
;;   (IMPLIES (AND (<= Y Y+)
;;                 (CASE-SPLIT (RATIONALP Y))
;;                 (CASE-SPLIT (RATIONALP Y+)))
;;            (<= (FLoor Y 1) (FLoor Y+ 1)))
;;   :RULE-CLASSES
;;   ((:FORWARD-CHAINING :TRIGGER-TERMS ((FLoor Y 1) (FLoor Y+ 1)))
;;    (:LINEAR)
;;    (:FORWARD-CHAINING :TRIGGER-TERMS ((FLoor Y 1) (FLoor Y+ 1))
;;                       :COROLLARY
;;                       (IMPLIES (AND (< Y Y+)
;;                                     (CASE-SPLIT (RATIONALP Y))
;;                                     (CASE-SPLIT (RATIONALP Y+)))
;;                                (<= (FLoor Y 1) (FLoor Y+ 1))))
;;    (:LINEAR :COROLLARY
;;             (IMPLIES (AND (< Y Y+)
;;                           (CASE-SPLIT (RATIONALP Y))
;;                           (CASE-SPLIT (RATIONALP Y+)))
;;                      (<= (FLoor Y 1) (FLoor Y+ 1))))))

;can be expensive?
(defthm floor-when-<-2
  (implies (and (< i 2)
                (<= 0 i)
                (rationalp i))
           (equal (floor i 1)
                  (if (< i 1)
                      0
                    1))))

;bzo combine the ways
;rename
(defthmd one-way
  (IMPLIES (AND (INTEGERP (* 1/2 (FLOOR X 16384)))
                (INTEGERP X))
           (EQUAL (MOD X 16384)
                  (MOD X 32768)))
  :hints (("Goal" :in-theory (disable evenp-collapse))))


;keep this disabled most of the time
(defthmd loghead-split-x-rewrite
  (implies (and (syntaxp (equal x 'x))
                (integerp n)
                (< 0 n))
           (equal (loghead n x)
                  (logapp (+ -1 n)
                          (loghead (+ -1 n) x)
                          (logbit (+ -1 n) x))))
  :hints (("Goal" :by loghead-split)))

(defthmd loghead-split-y-rewrite
  (implies (and (syntaxp (equal x 'y))
                (integerp n)
                (< 0 n))
           (equal (loghead n x)
                  (logapp (+ -1 n)
                          (loghead (+ -1 n) x)
                          (logbit (+ -1 n) x))))
  :hints (("Goal" :in-theory (disable loghead-split-x-rewrite)
           :use (:instance loghead-split-x-rewrite))))


;rename
;gen the +1 ?
(defthm equal-of-logheads-of-when-one-is-one-longer
  (implies (and (equal m (+ 1 n)) ;in case the (+ 1 n) doesn't match
                (integerp n)
                (<= 0 n))
           (equal (equal (loghead m x) (loghead n y))
                  (and (equal (logbit n x) 0)
                       (equal (loghead n x)
                              (loghead n y)))))
  :hints (("Goal" :in-theory (enable loghead-split-y-rewrite
                                     loghead-split-x-rewrite))))

;shouldn't need the -alt form.  if i do, complaint to matt and j?
(defthm equal-of-logheads-of-when-one-is-one-longer-alt
  (implies (and (equal (+ 1 n) m) ;in case the (+ 1 n) doesn't match
                (integerp n)
                (<= 0 n))
           (equal (equal (loghead m x) (loghead n y))
                  (and (equal (logbit n x) 0)
                       (equal (loghead n x)
                              (loghead n y)))))
  :hints (("Goal" :in-theory (enable loghead-split-y-rewrite
                                     loghead-split-x-rewrite))))

;subsumed by the rule that rewrites an equality of logexts to and equality of logheads?
;; (defthm hackyyy
;;   (equal (equal (logext 16 x) (logext 15 y))
;;          (and (equal (logbit 15 x) (logbit 14 y))
;;               (equal (loghead 15 x)
;;                      (loghead 15 y))))
;;   :otf-flg t
;;   :hints (("Goal"
;;            :in-theory (enable logext))))


(defthm logtail-equal-minus-one-rewrite
  (equal (equal -1 (logtail n x))
         (if (and (integerp n)
                  (<= 0 n))
             (and (< x 0)
                  (signed-byte-p (+ 1 n) x))
           (equal -1 x)))
  :hints (("Goal" :in-theory (enable logtail signed-byte-p ifloor ifix))))

(defthm <-of-ash
  (implies (and (natp n)
                (rationalp k)
                )
           (equal (< k (ASH x n))
                  (< (/ k (expt 2 n)) (ifix x))))
  :hints (("Goal" :in-theory (enable ash ifix))))

(defthm logtail-shift
  (implies (and (<= m n)  ;handle other case
                (integerp x)
                (< 0 n)
                (integerp n)
                (<= 0 m)
                (integerp m)
                )
           (equal (logtail n (* (expt 2 m) x))
                  (logtail (- n m) x)))
  :hints (("Goal" :use (:instance INTEGERP-EXPT (n (- n m)))
           :in-theory (e/d (logtail ifloor ifix FLOOR-NORMALIZES-TO-HAVE-J-BE-1
                              EXPONENTS-ADD-UNRESTRICTED)
                           (INTEGERP-EXPT)))))

(defthm logtail-shift-constant-version
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (<= (expo k) n)  ;handle other case
                (integerp x)
                (< 0 n)
                (integerp n)
                (<= 0 (expo k))
 ;               (integerp m)
                )
           (equal (logtail n (* k x))
                  (logtail (- n (expo k)) x)))
  :hints (("Goal" :use (:instance logtail-shift (m (expo k)))
           :in-theory (disable logtail-shift))))



;does this function already exist?
;the divisor goes first, since it will often be a constant number like 2
(defund divides (x y)
  (integerp (/ y x)))

(defthm divides-hack
  (equal (INTEGERP (+ (* 1/65536 I) (- (* 1/65536 I1))))
         (divides 65536 (+ i (- i1))))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-hack2
  (equal (INTEGERP (* 1/65536 I))
         (divides 65536 i))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-of-sum
  (implies (and (divides x y)
                (divides x z))
           (divides x (+ y z)))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-of-sum-2
  (implies (divides x y)
           (equal (divides x (+ y z))
                  (divides x z)))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-of-sum-2b
  (implies (divides x z)
           (equal (divides x (+ y z))
                  (divides x y)))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-of-sum-2c
  (implies (divides x w)
           (equal (divides x (+ y z w))
                  (divides x (+ y z))))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-of-unary-minus
  (equal (divides x (- z))
         (divides x z))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-of-times-1
  (implies (and (divides x y)
                (integerp z))
           (divides x (* y z)))
  :hints (("Goal" :in-theory (enable divides))))

(defthm divides-of-times-2
  (implies (and (divides x z)
                (integerp y))
           (divides x (* y z)))
  :hints (("Goal" :in-theory (enable divides))))

(defthmd integerp-squeeze-hack
  (implies (and (< x 2)
                (< 0 x))
           (equal (integerp x)
                  (equal 1 x))))

(defthm divides-squeeze-hack
  (implies (and (< y (* 2 x))
                (< 0 y)
                (rationalp x)
                (rationalp y)
                )
           (equal (divides x y)
                  (equal x y)))
  :hints (("Goal" :in-theory (enable divides  integerp-squeeze-hack))))

(defthmd integerp-squeeze-hack-2
  (implies (and (< -1 x)
                (<= x 0))
           (equal (integerp x)
                  (equal 0 x))))

(defthm divides-squeeze-hack-3
  (implies (and (<= y 0)
                (< (- x) y)
                (< 0 x)
                (rationalp x)
                (rationalp y)
                )
           (equal (divides x y)
                  (equal -0 y)
                  ))
  :hints (("Goal" :in-theory (enable divides integerp-squeeze-hack-2))))

(defthm divides-squeeze-hack-2
  (implies (and (< y (* 2 x))
                (< (- x) y)
                (rationalp x)
                (rationalp y)
                )
           (equal (divides x y)
                  (if (< 0 y)
                      (equal x y)
                    (equal 0 y)
                    )))
  :hints (("Goal" :in-theory (enable divides integerp-squeeze-hack-2 integerp-squeeze-hack))))

;gen!
(defthm mod-of-difference-equal-0-rewrite
  (implies (and (integerp x)
                (integerp y)
                )
           (equal (equal 0 (mod (+ (- x) y) 65536))
                  (equal (mod x 65536) (mod y 65536)))))

;gen!
(defthm mod-of-difference-equal-0-rewrite-alt
  (implies (and (integerp x)
                (integerp y)
                )
           (equal (equal 0 (mod (+ y (- x)) 65536))
                  (equal (mod x 65536) (mod y 65536)))))


(defthm loghead-of-difference-equal-0-rewrite-alt
  (implies (and (integerp x)
                (integerp y)
                (<= 0 n)
                (integerp n)
                )
           (equal (equal 0 (loghead n (+ y (- x))))
                  (equal (loghead n x) (loghead n y))))
  :hints
  (("Goal" :in-theory (e/d (;loghead
                            LOGHEAD-SUM-SPLIT-INTO-2-CASES
                            imod ifix) (mod-=-0)))))


(defthm loghead-of-difference-equal-0-rewrite
  (implies (and (integerp x)
                (integerp y)
                (<= 0 n)
                (integerp n)
                )
           (equal (equal 0 (loghead n (+ (- x) y)))
                  (equal (loghead n x) (loghead n y))))
  :hints
  (("Goal" :in-theory (e/d (;loghead
                            LOGHEAD-SUM-SPLIT-INTO-2-CASES
                            imod ifix) (mod-=-0)))))

;bzo harvest the stuff below

;generalize?
(defthmd mod-16-32
  (implies (and (unsigned-byte-p n x)
                (< n 32) ;could this be <=
                )
           (equal (mod x 4294967296)
                  x))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P UNSIGNED-BYTE-P))))

(defthmd ash1-is-mult2
  (equal (ash x 1)
         (* (ifix x) 2))
  :hints (("Goal" :in-theory (e/d (ash)(unsigned-byte-p)))))


(defthmd ash-is-mult2
  (implies (and (unsigned-byte-p 16 x)
                (integerp n)
                (< 0 n))
           (equal (ash x n)
                  (ash (ash x (1- n)) 1)))
  :hints (("Goal" :in-theory (e/d (ash expt)(unsigned-byte-p)))))

;move this
;try disabling this
(defthmd ash-open
  (implies (and (unsigned-byte-p 16 x)
                (integerp n)
                (< 0 n))
           (equal (ash x n)
                  (* (ash x (1- n)) 2)))
  :hints (("goal" :in-theory (enable ash expt))))

(defthmd shift-is-mult2
  (implies (unsigned-byte-p 16 x)
           (equal (lshu 32 x 1)
                  (* x 2)))
:hints (("Goal" :in-theory (e/d (lshu loghead ash)(unsigned-byte-p)))))

;move?
;rephrase conclusion?

(defthm shift-bounds
  (implies (unsigned-byte-p 16 x)
           (<= (lshu 32 x 16) (- (expt 2 32) (expt 2 16))))
  :hints (("Goal" :in-theory (e/d (lshu loghead ash) nil))))

;; ;bzo generalize
;handled below
;; (defthm sbp-of-logapp-hack
;;   (implies (signed-byte-p 16 b)
;;            (signed-byte-p 32 (logapp 16 a b)))
;;   :hints (("Goal" :in-theory (enable logapp
;;                                      signed-byte-p
;;                                      integer-range-p))))



;;This take us from the unsigned-byte-p world to the arithmetic world, but
;;since the LHS mentions +, maybe we're already in the arithmetic world.
(defthm unsigned-byte-p-of-sum-with-constant
  (implies (and (syntaxp (quotep c))
                (unsigned-byte-p n c)
                (unsigned-byte-p n x))
           (equal (unsigned-byte-p n (+ c x))
                  (< x (- (expt 2 n) c))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p))))




;We want to extend an inequality like (< x 65535) to (< x 65536) when we also know (not (equal x 65535)) and (integerp x).
;Writing the rule with the free variable means we really must find the disquality right there in the context.
;Perhaps this should pay attention to whether we're trying to satisfy or falsity the <.
;seemed to loop.
(defthmd extend-<
  (implies (and (not (equal x free))
                (equal free k)
                (integerp x)
                (integerp k))
           (equal (< x k)
                  (< x (+ 1 k)))))

;bad name!
;same as usb-linear-rewrite in bags library!
(defthm usb-linear-rewrite
  (implies (and (unsigned-byte-p n x) ;n is a free variable
                (<= (expt 2 n) v))
           (< x v))
  :rule-classes (:rewrite)
  :hints (("goal" :in-theory (enable unsigned-byte-p))))


(defthmd logbitp-top-bit-when-signed-byte-p
  (implies (and (signed-byte-p (+ 1 n) x)
                (integerp n)
                (<= 0 n))
           (equal (logbitp n x)
                  (< x 0)))
  :hints (("Goal" :in-theory (enable logbitp signed-byte-p))))
(in-theory (disable LOGBITP-TEST-OF-TOP-BIT))

;;
;; (defthm loghead-subst-32
;;   (implies (and (equal (loghead 32 x) k)
;;                 (syntaxp (quotep k))
;;                 )
;;            (equal (loghead 31 x)
;;                   (loghead 31 k))))


;bzo gen
(defthm loghead-subst-2
  (implies (and (equal (loghead 31 x) k)
                (syntaxp (quotep k))
                )
           (equal (loghead 32 x)
                  (logapp 31 k (logbit 31 x))
                  )))



(defthm logorc1-of-zero-two
  (equal (logorc1 x 0)
         (lognot x))
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm logorc1-of-zero-one
  (equal (logorc1 0 x)
         -1)
  :hints (("Goal" :in-theory (enable logorc1))))

(defthm logeqv-of-zero-one
  (equal (logeqv 0 x)
         (lognot x))
  :hints (("Goal" :in-theory (enable logeqv lognot))))

(defthm logeqv-commutative
  (equal (logeqv x y)
         (logeqv y x))
  :hints (("Goal" :in-theory (e/d (logeqv lognot)
                                  (LOGAND-LOGIOR ;bzo forcing
                                   )))))

(defthm logand-with-negative-of-power-of-2
  (implies (and (<= 0 n)
                (integerp n))
           (equal (logand (- (expt 2 n)) x)
                  (logapp n 0 (logtail n x))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :expand (logand x (- (expt 2 n)))
           :induct (sub1-logcdr-induction n x)
           :in-theory (enable LOGTAIL*-better
                              logand ash logcdr exponents-add-unrestricted))))

(defthm logand-with-negative-of-power-of-2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (- (expt 2 (expo k))))
                (<= 0 (expo k))
                )
           (equal (logand k x)
                  (logapp (expo k) 0 (logtail (expo k) x))))
  :hints (("Goal" :use (:instance  logand-with-negative-of-power-of-2 (n (expo k)))
           :in-theory (disable  logand-with-negative-of-power-of-2))))

(defthmd divide-both-sides-hack
  (implies (equal x y)
           (equal (/ x z) (/ y z))))

(defthm cancel-negated-case
  (implies (and (< 0 y)
                (integerp x)
                (integerp y))
           (equal (equal (- y) (* x y))
                  (equal -1 x)))
  :hints (("Goal" :use (:instance divide-both-sides-hack (x (- y)) (y (* x y)) (z y))))
  )

;gen?
(defthm ash-equal-minus-expt2n
  (implies (and (< 0 n)
                (integerp n))
           (equal (equal (- (expt 2 n)) (ASH x n))
                  (equal x -1)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm ash-equal-minus-expt2n-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (- (expt 2 n)))
                (< 0 n)
                (integerp n)
                )
           (equal (equal k (ASH x n))
                  (equal x -1)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm logeqv-neg
  (implies (and (integerp x)
                (integerp y))
           (equal (< (logeqv x y) 0)
                  (or (and (<= 0 x)
                           (<= 0 y))
                      (and (< x 0)
                           (< y 0)))))
  :hints (("Goal" :in-theory (enable logeqv
                                     logorc1
                                     ))))

;; (defthm logeqv-pos
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (< 0 (logeqv x y))
;;                   (or (and (<= x 0)
;;                            (<= 0 y))
;;                       (and (< 0 x)
;;                            (< y 0)))))
;;   :hints (("Goal" :in-theory (enable logeqv
;;                                      logorc1
;;                                      lognot
;;                                      ))))

(defthm unsigned-byte-p-of-lognot
  (equal (unsigned-byte-p n (lognot x))
         (and (< x 0)
              (unsigned-byte-p n (+ -1 (- x)))))
  :hints (("Goal" :in-theory (enable lognot))))

;more rules like this?
(defthm logbit-subst-simpler
  (implies (and (equal (loghead n x) (loghead n y))
                (syntaxp (smaller-term y x))
                (< m n)
                (<= 0 m)
                (integerp n)
                (integerp m)
                )
           (equal (logbit m x)
                  (logbit m y)))
  :hints (("Goal" :use ((:instance logbit-loghead-better (pos m) (size n) (i x))
                        (:instance logbit-loghead-better (pos m) (size n) (i y)))
           :in-theory (disable logbit-loghead-better))))

(defthm logbit-of-logcar
  (equal (logbit n (logcar x))
         (if (and (< 0 n)
                  (integerp n))
             0
           (logcar x))))

;changed the RHS to do a case-split because 0 is so much simpler than (ash (logbit (+ -1 n) x) (+ -1 n))
;split into 2 rules?
(defthm loghead-when-mostly-0
  (implies (and (equal (loghead m x) 0) ;m is a free variable
                (<= (+ -1 n) m)
                (integerp m)
                (integerp n)
                )
           (equal (loghead n x)
                  (if (equal m (+ -1 n))
                      (ash (logbit (+ -1 n) x) (+ -1 n))
                    0)))
  :hints (("Goal" :use (:instance loghead-split))))

;The if in the RHS prevents a logapp from being introduced needlessly.

;add ifix to conclusion?

(defthmd loghead-subst-simpler-2
  (implies (and (equal (loghead m x) (loghead m y)) ;y is a free variable
                (syntaxp (smaller-term y x))
                (<= (+ -1 n) m)
                (integerp m)
                (integerp n)
                (< 0 n)
                )
           (equal (loghead n x)
                  (if (equal m (+ -1 n))
                      (if (integerp y)
                          (logapp (+ -1 n) y (logbit (+ -1 n) x))
                        (logapp (+ -1 n) 0 (logbit (+ -1 n) x)))
                    (loghead n y)))))

;Note the backchain-limit
(defthm loghead-equal-when-almost-equal
  (implies (and (equal (loghead m x) (loghead m y))
                (equal m (+ -1 n)) ;phrased in this weird way so that hyp 1 is sure to match...
                (< 0 n)
                (integerp m)
                (integerp n)
                )
           (equal (equal (loghead n x) (loghead n y))
                  (equal (logbit m x) (logbit m y))))
  :hints (("Goal" :cases ((integerp x))
           :in-theory (enable loghead-subst-simpler-2)
           ))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil nil nil))))

(defthm logapp-loghead-drop
  (implies (and (<= m n)
                (<= 0 m) ;gen this after gening LOGTAIL-LOGAPP-BETTER?
                (integerp n)
                (integerp m)
                )
           (equal (logapp m (loghead n x) y)
                  (logapp m x y))))


;; ;gen the n arg to loghead
;; ;drop?
;; (defthm logtail-loghead-to-logbit
;;   (implies (and (integerp n)
;;                 (< 0 n))
;;            (equal (LOGTAIL (+ -1 N) (LOGHEAD N X))
;;                   (logbit (+ -1 n) x)))
;;   :hints (("Goal" :in-theory (enable logbit logbitp))))

;gen the 1
(defthm loghead-equal-logapp-same-rewrite
  (implies (and (integerp n)
                (< 0 n))
           (equal (equal (loghead n x) (logapp (+ -1 n) x 1))
                  (equal 1 (logbit (+ -1 n) x)))))

(defthm loghead-equal-loghead-one-shorter-rewrite
  (implies (and (integerp x)
                (integerp n)
                (< 0 n))
           (equal (equal (loghead (+ -1 n) x) (loghead n x))
                  (equal (logbit (+ -1 n) x) 0)))
  :hints (("Goal" :in-theory (enable loghead-split-x-rewrite))))

;gen the but position at which the difference occurs
;expensive?
(defthm loghead-differ-when-bit-differs
  (implies (and (not (logbitp (+ -1 n) y))
                (logbitp (+ -1 n) x))
           (equal (equal (loghead n y) (loghead n x))
                  (not (and (integerp n)
                            (< 0 n)))))
  :hints (("Goal" :in-theory (enable loghead-split-y-rewrite loghead-split-x-rewrite))))

(defthm loghead-differ-when-bit-differs-alt
  (implies (and (not (logbitp (+ -1 n) y))
                (logbitp (+ -1 n) x))
           (equal (equal (loghead n x) (loghead n y))
                  (not (and (integerp n)
                            (< 0 n)))))
  :hints (("Goal" :in-theory (enable loghead-split-y-rewrite loghead-split-x-rewrite))))

;this one uses the signed-byte-p range
(defthm loghead-sum-chop-first-arg-when-constant-alt
  (implies (and (syntaxp (and (quotep x)
                              (quotep n) ;bzo without this we got a loop; change other rules similarly
                              ))
                (not (unsigned-byte-p n x))
                (< 0 n)
                (integerp n)
                (integerp x)
                (integerp y))
           (equal (loghead n (+ x y))
                  (loghead n (+ (loghead n x) y)))))

(in-theory (disable loghead-sum-chop-first-arg-when-constant))


;can this loop?  maybe this and others like it are okay...
;restrict to when j is a quotep?
(defthm logbit-subst
  (implies (and (equal j (loghead pos2 i))
                (syntaxp (smaller-term j i))
                (< pos pos2)
                (integerp pos)
                (integerp pos2)
                (<= 0 pos)
                )
           (equal (logbit pos i)
                  (logbit pos j))))


;;
;; (defthm logbitp-subst-32
;;   (implies (and (equal (loghead 32 x) k)
;;                 (syntaxp (quotep k))
;;                 )
;;            (equal (logbitp 31 x)
;;                   (logbitp 31 k))))

;can this loop?
;restrict to when j is a quotep?
(defthm logbitp-subst
  (implies (and (equal j (loghead pos2 i))
                (syntaxp (smaller-term j i))
                (< pos pos2)
                (integerp pos)
                (integerp pos2)
                (<= 0 pos)
                )
           (equal (logbitp pos i)
                  (logbitp pos j)))
  :hints (("Goal" :use (:instance logbit-subst)
           :in-theory (disable logbit-subst))))

(defthm logbitp-subst-2
   (implies (and (equal (loghead pos2 j) (loghead pos2 i))
                 (syntaxp (smaller-term j i))
                 (< pos pos2)
                 (integerp pos)
                 (integerp pos2)
                 (<= 0 pos)
                 )
            (equal (logbitp pos i)
                   (logbitp pos j)))
   :hints (("Goal" :use (:instance logbit-subst-simpler (x i) (y j) (m pos) (n pos2))
            :in-theory (e/d (logbit) (logbit-subst LOGBIT-SUBST-SIMPLER)))))

;bzo gen
(defthm logext-equal-min-value-hack
  (implies (integerp x)
           (equal (equal (logext 32 x) -2147483648)
                  (equal (loghead 32 x) 2147483648)))
  :hints (("Goal" :in-theory (enable logext))))


;don't enable this rule, or you'll probably get a loop!
;use this to prove some super-ihs lemmas - like the splitting once rules...
(defthmd loghead-split-gen
  (implies (and (integerp n)
                (<= m n)
                (integerp m)
                (<= 0 m)
                )
           (equal (loghead n x)
                  (logapp m x (logtail m (loghead n x))))))


(defthm ash-equal-expt-rewrite
  (implies (and (integerp n)
                (<= 0 n))
           (equal (equal (ash 1 n) (expt 2 n))
                  t
                  ))
  :hints (("Goal" :in-theory (enable ash))))

(defthm loghead-equal-expt-rewrite
  (implies (and (integerp n)
                (< 0 n))
           (equal (equal (loghead n x) (expt 2 (+ -1 n)))
                  (and (logbitp (+ -1 n) x)
                       (equal (loghead (+ -1 n) x) 0))))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (ash
                                   LOGHEAD-SPLIT-X-REWRITE)
                                  (loghead-when-mostly-0
                                   LOGTAIL-LEAVES-SINGLE-BIT
                                   LOGHEAD-EQUAL-LOGAPP-SAME-REWRITE
                                   LOGAPP-0-PART-1-BETTER
                                   ))
           :use (:instance loghead-split-gen (m (+ -1 n))))))

(defthm signed-byte-p-of-minus-2-to-the-n-minus-1
  (implies (and (integerp n)
                (< 0 n))
           (signed-byte-p n (- (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

(defthm logext-equal-min-value-hack-gen
  (implies (and (integerp x)
                (integerp n)
                (< 0 n))
           (equal (equal (logext n x) (- (expt 2 (+ -1 n))))
                  (equal (loghead n x) (expt 2 (+ -1 n)))))
  :otf-flg t
  :hints (("Goal" :in-theory (enable logext ash))))

(defthm logext-equal-min-value-hack-gen-constant-version
  (implies (and (syntaxp (and (quotep k)
                              (quotep n)
                              ))
                (equal k (- (expt 2 (+ -1 n))))
                (integerp x)
                (integerp n)
                (< 0 n))
           (equal (equal (logext n x) k)
                  (equal (loghead n x) (expt 2 (+ -1 n)))))
  :otf-flg t
  :hints (("Goal" :use (:instance logext-equal-min-value-hack-gen)
            :in-theory (disable logext-equal-min-value-hack-gen))))



;bzo - lots of stuff in this file need (especially stuff below this comment)
;to be improved, sorted, etc.

;reorder hyps?
(defthm unsigned-byte-p-plus-limit
  (implies (and (unsigned-byte-p n (+ k x)) ;k is a free variable
                (<= j k)
                (unsigned-byte-p n x)
                (<= 0 j)
                (integerp k)
                (integerp j))
           (unsigned-byte-p n (+ j x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p integer-range-p))))





;replace the other?
(defthm plus-of-logapp-suck-in-gen2
  (implies (and (unsigned-byte-p k (+ x (loghead k y)))
                (natp k)
                (integerp x)
                (integerp j)
                (integerp y)
                )
           (equal (+ x (logapp k y j))
                  (logapp k (+ x y) j)))
  :hints (("Goal" :use (:instance loghead-identity (size k) (i  (+ x (loghead k y))))
           :in-theory (e/d (logapp) (loghead-identity
                                     loghead-does-nothing-rewrite)))))

;Can cause a case split.
(defthmd loghead-suck-in-one-plus
  (implies (and (syntaxp (and (consp x)
                              (equal (car x) 'binary-+)
                              (quotep (cadr x))))
                (integerp x)
                (<= 0 n)
                )
           (equal (+ 1 (loghead n x))
                  (if (equal (+ -1 (expt 2 n)) (loghead n x))
                      (expt 2 n)
                    (loghead n (+ 1 x)))))
  :hints (("Goal" :in-theory (enable LOGHEAD-OF-ONE-MORE-THAN-X
                                     ))))




;; ;gen
;; (defthm loghead-sum-loghead-3
;;   (equal (loghead 16 (+ y z (loghead 16 x)))
;;          (if (integerp x)
;;              (if (integerp (+ y z))
;;                  (loghead 16 (+ x y z))
;;                (if (acl2-numberp (+ y z))
;;                    0
;;                  (loghead 16 x)))
;;            (loghead 16 (+ y z))))
;;   :hints (("Goal" :in-theory (disable loghead-sum-loghead)
;;            :use (:instance loghead-sum-loghead (y (+ y z))))))



;; (thm
;;  (equal (LOGTAIL 16 (DATA-ADDRESS addr ST))
;;          (LOGEXT 17
;;                (LOGAPP 1 (LOGTAIL 15 ADDR)
;;                        (NTH *aamp.denvr* ST))) ;(LOGTAIL 15 addr)
;;         )
;;  :hints (("Goal" :in-theory (enable DATA-ADDRESS makeaddr))))


;; ;add syntaxp hyp to prevent loops?
;; ;generalize elsewhere for any constant?
;; (defthm loghead-plus-mult-16
;;   (implies (and (syntaxp (not (quotep off)))
;;                 (integerp off))
;;            (equal (loghead 16 (+ 65536 off))
;;                   (loghead 16 off)))
;;   :hints (("Goal" :in-theory (enable loghead))))

(defthm logapp-sum-normalize-leading-constant
  (implies (and (syntaxp (and (quotep k) (quotep n)))
                (not (unsigned-byte-p n k))
                (<= 0 n) ;drop?
                (integerp n)
                (integerp off)
                (integerp k)
                )
           (equal (logapp n (+ k off) cenv)
                  (logapp n (+ (loghead n k) off) cenv))))

(defthm logapp-normalize-constant-arg
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep size)) ;saw a loop without this
                (not (unsigned-byte-p size a))
                (integerp size)
                (<= 0 size)
                )
           (equal (logapp size a b)
                  (logapp size (loghead size a) b))))

;bzo think about the syntaxp hyp here and elsewhere
;
;
;looped, because it replaced (BINARY-+
;'65535 x) with the smaller term (BINARY-+
;'-1 x) which gets written back, due to our
;normal forms..
(defthmd logapp-subst-in-first-arg
  (implies (and (equal c (loghead size a))
                (syntaxp (smaller-term c a))
                )
           (equal (logapp size a b)
                  (logapp size c b))))


;move
(defthm odd-<-even-tighten
  (implies (and (integerp i)
                (integerp j))
           (equal (< (+ 1 (* 2 j)) (* 2 i))
                  (< (* 2 j) (* 2 i)))))

(defthm logapp-does-nothing-rewrite
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n)
                )
           (equal (equal x (logapp n x y))
                  (equal y (logtail n x)))))

(defthm logapp-of-loghead
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logapp n (loghead n x) y)
                  (logapp n x y))))


;; ;kind of weird
;; ;bzo gross hints
;; (defthmd loghead-stretch-8-16
;;   (implies (and (equal 0 (loghead 8 (logtail 8 x)))
;;                 (integerp x))
;;            (equal (loghead 8 x)
;;                   (loghead 16 x)
;;                   ))
;;   :hints (("Goal" :in-theory (e/d (logapp-hack2)
;;                                   ( logapp-loghead-logtail
;;                                     LOGTAIL-leaves-single-bit
;;                                     LOGAPP-OF-LOGHEAD
;;                                     LOGBIT-LOGHEAD-BETTER
;;                                     logapp-does-nothing-rewrite
;;                                     equal-logapp-x-y-z
;;                                     equal-logapp-x-y-z-constants
;;                                     LOGHEAD-WHEN-MOSTLY-0
;;                                     ))
;;            :use (:instance logapp-loghead-logtail (i x) (size 8)))))


;This is really weird, but I saw it come up in a proof. -ews
(defthm logbit-does-nothing-rewrite
  (implies (and (integerp pos)
                (<= 0 pos))
           (equal (equal (logbit pos i) i)
                  (or (equal i 0)
                      (and (equal i 1)
                           (equal pos 0)))))
  :hints (("Goal" :in-theory (enable logbit logbitp))))


;; (defthm logapp-+-hack
;;   (implies (and (integerp k) (integerp x) (integerp x2) (integerp y))
;;            (equal (LOGAPP 16 (+ K (LOGAPP 16 Y x)) x2)
;;                   (LOGAPP 16 (+ K y) X2))))


;; If this seems expensive, we could add a backchain-limit. -ews
(defthm logbit-of-usb-1
  (implies (unsigned-byte-p 1 x)
           (equal (logbit 0 x)
                  x))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm equal-constant-false-from-usb
  (implies (and (syntaxp (quotep y))
                (unsigned-byte-p n x)
                (<= (expt 2 n) y))
           (equal (equal x y)
                  nil)))

(defthm loghead-cancel-constants-hack
  (implies (and (syntaxp (and (quotep k1)   ;i think i want these syntaxp hyps, right?
                              (quotep k2)))
                (integerp x)
                (integerp y)
                (integerp k1)
                (integerp k2)
                )
           (equal (equal (loghead n (+ k1 x))
                         (loghead n (+ k2 y)))
                  (equal (loghead n (+ (- k1 k2) x))
                         (loghead n y))))
  :hints (("Goal" :in-theory (enable loghead-sum-split-into-2-cases))))

(defthm logbit-too-big
  (implies (and (unsigned-byte-p n x)
                (<= n (ifix m)))
           (equal (logbit m x)
                  0))
  :hints (("Goal" :in-theory (enable logbit))))

;generalize the 1
(defthm equal-to-ash-1-rewrite
  (equal (equal x (ash y 1))
         (and (integerp x)
              (equal (logcar x) 0)
              (equal (logcdr x) (ifix y)))))

(in-theory (disable
;                    logext-logapp ;trying enabled...
                    ))


(in-theory (disable loghead-sum-chop-first-arg-when-constant))





(defthm loghead-of-logext-hack-1
  (implies (and (integerp x)
                (integerp y))
           (equal (loghead size (+ (- (logext size x)) y))
                  (loghead size (+ (- x) y))))
  :hints (("Goal" :use ((:instance LOGHEAD-+-LOGHEAD (i y) (j (- (logext size x))))
                        (:instance LOGHEAD-+-LOGHEAD (i y) (j (- x))))
           :in-theory (disable LOGHEAD-+-LOGHEAD
                               LOGHEAD-+-CANCEL-0
                               LOGHEAD-WHEN-MOSTLY-0
                               LOGHEAD-SUBST-SIMPLER-2
                               LOGHEAD-+-CANCEL-BETTER))))

(defthm loghead-of-logext-hack-1-alt
  (implies (and (integerp x)
                (integerp y))
           (equal (loghead size (+ y (- (logext size x))))
                  (loghead size (+ y (- x)))))
  :hints (("Goal" :use ((:instance LOGHEAD-+-LOGHEAD (i y) (j (- (logext size x))))
                        (:instance LOGHEAD-+-LOGHEAD (i y) (j (- x))))
           :in-theory (disable LOGHEAD-+-LOGHEAD
                               LOGHEAD-+-CANCEL-0
                               LOGHEAD-WHEN-MOSTLY-0
                               LOGHEAD-SUBST-SIMPLER-2
                               LOGHEAD-+-CANCEL-BETTER))))

(defthm loghead-of-logext-hack-2
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                )
           (equal (loghead size (+ z (- (* i (logext size x))) y))
                  (loghead size (+ z (- (* i x)) y))))
  :hints (("Goal" :cases ((integerp (+ y z)))))
  )

(defthm loghead-of-logext-hack-3
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                )
           (equal (loghead size (+ z y (* i (logext size x))))
                  (loghead size (+ z (* i x) y))))
  :hints (("Goal" :cases ((integerp (+ y z))))))

;move
;more like this?
(defthm loghead-+-cancel-better-alt-1
  (implies (and (integerp y)
                (integerp zblah1)
                (integerp zblah2)
                (integerp x)
                )
           (equal (equal (loghead size (+ y x zblah1))
                         (loghead size (+ x zblah2)))
                  (equal (loghead size (+ y zblah1))
                         (loghead size zblah2)))))

(defthm loghead-of-logext-hack-4
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp z)
                )
           (equal (loghead size (+ z y (- (logext size x)) w))
                  (loghead size (+ z (- x) y w))))
  :hints (("Goal" :in-theory (disable ;loghead-+-cancel-better
                              loghead-of-sum-of-prod-of-loghead-lemma
                              )
           :use ((:instance loghead-of-sum-of-prod-of-loghead-lemma (n size) (y -1) (a (+ z y w)) (x x))))))

(defthm loghead-of-logext-hack-5
  (implies (and (integerp x)
                (integerp y)
                (integerp i)
                (integerp w)
                (integerp v)
;                (integerp z)
                )
           (equal (loghead size (+ z y w v (- (* i (logext size x)))))
                  (loghead size (+ z y w v (- (* i x))))))
  :hints (("Goal" :in-theory (disable LOGHEAD-OF-SUM-OF-PROD-OF-LOGHEAD-LEMMA
                                      )
           :use (:instance LOGHEAD-OF-SUM-OF-PROD-OF-LOGHEAD-LEMMA (n size) (y (- i)) (a (+ z y w v)) (x x)))))


(defthm integerp-<-hack
  (implies (and (integerp a)
                (integerp b))
           (equal (< (+ 1/2 b) a)
                  (<= (+ 1 b) a))))

(defthm divides-hack-more
  (equal (integerp (+ 1/65536 (* 1/65536 x)))
         (divides 65536 (+ 1 x)))
  :hints (("Goal" :in-theory (e/d (divides) (divides-hack2 ;looped
                                                   )))))
(defthm divides-16-hack
  (implies (integerp x)
           (equal (divides 65536 x)
                  (equal (loghead 16 x) 0)))
  :hints (("Goal" :in-theory (enable loghead))))

(in-theory (disable MOD-=-0)) ;bzo investigate loops - make a better version of this rule?

;; (defthm logtail-of-one-more
;;   (implies (integerp x)
;;            (equal (logtail 16 (+ 1 x))
;;                   (if (equal 65535 (loghead 16 x))
;;                       (+ 1 (logtail 16 x))
;;                     (logtail 16 x))))
;;   :hints (("Goal" :in-theory (enable logtail loghead
;;                                      ))))


;Strange proof?
(defthmd logtail-of-one-more
  (implies (and (integerp x)
                (<= 0 n)
                (integerp n))
           (equal (logtail n (+ 1 x))
                  (if (equal (+ -1 (expt 2 n)) (loghead n x))
                      (+ 1 (logtail n x))
                    (logtail n x))))
  :hints (("Goal" :in-theory (enable logtail loghead
                                     ))))


(defthm logapp-logbit-reassemble
  (implies (and (integerp n)
                (<= 0 n)
                )
           (equal (logapp n a (logbit n a))
                  (loghead (+ 1 n) a)))
  :hints (("Goal" :in-theory (e/d (equal-logapp-x-y-z
                                     logtail-loghead-better
                                     )
                                  (loghead-logtail)))))


;; ;do we have any of these elsewhere?
;; (defthm logext32reductions
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (and; (equal (logext 32 (* (logext 32 x) y))
;;                ;        (logext 32 (* x y)))
;;                ; (equal (logext 32 (* x (logext 32 y)))
;;                ;        (logext 32 (* x y)))
;;                 (equal (logext 32 (+ (logext 32 x) y))
;;                        (logext 32 (+ x y)))
;;                 (equal (logext 32 (+ x (logext 32 y)))
;;                        (logext 32 (+ x y)))))
;;   :hints (("Goal" :in-theory (enable)))
;;   )

;; (defthm logext32reductions-1
;;   (implies (and (integerp x) (integerp y))
;;            (equal (logext 32 (+ (logext 32 x) y))
;;                   (logext 32 (+ x y)))))






;bzo rename these to not mention 32...

;bzo handle this better
(defthm logext32hack
  (implies (and (integerp m)
                (integerp n)
                (integerp a)
                (integerp b))
           (equal (logext size (+ a b (* n (logext size m))))
                  (logext size (+ a b (* n m))))))

(defthm logext32hack-2
  (implies  (and (integerp m)
                 (integerp k)
                 (integerp a)
                 (integerp b))
            (equal (LOGEXT size (+ a b (- (* K (LOGEXT size m)))))
                   (LOGEXT size (+ a b (- (* K m))))))
  :hints (("Goal" :in-theory (disable logext32hack)
           :use (:instance logext32hack (n (- k)) (size 32)))))

(defthm logext32hack-3
  (implies  (and (integerp a)
                 (integerp b)
                 (integerp c)
                 (integerp d))
            (equal (LOGEXT size (+ a b (- (LOGEXT size c)) d))
                   (LOGEXT size (+ a b (- c) d)))))

(defthm logext32hack-4
  (implies  (and (integerp a)
                 (integerp b)
                 (integerp c)
                 (integerp d)
                 (integerp e)
                 (integerp i)
                 )
            (equal (LOGEXT size (+ a b c d (- (* I (LOGEXT size e)))))
                   (LOGEXT size (+ a b c d (- (* I e))))
                   )))

(defthm logext32hack-6
  (implies  (and
                 (integerp a)
                 (integerp b))
            (equal (LOGEXT size (+ (- (logext size a)) b))
                   (LOGEXT size (+ (- a) b)))))

(defthm logext32hack-7
  (implies  (and (integerp c)
                 (integerp a)
                 (integerp b))
            (equal (LOGEXT size (+ a (* b (logext size c))))
                   (LOGEXT size (+ a (* b c)))
                   )))

(defthm logext32hack-5
  (implies (and (integerp a)
                (integerp b)
                (integerp c)
                (integerp d)
                (integerp k)
                )
           (equal (LOGEXT size (+ a b (* k (LOGEXT size c)) d))
                  (LOGEXT size (+ a b (* k c) d)))))

(defthm logext32hack-8
  (implies (and (integerp a)
                (integerp b)
                (integerp c)
                (integerp d)
                (integerp k)
                )
           (equal (LOGEXT size (+ a b d (* k (LOGEXT size c))))
                  (LOGEXT size (+ a b (* k c) d)))))

(defthm logapp-recombine-logext-case
  (implies (and (<= n size) ;other case?
                (integerp size))
           (equal (logapp n x (logtail n (logext size x)))
                  (logext size x)))
  :hints (("Goal" :in-theory (enable equal-logapp-x-y-z))))

(defthm logapp-recombine-loghead-case
  (implies (and (<= n size) ;other case?
                (integerp size))
           (equal (logapp n x (logtail n (loghead size x))) ;the loghead might get dropped when we have better rules
                  (loghead size x)))
  :hints (("Goal" :in-theory (enable equal-logapp-x-y-z))))

;bzo - gen?
(defthm loghead-sum-weird
  (implies (and (integerp y)
                (integerp x)
                (integerp z)
                (<= n size)
                (integerp size)
                )
           (equal (loghead n (+ x y (- (logext size z))))
                  (loghead n (+ x y (- z)))))
  :hints (("Goal" :in-theory (disable loghead-of-sum-of-prod-of-loghead-lemma-better2
;                                      LOGHEAD-+-CANCEL-BETTER-ALT-1
;                                      loghead-+-cancel-better
;                                      loghead-sum-loghead
;                                     loghead-sum-loghead-alt
                                      meta-rule-eric
                                      loghead-+-loghead-better))))

(defthm logapp-chop-hack-1
  (implies (and (<= n size)
                (integerp size)
                (integerp y)
                (integerp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (logapp n (+ (- (logext size x)) y) z)
                  (logapp n (+ (- x) y) z)))
  :hints (("Goal" :in-theory (enable equal-logapp-x-y-z))))


(defthm hack-blah
  (implies (and (integerp i)
                (integerp z)
                (<= n size)
                (integerp size)
                )
           (equal (LOGHEAD n (* I (LOGEXT size Z)))
                  (LOGHEAD n (* I Z))))
  :hints (("Goal" :use ((:instance LOGHEAD-OF-PROD-LEMMA-ALT (x (LOGEXT size Z)) (y i))
                        (:instance LOGHEAD-OF-PROD-LEMMA-ALT (x Z) (y i)))
           :in-theory (disable LOGHEAD-OF-PROD-LEMMA-ALT))))


(defthm logapp-hack-3
  (implies (and (<= n size)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp w)
                (integerp v)
                (integerp i)
                (integerp size)
                (integerp n)
                (<= 0 n)
                )
           (equal (LOGAPP n (+ x y (- (* I (LOGEXT size z))) w) v)
                  (LOGAPP n (+ x y (- (* I z)) w) v)))
  :hints (("Goal" :in-theory (enable EQUAL-LOGAPP-X-Y-Z))))

(defthm logapp-hack-4
  (implies (and (<= m size)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp w)
                (integerp v)
                (integerp xx)
                (integerp n)
                (integerp size)
                (integerp m)
                (<= 0 m)
                )
           (equal (LOGAPP m (+ w v x y (* N (LOGEXT size z))) xx)
                  (LOGAPP m (+ w v x y (* N z)) xx))))

(defthm loghead-hack-blah
  (implies (and (integerp y)
                (integerp z)
                (<= 0 size)
                (integerp size))
           (equal (loghead size (+ (- (loghead size z)) y))
                  (loghead size (+ (- z) y))))
  :hints (("Goal" :in-theory (enable loghead-of-minus))))

(defthm loghead-cancel-sigh
  (implies (and (integerp a)
                (integerp j)
                (integerp k)
                (integerp k2))
           (equal (EQUAL (LOGHEAD size (+ J a))
                         (LOGHEAD size (+ k2 K a)))
                  (EQUAL (LOGHEAD size J)
                         (LOGHEAD size (+ k2 K))))))

;bzo add to super-ihs
;subst into logcar from loghead equality?
(defthm logext-subst2
  (implies (and (equal (loghead m x) (loghead m y)) ;y and m are free variables
                (syntaxp (smaller-term y x))
                (<= n m)
                (< 0 n)
                (integerp m)
;                (integerp y)
 ;               (integerp x)
                (integerp n)
                )
           (equal (logext n x)
                  (logext n y))))

(defthm logext-subst2-alt
  (implies (and (equal (loghead m x) (loghead m y)) ;y and m are free variables
                (syntaxp (smaller-term y x))
                (<= n m)
                (< 0 n)
                (integerp m)
;                (integerp y)
;               (integerp x)
                (integerp n)
                )
           (equal (logext n x)
                  (logext n y))))


;; ;need a generalized version of EQUAL-OF-LOGHEADS-OF-WHEN-ONE-IS-ONE-LONGER
;; (defthm equal-of-two-logexts-rewrite-helper
;;   (implies (and (integerp n)
;;                 (< 0 n)
;;                 (integerp m)
;;                 (< 0 m))
;;            (equal (equal (logext m a)
;;                          (logext n b))
;;                   (equal (loghead m a)
;;                          (loghead n b))))
;;   :hints (("Goal" :in-theory (e/d (logext
;; ;                                   loghead-split-special
;; ;                                  logbit ;bzo
;; ;                                 equal-of-logheads-split
;;                                    )
;;                                   ()))))

;trying...
;looped...
;(in-theory (disable PLUS-OF-LOGAPP-SUCK-IN-GEN))

(defthm equal-of-logexts-of-when-one-is-one-longer
  (implies (and (equal m (+ 1 n))
                (integerp n)
                (< 0 n))
           (equal (equal (logext m x)
                         (logext n y))
                  (and (equal (logbit (+ -1 n) y) (logbit n x))
                       (equal (loghead n x)
                              (loghead n y)))))
  :hints (("Goal" :in-theory (enable logext
                                     logbit
                                     LOGHEAD-SUBST-SIMPLER-2
                                     ))))

;do we need this -alt version?
(defthm equal-of-logexts-of-when-one-is-one-longer-alt
  (implies (and (equal m (+ 1 n))
                (integerp n)
                (< 0 n))
           (equal (equal (logext n y)
                         (logext m x))
                  (and (equal (logbit (+ -1 n) y) (logbit n x))
                       (equal (loghead n x)
                              (loghead n y)))))
  :hints (("Goal" :by  equal-of-logexts-of-when-one-is-one-longer)))


;; SHOW-BITS

;; Utility function to show the bits
;; in a positive number.

(defun show-bits-aux (i l)
  ;; only works for a positive number
  (if (zp i)
      l
    (show-bits-aux (floor i 2)
              (cons (if (evenp i) 0 1)
                    l))))

;; Used to be called bits but it was renamed, since a really important function
;; in rtl/ is named bits (and maybe we will someday try to unify super-ihs/
;; and rtl/)? -ews
;;
(defun show-bits (i)
  (show-bits-aux i nil))

;; ;bzo gen!
;; ;make an alt form for when loghead and logtail are switched?
;; ;see logapp-recombine-loghead-case
;; (defthm logapp-recollapse
;;   (equal (logapp 16 val (loghead 16 (logtail 16 val)))
;;          (loghead 32 val))
;;   :hints (("Goal" :in-theory (e/d (logtail-loghead-better
;;                                      equal-logapp-x-y-z)
;;                                   (loghead-logtail)))))

(defthm logapp-recollapse
  (implies (and (<= 0 m)
                (<= 0 n)
                (integerp n)
                (integerp m))
           (equal (logapp n val (loghead m (logtail n val)))
                  (loghead (+ n m) val)))
  :hints (("Goal" :in-theory (e/d (logtail-loghead-better
                                   equal-logapp-x-y-z)
                                  (loghead-logtail)))))



;gets rid of annoying and unhelpful hyps like (<= x x) and conclusions like (< x x).
(defthm dumb
  (not (< M M)))

(defthm multiply-by-negative-integer-linear
  (IMPLIES (AND (< X 0)
                (INTEGERP X)
                (<= 0 y)
                (rationalp y)
                )
           (<= (* X y)
               (* -1 y)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT
                                      MOVE-NEGATED-TERM-TO-OTHER-SIDE-OF-<-TERM-1-ON-LHS))))

(defthm multiply-by-positive-integer-linear
  (implies (and (< 0 x)
                (integerp x)
                (rationalp y)
                (<= 0 y)
                )
           (<= (* y) (* x y)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable functional-commutativity-of-minus-*-left
                                      move-negated-term-to-other-side-of-<-term-1-on-lhs))))

;; (defthm hackarith
;;  (IMPLIES (AND (<= X -1)
;;                (INTEGERP X)
;;                (INTEGERP M)
;;                (<= 0 M)
;;                (INTEGERP OFF)
;;                (<= 0 OFF)
;;                (< OFF (EXPT 2 M))
;;                (< 0 M))
;;           (< (+ OFF (* X (EXPT 2 M)))
;;              0))
;;  :rule-classes :linear
;;  )

(defthmd tiny-addend-doesnt-matter-when-comparing-integers
  (implies (and (integerp x)
                (integerp y)
                (<= 0 off)
                (< off 1))
           (equal (< (+ off x) y)
                  (< x y))))


(defthmd non-multiple-addend-doesnt-matter-when-comparing-multiples
  (implies (and (integerp z)
                (integerp x)
                (integerp y)
                (integerp (/ z y))
                (integerp (/ x y))
                (integerp off)
                (<= 0 off)
                (< off y))
           (equal (< (+ OFF x) z)
                  (< x z)))
  :hints (("Goal" :use (:instance tiny-addend-doesnt-matter-when-comparing-integers
                                  (off (/ off y))
                                  (x (/ x y))
                                  (y (/ z y)))))
  )


(defthmd compare-of-add-to-shifted
  (implies (and (unsigned-byte-p m off)
                (not (equal 0 x))
                (integerp x)
                (integerp m)
                (integerp n)
                )
           (equal (< (+ off (* x (expt 2 m))) (expt 2 n))
                  (< (* x (expt 2 m)) (expt 2 n))))
  :otf-flg t
  :hints (("subgoal 2" :use (:instance non-multiple-addend-doesnt-matter-when-comparing-multiples
                                       (x (* x (expt 2 m)))
                                       (y (expt 2 m))
                                       (z (expt 2 n))
                                       )
           )
          ("Goal" :cases ((< x 0))
           :in-theory (enable unsigned-byte-p))))

(defthmd compare-of-add-to-shifted-neg
  (IMPLIES (AND (INTEGERP X)
                (not (equal 0 x))
                (unsigned-byte-p m off)
                (INTEGERP M)
                (INTEGERP N)
                (<= m n) ;gen?
;                (<= 0 M)
;                (<= 0 N)
                )
           (equal (< (+ off (* X (EXPT 2 M))) (- (EXPT 2 n)))
                  (< (* X (EXPT 2 M)) (- (EXPT 2 n)))))
  :otf-flg t
  :hints (("subgoal 1" :use (:instance non-multiple-addend-doesnt-matter-when-comparing-multiples
                                       (x (* X (EXPT 2 M)))
                                       (y (EXPT 2 M))
                                       (z (- (EXPT 2 N)))
                                       )
           )
          ("Goal"
           :cases ((< x 0))
           :in-theory (enable UNSIGNED-BYTE-P))))


(defthmd arithhack3
  (IMPLIES (AND (< 0 y)
                (rationalp x)
                (rationalp y)
                (rationalp z)
                )
           (equal (< (+ X (* (/ y) z)) 0)
                  (< (+ z (* X y)) 0)))
  :hints (("Goal" :use (:instance <-*-LEFT-CANCEL
                                  (z y)
                                  (x (+ X (* (/ y) z)))
                                  (y 0))
           :in-theory (disable <-*-LEFT-CANCEL))))


(defthmd arithhack4
  (IMPLIES (AND (<= X 0)
                (NOT (EQUAL 0 X))
                (rationalp X)
                (INTEGERP M)
                (INTEGERP N)
                (<= 0 M)
;                (<= 0 N)
                )
           (equal (< (+ (EXPT 2 n) (* X (EXPT 2 M))) 0)
                  (< (+ X (EXPT 2 (+ (- M) N))) 0)))
  :hints (("Goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED  arithhack3))))


(encapsulate
 ()
 (local (defthm signed-byte-p-of-logapp-fw
          (implies (and (< m n) ;gen?
                        (integerp x)
                        (integerp m)
                        (integerp n)
                        (<= 0 m)
                        )
                   (implies (signed-byte-p n (logapp m offset x))
                            (signed-byte-p (- n m) x)))
          :otf-flg t
          :hints (("Subgoal 2" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED
                                                  signed-byte-p
                                                  logapp
                                                  arithhack4
                                                  compare-of-add-to-shifted
                                                  compare-of-add-to-shifted-neg))
                  ("Goal" :cases ((< 0 x)
                                  (= 0 x))
                   :in-theory (e/d (signed-byte-p
                                    logapp
                                    arithhack4
                                    compare-of-add-to-shifted
                                    compare-of-add-to-shifted-neg
                                    )
                                   ())))))


 (local (defthm signed-byte-p-of-logapp-bk
          (implies (and (< m n) ;gen?
                        (integerp x)
                        (integerp m)
                        (integerp n)
                        (<= 0 m)
                        )
                   (implies (signed-byte-p (- n m) x)
                            (signed-byte-p n (logapp m offset x))))
          :otf-flg t
          :hints ( ;bzo gross subgoal hint
                  ("Subgoal 2.1" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED
                                                    signed-byte-p
                                                    logapp
                                                    arithhack4
                                                    compare-of-add-to-shifted
                                                    compare-of-add-to-shifted-neg))
                  ("subgoal 3" :in-theory (e/d (signed-byte-p
                                                logapp
                                                compare-of-add-to-shifted
                                                arithhack4) ( ))
                   :use (:instance non-multiple-addend-doesnt-matter-when-comparing-multiples
                                   (x (* X (EXPT 2 M)))
                                   (y (EXPT 2 M))
                                   (off (LOGHEAD M OFFSET))
                                   (z (- (EXPT 2 (+ -1 N))))
                                   )
                   )
                  ("Goal" :cases ((< 0 x)
                                  (= 0 x))
                   :in-theory (e/d (signed-byte-p
                                    logapp
                                    arithhack4
                                    compare-of-add-to-shifted
                                    compare-of-add-to-shifted-neg
                                    )
                                   ())))))

 (defthm signed-byte-p-of-logapp
   (implies (and (< m n) ;gen?
                 (integerp m)
                 (integerp n)
                 (<= 0 m)
                 )
            (equal (signed-byte-p n (logapp m offset x))
                   (signed-byte-p (- n m) (ifix x))))
   :hints (("Goal" :use ((:instance signed-byte-p-of-logapp-bk)
                         (:instance signed-byte-p-of-logapp-fw))
            :in-theory (disable signed-byte-p-of-logapp-fw signed-byte-p-of-logapp-bk)))

   :otf-flg t
   ))

(defthm logext-subst-with-loghead
  (implies (and (equal (loghead m x)
                       y)
                (syntaxp (smaller-term y x))
                (<= n m)
                (< 0 n)
                (integerp m)
                (integerp n))
           (equal (logext n x)
                  (logext n y))))


;bzo gen
(defthmd loghead-equal-to-divides
  (implies (and (integerp a) (integerp b))
           (equal (equal (loghead 16 a) (loghead 16 b))
                  (divides (expt 2 16) (- a b))))
  :hints (("Goal" :in-theory (enable loghead))))

;bzo gen
(defthmd loghead-equal-to-divides2
  (implies (and (integerp a) (integerp b))
           (equal (equal 0 (loghead 16 a))
                  (divides (expt 2 16) a)))
  :hints (("Goal" :in-theory (enable loghead))))




;bzo gen?
(defthm loghead8-plus-times-256
  (implies (and (integerp x) ;(unsigned-byte-p 8 x)
                (integerp y))
           (equal (loghead 8 (+ x (* 256 y)))
                  (loghead 8 x))))

;bzo gen
(defthm usb-lemma
  (implies (and (unsigned-byte-p 16 x)
                (unsigned-byte-p 15 y))
           (unsigned-byte-p 31 (+ x (* 65536 y))))
  :hints (("Goal" :in-theory (enable sum-with-shift-becomes-logapp-constant-version))))

;EQUAL-LOGEXT-0 looped!

;bzo move hyps to conclusion
(defthm signed-byte-p-of-minus-2-to-the-size-minus-one
  (implies (and (integerp size) (< 0 size))
           (signed-byte-p size (- (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (enable signed-byte-p))))

;move?
(defthm logext-of-2-to-the-size-minus-one
  (implies (and (integerp size) (< 0 size))
           (equal (logext size (expt 2 (+ -1 size)))
                  (-  (expt 2 (+ -1 size)))))
  :hints (("Goal" :in-theory (e/d (logext EQUAL-LOGAPP-X-Y-Z)
                                  (logapp-subst-in-first-arg ;LOGAPP-HACK2 ;bzo
                                   )))))

;bzo gen
(defthmd minus-of-logext
  (implies (and (integerp size)
                (< 0 size)
                )
           (equal (- (logext size i))
                  (if (equal (expt 2 (+ -1 size)) (loghead size i)) ; (integerp (* i (/ (expt 2 (- size 1)))))
                      (expt 2 (+ -1 size))
                    (logext size (- i)))))
  :hints (("Goal" :use ((:instance LOGEXT-LOGHEAD (n size) (m size) (x i)))
           :in-theory (e/d (ASH-1-EXPT-REWRITE)
                           (LOGEXT-LOGHEAD
                            DUMB ;why?!
                            )))))

(theory-invariant (incompatible (:rewrite logext-minus) (:rewrite minus-of-logext)))

(defthmd lognot-of-logext
  (implies (and (integerp x)
                (integerp n)
                (< 0 n))
           (equal (lognot (logext n x))
                  (logext n (lognot x)))))

(theory-invariant (incompatible (:rewrite logext-lognot) (:rewrite lognot-of-logext)))


;bzo gen!
(defthm LOGAPP-of-sum-of-loghead-one
  (implies (and (integerp off1)
                (integerp off2))
           (equal (LOGAPP 16 (+ (LOGHEAD 16 OFF2) OFF1) CENV)
                  (LOGAPP 16 (+ OFF2 OFF1) CENV)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm LOGAPP-of-sum-of-loghead-two
  (implies (and (integerp off1)
                (integerp off2))
           (equal (LOGAPP 16 (+ OFF1 (LOGHEAD 16 OFF2)) CENV)
                  (LOGAPP 16 (+ OFF2 OFF1) CENV)))
  :hints (("Goal" :use (:instance  LOGAPP-of-sum-of-loghead-one)
           :in-theory (disable  LOGAPP-of-sum-of-loghead-one))))

(defthm logext-of-logext
  (implies (and (<= size1 size2)
                (integerp size1)
                (integerp size2)
                (< 0 size1))
           (equal (logext size1 (logext size2 x))
                  (logext size1 x))))

(defthmd loghead-split-when-usb-one-longer
  (implies (and (unsigned-byte-p (+ 1 n) x)
                (integerp n)
                )
           (equal (loghead n x)
                  (- x (* (expt 2 n) (logbit n x)))))
  :hints (("Goal" :use (:instance LOGAPP-LOGBIT-REASSEMBLE (a x))
           :in-theory (e/d (logapp) (LOGAPP-LOGBIT-REASSEMBLE)))))

(defthm equality-of-logheads-rewrite
  (IMPLIES (AND (UNSIGNED-BYTE-P (+ 1 n) X)
                (UNSIGNED-BYTE-P (+ 1 n) y)
                (equal (LOGBITP n X) (LOGBITP n Y))
                (integerp n)
                )
           (equal (EQUAL (LOGHEAD n X) (LOGHEAD n Y))
                  (equal x y)))
  :hints (("Goal" :in-theory (enable loghead-split-when-usb-one-longer LOGBIT))))

(defthm <-of-logheads-rewrite
  (implies (and (unsigned-byte-p (+ 1 n) x)
                (unsigned-byte-p (+ 1 n) y)
                (equal (logbitp n x) (logbitp n y))
                (integerp n)
                )
           (equal (< (loghead n x) (loghead n y))
                  (< x y)))
  :hints (("Goal" :in-theory (enable logbit loghead-split-when-usb-one-longer))))

;could associating logapp the other way help?
(defthm logapp-hack-yuck
  (equal (logapp 17 (logapp 1 a (loghead 16 x)) y)
         (logapp 17 (logapp 1 a x) y)))

(defthm logapp-hack-yuck2
  (implies (integerp x)
           (equal (logapp 17 (logapp 1 a (+ z (loghead 16 x))) y)
                  (logapp 17 (logapp 1 a (+ z x)) y))))


;see the non-2 version
(defthm logapp-subst-in-first-arg-2
  (implies (and (equal (loghead size free) (loghead size offset))
                (syntaxp (smaller-term free offset))
                )
           (equal (logapp size offset denvr)
                  (logapp size free denvr))))


(defthmd loghead-0-hack
 (implies (and (equal (loghead 16 offset1)
                      (loghead 16 offset2))
               (integerp offset1)
               (integerp offset2))
          (equal (LOGHEAD 16 (+ OFFSET1 (- OFFSET2)))
                 0)))



;; (thm
;;  (implies (integerp x)
;;           (equal (unsigned-byte-p 16 (loghead 31 x))
;;                  (equal 0 (logtail 16 (loghead 31 x)))))
;;  :hints (("Goal" :in-theory (disable logtail-16-loghead-32))))

;gen to have an x and a y?
;the RHS is our current prefered way to say that a range of bits is 0.
;but what about LOGTAIL-EQUAL-0?  disable it, or don't let it apply to logheads?
(defthm loghead-equal-loghead-longer
  (implies (and (integerp size1)
                (<= size2 size1)
                )
           (equal (equal (loghead size1 x) (loghead size2 x))
                  (equal (logtail size2 (loghead size1 x)) 0)))
  :otf-flg t
  :hints (("Goal" :use ((:instance loghead-split-gen
                                   (n size1)
                                   (m size2)
                                   )
                        (:instance equal-logapp-x-y-z
                                   (n size2)
                                   (y (logtail size2 (loghead size1 x)))
                                   (z  (loghead size1 x))))

           :in-theory (e/d (loghead-equal-rewrite)
                           (equal-logapp-x-y-z
                            equal-logapp-x-y-z-constants
                            LOGAPP-RECOMBINE-LOGHEAD-CASE
                            logtail-equal-0)))))

;keep disabled!
(defthmd logext-split-gen
  (implies (and (integerp n)
                (<= m n)
                (integerp m)
                (<= 0 m))
           (equal (logext n x)
                  (logapp m x (logtail m (logext n x))))))

;gen the 0?
(defthm logtail-logext-equal-0-rewrite
  (implies (and (< size2 size1) ;can't gen...
                (<= 0 size2)
                (integerp size1)
                (integerp size2)
                )
           (equal (equal (logtail size2 (logext size1 x)) 0)
                  (equal (logtail size2 (loghead size1 x)) 0)))
  :hints (("Goal" :in-theory (e/d (LOGTAIL-LOGHEAD-BETTEr
                                   LOGEXT-SUBST-WITH-LOGHEAD
                                   LOGTAIL-LOGEXT)
                                  (LOGTAIL-EQUAL-0
                                   LOGEXT-LOGTAIL
                                   LOGHEAD-LOGTAIL)))))

(defthm loghead-equal-logext-longer
  (implies (and (integerp size1)
                (<= size2 size1)
                (integerp size2)
                (< 0 size2)
                )
           (equal (equal (logext size1 x) (loghead size2 x))
                  (equal (logtail size2 (logext size1 x)) 0)))
  :otf-flg t
  :hints (("Goal" :use ((:instance logext-split-gen
                                   (n size1)
                                   (m size2)
                                   )
                        (:instance equal-logapp-x-y-z
                                   (n size2)
                                   (y (logtail size2 (logext size1 x)))
                                   (z  (logext size1 x))))

           :in-theory (e/d (loghead-equal-rewrite)
                           (LOGAPP-RECOMBINE-LOGEXT-CASE
                            equal-logapp-x-y-z
                            equal-logapp-x-y-z-constants
                            logtail-equal-0)))))

;loghead-equal-logext-longer and logtail-logext-equal-0-rewrite together do what this does...
;; ;has a loghead instead of a logext in the RHS
;; (defthm loghead-equal-logext-longer2
;;   (implies (and (integerp size1)
;;                 (< size2 size1)
;;                 (integerp size2)
;;                 (< 0 size2)
;;                 )
;;            (equal (equal (logext size1 x) (loghead size2 x))
;;                   (equal (logtail size2 (loghead size1 x)) 0)))
;;   :hints (("Goal" :in-theory (disable LOGTAIL-EQUAL-0))))




;how do free variable get handled here?
(defthm expt-weakly-monotonic-linear
  (IMPLIES (<= (ifix SIZE) (ifix SIZE1))
           (<= (EXPT 2 SIZE)
               (EXPT 2 SIZE1)))
  :rule-classes :linear)

(defthm prod-non-negative-linear
  (implies (and (<= 0 x)
                (<= 0 y)
                (rationalp x)
                (rationalp y)
                )
           (<= 0 (* x y)))
  :rule-classes :linear
  )

(defthm prod-linear
  (implies (and (<= 0 x)
                (<= 1 y)
                (rationalp x)
                (rationalp y)
                )
           (<= x (* x y)))
  :rule-classes :linear
  )

(defthm prod-linear-alt
  (implies (and (<= 0 x)
                (<= 1 y)
                (rationalp x)
                (rationalp y)
                )
           (<= x (* y x)))
  :rule-classes :linear
  )

;make a lemma to handle both cases?
(defthm usb-of-logapp-2-gen
  (implies (and (integerp y)
                (<= size size1)
                (integerp size1)
                (integerp size)
                (<= 0 size1)
                (<= 0 y))
           (equal (unsigned-byte-p size (logapp size1 x y))
                  (and (equal y 0)
                       (unsigned-byte-p size (loghead size1 x)))))
  :hints (("Goal" :use (:instance expt-weakly-monotonic-linear)
           :in-theory (e/d (logapp UNSIGNED-BYTE-P
                                   )
                           (EXPT-IS-WEAKLY-INCREASING-FOR-BASE>1
                            EXPT-COMPARE)))))


;make an -alt version?


(defthm logtail-of-sum-of-ash
  (implies (unsigned-byte-p n k)
           (equal (logtail n (+ k (ash x n)))
                  (ifix x)))
  :hints (("Goal" :cases ((and (integerp n)
                               (<= 0 n)))
           :in-theory (e/d (ash-as-logapp)
                           (logapp-0-part-2-better)))))

(defthm logtail-of-sum-of-ash-alt
  (implies (unsigned-byte-p n k)
           (equal (logtail n (+ (ash x n) k))
                  (ifix x))))

;gen the -1...
(defthm logtail-of-sub1-of-ash
  (implies (and (natp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (logtail n (+ -1 (ash x n)))
                  (+ -1 x)))
  :hints (("Goal" :in-theory (e/d (LOGTAIL-OF-ONE-LESS-THAN-X) ( LOGAPP-0-PART-2-BETTER)))) )

;gen the -1?
(defthm logtail-of-sub1-of-logapp
  (implies (and (natp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (logtail 16 (+ -1 (logapp 16 0 x)))
                  (+ -1 x)))
  :hints (("Goal" :in-theory (e/d (LOGTAIL-OF-ONE-LESS-THAN-X) ( LOGAPP-0-PART-2-BETTER)))))

;i might be (+ x 65532) with x known to be >=4 and n=16
;bzo disable? might be expensive?  or we might want to keep the logheads around?

(defthmd loghead-identity-2
  (implies (and (unsigned-byte-p n (- i (expt 2 n)))
                (integerp i)
                )
           (equal (loghead n i)
                  (- i (expt 2 n))))
  :hints (("Goal" :in-theory (disable loghead-identity
                                      loghead-does-nothing-rewrite
                                      )
           :use (:instance loghead-identity (size n) (i (- i (expt 2 n)))))) )

;see also DIFFERENCE-UNSIGNED-BYTE-P
(defthm unsigned-byte-p-becomes-inequality
  (implies (and (unsigned-byte-p 16 x)
                (<= 0 k)
                (integerp k))
           (equal (unsigned-byte-p 16 (+ (- k) x))
                  (<= k x))))

(defthm unsigned-byte-p-becomes-inequality-alt
  (implies (and (unsigned-byte-p 16 x)
                (<= 0 k)
                (integerp k))
           (equal (unsigned-byte-p 16 (+ x (- k)))
                  (<= k x))))

(defthmd usb-of-sum-with-two-other-addends-hack
  (implies (and (unsigned-byte-p n x)
                (<= (+ a b) 0)
                (<= (- (+ a b)) x)
                (integerp a)
                (integerp b)
                (integerp x)
                )
           (unsigned-byte-p n (+ a b x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;move to loghead
(defthm loghead-of-prod-lemma-alt-gen
  (implies (and (<= n n2)
                (integerp y)
                (integerp n)
                (integerp n2)
                )
           (equal (loghead n (* y (loghead n2 x)))
                  (loghead n (* (ifix x) y))))
  :otf-flg t
  :hints (("Goal" :use ((:instance loghead-of-prod-lemma-alt (x (loghead n2 x)))
                        (:instance loghead-of-prod-lemma-alt))
           :in-theory (disable loghead-of-prod-lemma-alt))))

(defthm loghead-times-16-of-logapp
  (implies (integerp numwords)
           (equal (loghead (* 16 numwords) (logapp 16 x y))
                  (if (zp numwords)
                      0
                    (logapp 16 x (loghead (* 16 (+ -1 numwords)) y)))))
  :hints (("Goal" :cases ((<= 1 numwords))
           :in-theory (enable ;logapp
                       ))))

(defthm loghead-of-minus-compare-when-usb
  (implies (and (unsigned-byte-p n x)
                (integerp k)
                (< 0 k) ;drop (put loghead in concl?)
                )
           (equal (< (loghead n (- x)) k)
                  (or (equal x 0)
                      (< (- (expt 2 n) k) x))))
  :hints (("Goal" :in-theory (enable loghead-of-minus))))

;why did this suddenly become necessary?
(defthm logbit-too-big-no-free-vars
  (implies (unsigned-byte-p n x)
           (equal (logbit n x)
                  0))
  :hints (("Goal" :in-theory (enable logbit logbitp))))

;change to say quotep k?
(defthmd loghead-of-one-less-than-x-alt
  (implies (and (syntaxp (not (quotep x)))
                (equal k (+ -1 (expt 2 n)))
                (integerp x)
                (<= 0 n))
           (equal (loghead n (+ k x))
                  (if (equal (loghead n x) 0)
                      (+ -1 (expt 2 n))
                    (+ -1 (loghead n x)))))
  :hints (("Goal" :in-theory (enable LOGHEAD-+-EXPT)
           :use (:instance loghead-of-one-less-than-x))))

(defthm loghead-of-1
  (equal (loghead size 1)
         (if (zp size)
             0
           1)))

;change to say quotep k?
(defthmd loghead-of-one-less-than-x-alt-non-splitting
  (implies (and (syntaxp (not (quotep x)))
                (equal k (+ -1 (expt 2 n)))
                (< 0 (loghead n x))
                (integerp x)
                (<= 0 n)
                )
           (equal (loghead n (+ k x))
                  (+ -1 (loghead n x))))
  :hints (("Goal" :in-theory (enable loghead-of-one-less-than-x-alt zp))))

;k can be 2^size - 1 is k is an integer..
(defthm loghead-not-greater-than-big-constant
  (implies (and (syntaxp (quotep k))
                (<= (expt 2 size) k)
                )
           (equal (< k (LOGHEAD size i))
                  nil)))


;can this loop?
(defthm loghead-sum-subst-helper-better
  (implies (and (equal (loghead n x) y)
                (syntaxp (and (term-order y x)
                              (not (equal y x))))
                (integerp z))
           (equal (loghead n (+ x z))
                  (if (integerp x)
                      (loghead n (+ y z))
                      (if (acl2-numberp x) 0 (loghead n z)))))
  :hints
  (("Goal" :in-theory
    (enable loghead-+-loghead))))


(defthm loghead-one-more-wraps-around
  (implies (and (syntaxp (not (quotep x))) ;acl2 will unifies (+ 1 x) with a constant!
                (<= y (loghead width x))
                (integerp y)
                (integerp x)
                (<= 0 width)
                (integerp width)
                )
           (equal (< (loghead width (+ 1 x)) y)
                  (and (equal (+ -1 (expt 2 width)) (loghead width x))
                       (< 0 y)
                       )))
  :hints (("Goal" :in-theory (enable loghead-of-one-more-than-x))))

;restrict with (syntaxp (quotep bigconst)) ?
(defthm loghead-identity-2-alt
  (implies (and (< bigconst 65536)
                (unsigned-byte-p 16 i)
                (<= (- 65536 bigconst) i) ;most likely to fail?
                (<= 0 bigconst)
                (integerp bigconst)
                )
           (equal (loghead 16 (+ bigconst i))
                  (+ (- bigconst 65536) i)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d ( loghead-sum-split-into-2-cases )
                                  ( ;loghead-identity
 ;                                  unsigned-byte-p-of-x-minus-1 ;looped!
                                   loghead-does-nothing-rewrite
                                   )))))


;move
;since acl2 sometimes "throws away" type information...
(defthmd loghead-sum-split-into-2-cases-forced
  (implies (and (force (integerp i))
                (force (integerp j))
                )
           (equal (loghead n (+ i j))
                  (if (< (+ (loghead n i) (loghead n j))
                         (expt 2 n))
                      (+ (loghead n i) (loghead n j))
                    (+ (loghead n i)
                       (loghead n j)
                       (- (expt 2 n))))))
  :hints
  (("Goal"
    :in-theory (disable loghead-split-into-2-cases)
    :use (:instance loghead-split-into-2-cases (n n)
                    (x (+ (loghead n i) (loghead n j)))))))


(defthm loghead-equality-impossible
  (implies (and (syntaxp (and (quotep k1)
                              (quotep k2)))
                (not (equal 0 (loghead 16 (+ k1 k2))))
                (unsigned-byte-p 16 x) ;not needed?
                (unsigned-byte-p 16 k1)
                (unsigned-byte-p 16 k2)
                )
           (equal (equal x (+ k1 (loghead 16 (+ k2 x)))) ;note that x appears twice in LHS
                  nil))
  :hints (("Goal" :in-theory (e/d (loghead-sum-split-into-2-cases
                                   loghead-of-minus)
                                  (unsigned-byte-p-loghead-forward-chaining
;loghead-type
;(:type-prescription loghead)
                                   )))))


;bzo put the events below where they go

;rename
;bzo can we get this with type reasoning?
(defthm not-unsigned-byte-p-when-j-is-negative
  (implies (and (< j 0)
                (integerp i)
                (integerp j)
                )
           (not (UNSIGNED-BYTE-P n (LOGAPP m i j)))))

(defthm loghead-lower-bound-when-top-bit-one
  (implies (and (logbitp (+ -1 n) x)
                (integerp n)
                (< 0 n)
                (integerp x))
           (<= (expt 2 (+ -1 n)) (loghead n x)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable loghead-when-know-top-bit ))))

(defthm loghead-upper-bound-when-top-bit-one
  (implies (and (not (logbitp (+ -1 n) x))
                (integerp n)
                (< 0 n)
                (integerp x))
           (< (loghead n x) (expt 2 (+ -1 n))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable loghead-when-know-top-bit ))))

(defthm unsigned-byte-p-of-logext-same-size
  (implies (and (integerp x)
                (< 0 n)
                )
           (equal (unsigned-byte-p n (logext n x))
                  (and (< (loghead n x) (expt 2 (+ -1 n)))
                       (integerp n))))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logapp-reassemble
  (equal (logapp n i (logtail n i))
         (ifix i)))

(defthmd loghead-plus-logtail-reassemble
  (implies (natp n)
           (equal (+ (loghead n x) (* (expt 2 n) (logtail n x)))
                  (ifix x)
                  ))
  :hints (("Goal" :use (:instance logapp-reassemble (i x))
           :in-theory (e/d (LOGAPP)
                           (logapp-reassemble
                            EQUAL-LOGAPP-X-Y-Z-CONSTANTS
                            LOGAPP-DOES-NOTHING-REWRITE))))
  )

(defthm x-equal-sum-of-loghead-cancel
  (implies (and (integerp x)
                (integerp y)
                (natp n)
                )
           (equal (EQUAL X (+ y (LOGHEAD n X)))
                  (EQUAL (* (expt 2 n) (logtail n x)) y)))
  :hints (("Goal" :use (:instance loghead-plus-logtail-reassemble)
           :in-theory (disable loghead-plus-logtail-reassemble)))
  )

(defthm logapp-of-minus-one-plus-expt2n
  (implies (natp n)
           (equal (+ (expt 2 n) (logapp n x -1))
                  (loghead n x)))
  :hints (("Goal" :in-theory (enable logapp)))
  )

(defthm logapp-of-minus-one-plus-expt2n-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (natp n))
           (equal (+ k (logapp n x -1))
                  (loghead n x)))
  :hints (("Goal" :in-theory (enable logapp)))
  )

(defthm signed-byte-p-of-x-minus-2-to-then-minus-one-when-usb
  (IMPLIES (AND (UNSIGNED-BYTE-P (+ -1 N) X)
                (INTEGERP N)
                (< 0 N))
           (SIGNED-BYTE-P N (+ X (- (EXPT 2 (+ -1 N))))))
  :hints (("Goal" :in-theory (enable SIGNED-BYTE-P
                                     unSIGNED-BYTE-P
                                     EXPONENTS-ADD-UNRESTRICTED))))

(defthm logext-of-x-plus-2-to-the-n-minus-one
  (implies (and (unsigned-byte-p n x)
                (integerp n)
                (< 0 n))
           (equal (logext n (+ (expt 2 (+ -1 n)) x))
                  (+ (- (expt 2 (+ -1 n))) x)))
  :hints (("Goal" :in-theory (enable logext logbitp-+-expt-n-rewrite))))

(defthm logext-of-x-plus-2-to-the-n-minus-one-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (+ -1 n)))
                (unsigned-byte-p n x)
                (integerp n)
                (< 0 n))
           (equal (logext n (+ k x))
                  (+ (- (expt 2 (+ -1 n))) x)))
  :hints (("Goal" :in-theory (enable logext logbitp-+-expt-n-rewrite))))

;gen!?
(defthm half-cancel
  (equal (+ x (- (* 1/2 x)) y)
         (+ (* 1/2 x) y)))

(defthm logext-plus-expt2n-rewrite
  (implies (and (unsigned-byte-p n x)
                (integerp n)
                (< 0 n))
           (equal (EQUAL x (+ (expt 2 n) (LOGEXT n x)))
                  (<= (expt 2 (+ -1 n)) x)))
  :hints (("Goal" :in-theory (enable logext
                                     logapp
                                     EXPONENTS-ADD-UNRESTRICTED))))

(defthm logext-plus-expt2n-rewrite-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (unsigned-byte-p n x)
                (integerp n)
                (< 0 n))
           (equal (EQUAL x (+ k (LOGEXT n x)))
                  (<= (expt 2 (+ -1 n)) x)))
  :hints (("Goal" :use (:instance  logext-plus-expt2n-rewrite)
           :in-theory (disable  logext-plus-expt2n-rewrite))))

;nice, general lemma
;but too powerful in some cases?
;i do like that it turns logext facts into loghead facts
(defthm logext-equal-rewrite
  (implies (and (integerp n)
                (< 0 n))
           (equal (equal (logext n x) k)
                  (and (signed-byte-p n k)
                       (equal (loghead n x)
                              (loghead n k))))))

(defthm unsigned-byte-p-of-minus-of-positive
  (implies (and (<= 0 x)
                (<= 0 size)
                (integerp size)
                )
           (equal (unsigned-byte-p size (- x))
                  (equal 0 (fix x)))))

;bzo move to super-ihs?  or just include better arithmetic?
(defthm move-negated-term-hack
  (implies (and (acl2-numberp y)
                (acl2-numberp z))
           (equal (equal (+ (- x) y) z)
                  (equal y (+ x z)))))

;generalize: if the logior of y and the lognot of z is not -1, then (equal (logior z x) y) = nil.

(defthm logior-hack
  (implies (and (not (logbitp 8 y))
                (integerp x) ;drop
                )
           (not (equal (logior 256 x) y)
                )))

(defthm logbitp-bound
  (implies (and (logbitp n x)
                (<= 0 x)
                (integerp n)
                (<= 0 n)
                ;(integerp x)
                )
           (<= (expt 2 n) x))
  :rule-classes ((:linear :trigger-terms ( (logbitp 31 x))))
  :hints (("Goal" :in-theory (enable logbitp))))


;; ;not sure this gives me what i want...
;; (defthm logbitp-31-linear
;;   (IMPLIES (AND (LOGBITP 31 X)
;;                 (<= 0 X)
;;                 (INTEGERP X))
;;            (<= (expt 2 31) x))
;;   :rule-classes ((:linear :trigger-terms ((LOGBITP 31 X))))
;;   :hints (("Goal" :in-theory (enable LOGBITP))))


(defthm ash-equal-rewrite
  (implies (and (integerp n)
                (<= 0 n))
           (equal (equal x (ash y n))
                  (and (integerp x)
                       (equal 0 (loghead n x))
                       (equal (ifix y) (logtail n x))))))

;trying a switch of the direction to associate logapp!  doing it this way
;means the sizes in the logapp nest are the sizes of their corresponding
;values, rather than sums of the sizes of several values
(defthm associativity-of-logapp-better-back
  (implies (and (integerp size2)
                (<= size size2)
                (integerp size)
                (<= 0 size))
           (equal (logapp size2 (logapp size i j) k)
                  (logapp size i (logapp (- size2 size) j k)))))

(in-theory (disable associativity-of-logapp-better))

(theory-invariant (incompatible (:rewrite associativity-of-logapp-better) (:rewrite associativity-of-logapp-better-back)))
(theory-invariant (incompatible (:rewrite associativity-of-logapp) (:rewrite associativity-of-logapp-better-back)))


;This one's :executable-counterpart stays enabled.
(defund expt-execute (r i) (expt r i))

;Allows expt calls with small exponents to be computed
;You can change 1000 to your own desired bound.
(defthmd expt-execute-rewrite
  (implies (and (syntaxp (and (quotep r) (quotep i) (< (abs (cadr i)) 1000))))
           (equal (expt r i)
                  (expt-execute r i)))
  :hints (("Goal" :in-theory (enable expt-execute))))

;Doing this here can cause problems (maybe with forward-chaining or some sort
;of lightweight reasoning where the rule above doesn't fire?).  Let's wait until we see an expensive call to expt and then use this stuff

;(in-theory (disable (:executable-counterpart expt))) ;prevents really expensive calls
;(in-theory (enable expt-execute-rewrite))

;disable and add priority?
;bzo move
(DEFTHMd logapp-equal-constant
  (IMPLIES (AND (SYNTAXP (QUOTEP Z))
;                (SYNTAXP (QUOTEP N))
                )
           (EQUAL (EQUAL (LOGAPP N X Y) Z)
                  (AND (INTEGERP Z)
                       (IF (INTEGERP X)
                           (EQUAL (LOGHEAD N X) (LOGHEAD N Z))
                           (EQUAL (ASH Y (NFIX N)) Z))
                       (IF (INTEGERP Y)
                           (EQUAL Y (LOGTAIL N Z))
                           (EQUAL Z (LOGHEAD N X))))))
  :HINTS (("Goal" :IN-THEORY (ENABLE EQUAL-LOGAPP-X-Y-Z))))

(defthm loghead-compare-to-max
  (implies (and (quotep k)
                (equal k (+ -1 (expt 2 n)))
                (natp n))
           (equal (< (loghead n x) k)
                  (not (equal (loghead n x) k)))))

;bzo gen
(defthm loghead-equal-max-plus-something-else
  (implies (and (syntaxp (not (equal y ''0))) ;will loop! ACL2 unifies 32767 with the term (+ 32767 y), binding y to 0)
                (<= 0 y)
                (integerp y))
           (equal (equal (loghead 15 x) (+ 32767 y))
                  (and (equal 0 y)
                       (equal 32767 (loghead 15 x))))))

(defthm loghead-plus-expt-as-third-addend
  (implies (and (integerp a)
                (integerp b))
           (equal (loghead width (+ a b (expt 2 width)))
                  (loghead width (+ a b))))
  :hints (("Goal" :use (:instance acl2::loghead-+-expt
                                  (acl2::n width)
                                  (acl2::x (+ a b))
                                  )
           :in-theory (disable acl2::loghead-+-expt))))

;;bzo gen
;;consider enabling with a syntaxp hyp to prevent loops?
(defthmd loghead-of-difference
  (implies (and (syntaxp (smaller-term b a))
                (integerp a)
                (integerp b))
           (equal (loghead 16 (+ a (- b)))
                  (if (equal (loghead 16 a) (loghead 16 b))
                      0
                    (- 65536 (loghead 16 (- b a))))))
  :rule-classes ((:rewrite :loop-stopper ((b a))))
  :hints (("Goal" :in-theory (enable loghead-sum-split-into-2-cases
                                     loghead-of-minus
                                     ))))

(defthmd loghead-of-difference-alt
  (implies (and (syntaxp (smaller-term b a))
                (integerp a)
                (integerp b)
                )
           (equal (loghead 16 (+ (- b) a))
                  (if (equal (loghead 16 a) (loghead 16 b))
                      0
                    (- 65536 (loghead 16 (- b a))))))
  :rule-classes ((:rewrite :loop-stopper ((b a))))
  :hints (("Goal" :in-theory (enable loghead-sum-split-into-2-cases
                                     loghead-of-minus
                                     ))))

(defthm hack<
  (implies (< x y)
           (not (equal x y)))
  :rule-classes ((:rewrite :backchain-limit-lst (0))))

;bzo gen
(defthm logapp-loghead-hack-16-31
  (implies (and (integerp a)
                (integerp b))
           (equal (logapp 16 (+ a (loghead 31 b)) c)
                  (logapp 16 (+ a b) c))))

;more like this?
(defthm logheads-of-sum-almost-equal
  (implies (and (equal (loghead n x)
                       (loghead n y))
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (equal (loghead n (+ z y))
                         (loghead n (+ z x)))
                  t)))

(defthm logheads-of-sum-almost-equal-alt
  (implies (and (equal (loghead n x)
                       (loghead n y))
                (integerp x)
                (integerp y)
                (integerp z))
           (equal (equal (loghead n (+ z y))
                         (loghead n (+ x z)))
                  t)))
;more like this?
(defthm loghead-of-sum-of-logapp
  (implies (and (<= m n)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp n)
                )
           (equal (loghead m (+ z (logapp n x y)))
                  (loghead m (+ z x)))))

;more like this?
(defthm loghead-of-sum-of-logapp-1
  (implies (and (<= m n)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp n)
                )
           (equal (loghead m (+ (logapp n x y) z))
                  (loghead m (+ z x)))))



;bzo gen the 0?
;; (defthm loghead-plus-constant-compare-to-zero
;;   (implies (and (syntaxp (quotep j))
;;                 (integerp x)
;;                 (integerp size)
;;                 (<= 0 size)
;;                 (integerp j)
;;                 )
;;            (equal (< 0 (loghead size (+ j x)))
;;                   (not (equal (loghead size (- j))
;;                               (loghead size x))))))

(defthm logapp-of-ash
  (implies (and (<= size c)
                (integerp c))
           (equal (logapp size (ash x c) y)
                  (logapp size 0 y))))

(defthm equal-logapp-with-logtail-of-self-rewrite
  (equal (equal y (acl2::logapp 16 x (acl2::logtail 16 y)))
         (and (integerp y)
              (equal (acl2::loghead 16 x)
                     (acl2::loghead 16 y))))
  :hints (("Goal" :in-theory (enable acl2::equal-logapp-x-y-z))))

(defthm logapp-equal-logapp-rewrite-special
  (equal (equal (acl2::logapp size i j)
                (acl2::logapp size i2 j))
         (or (not (integerp size))
             (< size 0)
             (equal (acl2::loghead size i)
                    (acl2::loghead size i2))))
  :hints (("Goal" :in-theory (enable acl2::equal-logapp-x-y-z))))

(defthm larger-loghead-isnt-less
  (implies (and (<= m n)
                (integerp n))
           (not (< (acl2::loghead n x) (acl2::loghead m x))))
  :hints (("Goal" :use (:instance ACL2::LOGAPP-LOGHEAD-LOGTAIL
                                  (acl2::i (acl2::loghead n x))
                                  (acl2::size m))
           :in-theory (e/d (acl2::logapp)
                           ( ACL2::LOGAPP-REASSEMBLE
                             ACL2::LOGAPP-LOGHEAD-LOGTAIL)))))

(defthm logapp-<-no-same-x
  (implies (and (integerp n)
                (<= 0 n)
                (integerp x)
                (integerp y)
                (integerp y2))
           (equal (< (acl2::logapp n x y) (acl2::logapp n x y2))
                  (< y y2)))
  :hints (("Goal" :in-theory (enable acl2::logapp-<))))
