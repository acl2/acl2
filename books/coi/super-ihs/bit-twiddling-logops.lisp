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
(include-book "logical-logops")

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; ash
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;



(defthm ash-logior
  (equal (ash (logior x y) n)
         (logior (ash x n) (ash y n)))
  :hints (("goal"
           :in-theory (e/d (LRDT zip) (ash*))
           :cases ((<= 0 n)))))

(in-theory (disable ash-as-logtail))


;move to ash?
(defthm ash-ash-right-to-ash
  (implies (and (<= n 0)
                (integerp n)
                (integerp m)
;                (integerp x)
                )
           (equal (ash (ash x m) n)
                  (ash x (+ m n))))
  :hints (("goal"
           :in-theory (e/d (LRDT expt2* ;ash
                                 ;logtail*-better
                                 ash-as-logtail
                                 ash-as-logapp
                                 open-logcons
                                 zip)
                           (logapp-0-part-2-better
                            EXPT-2-CRUNCHER)))))





;move
;never used
;; (defthmd exponents-add-bridge
;;   (implies (and (syntaxp (not (and (quotep i)
;;                                    (integerp (cadr i))
;;                                    (or (equal (cadr i) 1)
;;                                        (equal (cadr i) -1)))))
;;                 (syntaxp (not (and (quotep j)
;;                                    (integerp (cadr j))
;;                                    (or (equal (cadr j) 1)
;;                                        (equal (cadr j) -1)))))
;;                 (integerp x)
;;                 (not (equal 0 r))
;;                 (fc (acl2-numberp r))
;;                 (fc (integerp i))
;;                 (fc (integerp j)))
;;            (equal (expt r (+ x i j))
;;                   (* (expt r (+ x i)) (expt r j))))
;;   :hints (("goal" :use (:instance exponents-add (i (+ x i))))))


;; subsumed by ash-ash-right-to-ash
;; (defthm ash-ash-left
;;   (implies (and (integerp n)
;;                 (integerp m)
;;                 (integerp x)
;;                 (<= 0 m)
;;                 (<= 0 n))
;;            (equal (ASH (ASH x m) n)
;;                   (ash x (+ m n)))))
;;   :hints (("goal"
;;            :in-theory (enable LRDT ash-as-logtail ash-as-logapp))))

;; ;seems useless, and is proven instantly without hints.
;; (defthm ash-neg-of-unsigned-byte-p-bridge
;;   (implies (and (integerp n)
;;                 (< n 0)
;;                 (unsigned-byte-p (- n) (nth n1 (nth n2 x))))
;;            (equal (ash (nth n1 (nth n2 x)) n) 0)))
;;   :hints (("goal" :use (:instance ASH-GOES-TO-0
;;                                   (count (- n))
;;                                   (size (- n))
;;                                   (i x)))))

(defthm ash--1
  (equal (ash x -1)
         (logcdr x))
  :hints (("goal" :in-theory (enable ash
                                     logcons ;bzo?
                                     ))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logbitp, logbit
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm logbitp-logext
  (implies (and (integerp i)
                (integerp n)
;                (integerp x)
                (<= 0 i)
                (< 0 n))
           (equal (logbitp i (logext n x))
                  (if (< i n)
                      (logbitp i x)
                    (logbitp (1- n) x))))
  :hints (("goal"
           :in-theory (enable LRDT)
           :induct (sub1-sub1-logcdr-induction i n x))))

;; :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
;;            :induct (sub1-sub1-logcdr-induction i n x))))

;drop?
(defthm logbitp-+-logext-helper
  (implies (and (integerp i)
                (integerp n)
;                (integerp x)
                (integerp y)
                (<= 0 i)
                (< 0 n))
           (equal (logbitp i (logext n (+ x (logext n y))))
                  (logbitp i (logext n (+ x y)))))
  :rule-classes nil)

(defthm logbitp-+-logext
  (implies (and (integerp i)
                (integerp n)
;                (integerp x)
                (integerp y)
                (<= 0 i)
                (< i n))
           (equal (logbitp i (+ x (logext n y)))
                  (logbitp i (+ x y))))
  :hints (("goal" :use logbitp-+-logext-helper
           :in-theory (disable LOGEXT-+-LOGEXT-BETTER
                               ))))

;; We define a theory "overflow-bits" that simplifies expressions
;; involving overflow bits of added bit-vectors depending on the signs
;; of the bit-vector arguments.  We turn this theory off by default.

;bzo disable this stuff throughout and then enable selectively
(local (in-theory (disable SIGNED-BYTE-P-OF-LOGCDR
                           UNSIGNED-BYTE-P-OF-LOGCDR)))

(encapsulate
 ()


 (local
  (defthm logbitp-+-simple-helper
    (implies (and (integerp n)
                  (< 0 n)
                  (unsigned-byte-p 1 c)
                  (not (logbitp (1- n) x))
                  (signed-byte-p n x)
                  (signed-byte-p n y))
             (equal (logbitp n (+ x y c))
                    (and (logbitp n y) (logbitp (1- n) (+ x y c)))))
    :rule-classes nil
    :hints (("goal"
;:do-not '(generalize eliminate-destructors)
             :in-theory (e/d (LRDT open-logcons) (SIGNED-BYTE-P-OF-LOGCDR
                                                  LOGCONS-OF-0
                                                  ))))))
;             :induct (sub1-logcdr-logcdr-carry-induction n x y c)))))
;             :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)))))

 (defthm logbitp-+-simple
   (implies (and (signed-byte-p n x)
                 (signed-byte-p n y)
                 (not (logbitp (1- n) x)) ;rephrase?
                 (integerp n)
                 (< 0 n)
                 )
            (and (equal (logbitp n (+ x y))
                        (and (logbitp n y) (logbitp (1- n) (+ x y))))
                 (equal (logbitp n (+ y x))
                        (and (logbitp n y) (logbitp (1- n) (+ x y))))))
   :hints (("goal" :use (:instance logbitp-+-simple-helper (c 0))))))

(defthm logbitp-+-simple2-helper
  (implies (and (integerp n)
                (< 0 n)
                (unsigned-byte-p 1 c)
                (logbitp (1- n) x)
                (logbitp (1- n) y)
                (signed-byte-p n x)
                (signed-byte-p n y))
           (logbitp n (+ x y c)))
  :rule-classes nil
  :hints (("goal" :in-theory (e/d (LRDT open-logcons) (LOGCONS-OF-0)))))
;;            :induct (sub1-logcdr-logcdr-carry-induction n x y c))))
;;            :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY))))

(defthm logbitp-+-simple2
  (implies (and (integerp n)
                (< 0 n)
                (logbitp (1- n) x)
                (logbitp (1- n) y)
                (signed-byte-p n x)
                (signed-byte-p n y))
           (logbitp n (+ x y)))
  :hints (("goal" :use (:instance logbitp-+-simple2-helper (c 0)))))

(local (in-theory (disable logcons-of-0)))

(defthm logbitp-+-usb-v1-helper
  (implies (and (integerp n)
                (< 0 n)
                (logbitp (1- n) x)
                (unsigned-byte-p 1 c)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (not (logbitp (1- n) (+ x y c))))
           (logbitp n (+ x y c)))
  :rule-classes nil
  :hints (("goal" :in-theory (enable LRDT open-logcons))))
           ;; :induct (sub1-logcdr-logcdr-carry-induction n x y c)
;;            :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY))))

(defthm logbitp-+-usb-v1
  (implies (and (integerp n)
                (< 0 n)
                (logbitp (1- n) x)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (not (logbitp (1- n) (+ x y))))
           (and (logbitp n (+ x y))
                (logbitp n (+ y x))))
  :hints (("goal" :use (:instance logbitp-+-usb-v1-helper (c 0)))))

(defthm logbitp-+-usb-v2-helper
  (implies (and (integerp n)
                (< 0 n)
                (logbitp (1- n) x)
                (logbitp (1- n) y)
                (unsigned-byte-p 1 c)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (logbitp n (+ x y c)))
  :rule-classes nil
  :hints (("goal" :in-theory (enable LRDT open-logcons))))

(defthm logbitp-+-usb-v2
  (implies (and (integerp n)
                (< 0 n)
                (logbitp (1- n) x)
                (logbitp (1- n) y)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (logbitp n (+ x y)))
  :hints (("goal" :use (:instance logbitp-+-usb-v2-helper (c 0)))))

(defthm logbitp-+-usb-v3-helper
  (implies (and (integerp n)
                (< 0 n)
                    (not (logbitp (1- n) x))
                (not (logbitp (1- n) y))
                (unsigned-byte-p 1 c)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (not (logbitp n (+ x y c))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable LRDT open-logcons))))

(defthm logbitp-+-usb-v3
  (implies (and (integerp n)
                (< 0 n)
                (not (logbitp (1- n) x))
                (not (logbitp (1- n) y))
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (not (logbitp n (+ x y))))
  :hints (("goal" :use (:instance logbitp-+-usb-v3-helper (c 0)))))

(defthm logbitp-+-usb-v4-helper
  (implies (and (integerp n)
                (< 0 n)
                (not (logbitp (1- n) x))
                (unsigned-byte-p 1 c)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (logbitp (1- n) (+ x y c)))
           (not (logbitp n (+ x y c))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable LRDT open-logcons))))

(defthm logbitp-+-usb-v4
  (implies (and (integerp n)
                (< 0 n)
                (not (logbitp (1- n) x))
                (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (logbitp (1- n) (+ x y)))
           (and (not (logbitp n (+ x y)))
                (not (logbitp n (+ y x)))))
  :hints (("goal" :use (:instance logbitp-+-usb-v4-helper (c 0)))))

;; (deftheory overflow-bits
;;   '(logbitp-+-usb-v4
;;    logbitp-+-usb-v3
;;    logbitp-+-usb-v2
;;    logbitp-+-usb-v1
;;    logbitp-+-simple2
;;    logbitp-+-simple
;;    unsigned-byte-p-+))

(in-theory (disable ;overflow-bits
            logbitp-+-usb-v4
            logbitp-+-usb-v3
            logbitp-+-usb-v2
            logbitp-+-usb-v1
            logbitp-+-simple2
            logbitp-+-simple
            unsigned-byte-p-+))

;; doesn't belong here - but where does it belong?
;; Should I restrict this?  It seems expensive!
(defthm top-bit-means-<
  (implies (and (logbitp n x)
                (not (logbitp n y))
                (unsigned-byte-p (1+ n) x)
                (unsigned-byte-p (1+ n) y)
                (integerp n)
                (<= 0 n)
                )
           (< y x))
;           (and (< y x)
;                (not (< x y)))) ;shouldn't need this part as it's implied by the first
  :hints (("goal":in-theory (enable LRDT open-logcons))))

(defthm logbitp-logior
  (equal (logbitp n (logior x y))
         (or (logbitp n x) (logbitp n y)))
  :hints (("goal" :in-theory (enable LRDT zp))))

(defthm logbitp-logand
  (equal (logbitp n (logand x y))
         (and (logbitp n x) (logbitp n y)))
  :hints (("goal" :in-theory (enable LRDT zp))))
           ;; :in-theory (enable
;;                        LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
;;            :induct (sub1-logcdr-logcdr-induction n x y))))

;; (defthm logbitp-ash-neg
;;   (implies (and (integerp n)
;;                 (integerp x)
;;                 (integerp m)
;;                 (< m 0)
;;                 (<= 0 n))
;;            (equal (logbitp n (ash x m))
;;                   (logbitp (- n m) x)))
;;   :rule-classes nil
;;   :hints (("goal" :in-theory (enable LRDT logbit))))
;;            ;; :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
;; ;;            :induct (add1-add1-induction m n))
;; ;;           ("Subgoal *1/2.1'" :use (:instance logbitp* (pos (1+ n)) (i (ASH X (+ 1 M))))
;; ;;            :in-theory (disable logbitp*))))

;; (defthm logbitp-ash-pos
;;   (implies (and (integerp n)
;;                 (integerp x)
;;                 (integerp m)
;;                 (<= 0 m)
;;                 (<= 0 n))
;;            (equal (logbitp n (ash x m))
;;                   (and (<= m n) (logbitp (- n m) x))))
;;   :rule-classes nil
;;   :hints (("goal" :in-theory (enable LRDT))));))))
;;  ;; :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
;; ;;  :induct (sub1-sub1-induction m n))))

;bzo do we want this or not?
(defthm logbit-logbitp-1
  (equal (equal (logbit x n) 1)
         (logbitp x n))
  :hints (("goal" :in-theory (enable logbit))))

;bzo do we want this or not?
(defthm logbit-logbitp-2
  (equal (equal (logbit x n) 0)
         (not (logbitp x n)))
  :hints (("goal" :in-theory (enable logbit))))

(encapsulate
 ()

 (local
  (defthm logbitp-ash-l1
    (implies (and ;(integerp x)
                  (integerp m)
                  (equal (logcar (ash x m)) 1))
             (logbitp (- m) x))
    :hints (("goal"
             :cases ((< 0 m))))))

 (defthm logbitp-ash
   (implies (and (<= 0 n)
                 (integerp n)
                 (integerp m))
            (equal (logbitp n (ash x m))
                   (and (<= m n) (logbitp (- n m) x))))
   :hints (("Subgoal *1/2" :in-theory (enable ash*)) ;bzo why was this necessary?  ash* seemed to fire more easily after the move to 3.0?
           ("goal" :in-theory (e/d (LRDT ;zip
                                         ) (;logcons-of-0 ;for acl2 3.0
                                            ash*
                                           ))))))

;see also LOGBITP-TOO-BIG
(defthm logbitp-n-unsigned-byte-p-n
  (implies (unsigned-byte-p n x)
           (not (logbitp n x)))
  :hints (("goal" :in-theory (enable unsigned-byte-p logbitp)))
  :rule-classes ((:rewrite :backchain-limit-lst 5)))

(defthm logbitp-+-loghead-helper
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n1)
                (< n1 n2)
                (unsigned-byte-p 1 c))
           (equal (logbitp n1 (+ x (loghead n2 y) c))
                  (logbitp n1 (+ x y c))))
  :rule-classes nil
  :hints (("goal"
           :in-theory (enable LRDT open-logcons)
           :induct (sub1-sub1-logcdr-logcdr-carry-induction n1 n2 x y c))))

(defthm logbitp-+-loghead
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n1)
                (< n1 n2))
           (and (equal (logbitp n1 (+ x (loghead n2 y)))
                       (logbitp n1 (+ x y)))
                (equal (logbitp n1 (+ (loghead n2 y) x))
                       (logbitp n1 (+ y x)))
                (implies (integerp z)
                         (and (equal (logbitp n1 (+ x z (loghead n2 y)))
                                     (logbitp n1 (+ x z y)))
                              (equal (logbitp n1 (+ x (loghead n2 y) z))
                                     (logbitp n1 (+ x y z)))))))
  :hints (("goal" :use
           ((:instance logbitp-+-loghead-helper (c 0))
            (:instance logbitp-+-loghead-helper (c 0) (x (+ x z)))))))

(defthm logbitp-+-logext-bridge
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n1)
                (< n1 n2))
           (and (equal (logbitp n1 (+ (logext n2 y) x))
                       (logbitp n1 (+ y x)))
                (implies (integerp z)
                         (and (equal (logbitp n1 (+ x z (logext n2 y)))
                                     (logbitp n1 (+ x z y)))
                              (equal (logbitp n1 (+ x (logext n2 y) z))
                                     (logbitp n1 (+ x y z)))))))
  :hints (("goal" :use
           ((:instance logbitp-+-logext (i n1) (x (+ x z)) (n n2))))))

(defthm logbitp-+-logext-bridge
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n1)
                (< n1 n2))
           (and (equal (logbitp n1 (+ (logext n2 y) x))
                       (logbitp n1 (+ y x)))
                (implies (integerp z)
                         (and (equal (logbitp n1 (+ x z (logext n2 y)))
                                     (logbitp n1 (+ x z y)))
                              (equal (logbitp n1 (+ x (logext n2 y) z))
                                     (logbitp n1 (+ x y z)))))))
  :hints (("goal" :use
           ((:instance logbitp-+-logext (i n1) (x (+ x z)) (n n2))))))

(defthm logbitp---*2
  (implies (and (integerp n)
                (integerp x)
                (< 0 n))
           (equal (logbitp n (- (* 2 x)))
                  (logbitp (1- n) (- x))))
  :hints (("goal" :use (:instance logbitp*-better (pos n) (i (- (* 2 x)))))))

(defthm logbitp-+--1---*2
  (implies (and (integerp n)
                (integerp x)
                (< 0 n))
           (equal (logbitp n (+ -1 (- (* 2 x))))
                  (logbitp (1- n) (+ -1 (- x)))))
  :hints (("goal" :use (:instance logbitp* (pos n) (i (+ -1 (- (* 2 x))))))))

(defthmd negate-as-bits
  (implies (integerp x)
           (equal (- x)
                  (1+ (lognot x))))
  :hints (("goal" :in-theory (enable LRDT logendp open-logcons))))

(local (in-theory (enable open-logcons))) ;why?
(local (in-theory (disable EXPT-2-CRUNCHER))) ;bzo why?

(defthm logbitp--
  (implies (and (integerp n)
                (<= 0 n)
                (integerp x))
           (equal (logbitp n (- x))
                  (not (logbitp n (1- x)))))
  :hints (("goal"
           :induct (logbitp n x) ;not necessary, but speeds things up
           :in-theory (enable LRDT negate-as-bits))))

(defthm logbitp---logext
  (implies (and (integerp n1)
                (integerp n2)
                (integerp y)
                (<= 0 n1)
                (< n1 n2))
           (equal (logbitp n1 (- (logext n2 y)))
                  (logbitp n1 (- y)))))

(defthm logbitp-+x-
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (<= 0 n))
           (equal (logbitp n (+ x (- y)))
                  (not (logbitp n (1- (+ y (- x)))))))
  :hints (("goal" :use ((:instance logbitp-- (x (+ y (- x))))))))

(in-theory (disable logbitp-+x-))

(defthm logbitp-+---logext
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n1)
                (< n1 n2))
           (equal (logbitp n1 (+ x (- (logext n2 y))))
                  (logbitp n1 (+ x (- y)))))
  :hints (("goal" :in-theory (enable logbitp-+x-))))


(defthm logbitp-+-+---logext
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (integerp y)
                (integerp z)
                (<= 0 n1)
                (< n1 n2))
           (equal (logbitp n1 (+ x z (- (logext n2 y))))
                  (logbitp n1 (+ x z (- y)))))
  :hints (("goal" :use (:instance logbitp-+---logext (x (+ x z))))))

(defthm negate-as-bits-reverse
  (implies (integerp x)
           (equal (1+ (lognot x))
                  (- x)))
  :hints (("goal" :in-theory (enable LRDT logendp))))

(defthm negate-as-bits-reverse-bridge
  (implies (and (integerp x)
                (integerp y))
           (equal (+ 1 x (lognot y))
                  (+ x (- y))))
  :hints (("goal"
           :use (:instance negate-as-bits-reverse (x y))
           :in-theory (disable negate-as-bits-reverse))))

(defthm logbitp-+-expt-1-n
  (implies (and (integerp x)
                (integerp n)
                (<= 0 n))
           (equal (logbitp (1+ n) (+ (expt 2 n) x))
                  (equal (logbitp (1+ n) x) (not (logbitp n x)))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logbitp-+-expt-1-n-rewrite
  (implies (and (syntaxp (quotep k))
                (integerp x)
                (integerp n)
                (< 0 n)
                (equal k (expt 2 (1- n))))
           (equal (logbitp n (+ k x))
                  (equal (logbitp n x) (not (logbitp (1- n) x)))))
  :hints (("goal" :use (:instance logbitp-+-expt-1-n (n (1- n))))))

;; (thm
;;  (equal (EQUAL (LOGCAR (+ x y)) 0)
;;         (or (and (equal (logcar x) 0)
;;                  (equal (logcar y) 0))
;;             (and (equal (logcar x) 1)
;;                  (equal (logcar y) 1))))
;;  :hints (("Goal" :in-theory (enable logcar))))

(defthm logbitp-+-expt-n
  (implies (and (integerp x) ;drop?
                (integerp n)
                (<= 0 n))
           (equal (logbitp n (+ (expt 2 n) x))
                  (not (logbitp n x))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logbitp-+-expt-n-alt
  (implies (and (integerp x)
                (integerp n)
                (<= 0 n))
           (equal (logbitp n (+ x (expt 2 n)))
                  (not (logbitp n x))))
  :hints (("goal" :in-theory (e/d (LRDT) (;logbitp* LOGBITP*-BETTER
                                          LOGBITP-OF-LOGCDR LOGBITP-OF-LOGCDR2 ;bzo looped in acl2 version 3.0
                                                   )))))

(defthm logbitp-+-expt-n-rewrite
  (implies (and (syntaxp (quotep k))
                (integerp x)
                (integerp n)
                (equal k (expt 2 n))
                (<= 0 n))
           (equal (logbitp n (+ k x))
                  (not (logbitp n x))))
  :hints (("goal" :use logbitp-+-expt-n)))

(defthm logbitp-+-too-big
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n)
                (equal (loghead (1+ n) x) 0))
           (equal (logbitp n (+ x y)) (logbitp n y)))
  :hints (("goal"
           :in-theory (enable LRDT)
           :induct (sub1-logcdr-logcdr-induction n x y))))

(defthm sign-as-logbitp
  (implies (and (integerp n)
                (<= 0 n)
                (signed-byte-p (1+ n) x))
           (equal (< x 0) (logbitp n x)))
  :rule-classes nil
  :hints (("goal" :in-theory (enable LRDT))))

;; DANGER DANGER!
;; How should I handle < when dealing with overflow bits?
(defthm sign-bit-difference-as-<
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (logbitp n (+ x (- y)))
                  (< x y)))
  :hints (("goal" :use (:instance sign-as-logbitp (x (+ x (- y)))))))

(defthm logbitp-+---expt
  (implies (and (integerp n)
                (integerp x)
                (< 0 n))
           (equal (logbitp n (+ x (- (expt 2 n))))
                  (not (logbitp n x))))
  :hints (("goal" :in-theory (e/d (LRDT) (LOGBITP-OF-LOGCDR2 LOGBITP-OF-LOGCDR ;bzo looped with logbitp* and/or logbitp*-better in 3.0
                                                             ;bzo add theory invariant?
                                          )))))

(defthm logbitp-+---expt-rewrite
  (implies (and (syntaxp (quotep k))
                (integerp x)
                (< 0 n)
                (equal n (integer-length k))
                (equal k (- (expt 2 n))))
           (equal (logbitp n (+ k x))
                  (not (logbitp n x))))
  :hints (("goal" :use logbitp-+---expt)))

;bzo this seems odd and caused problems??
(defthm expt-bound-as-logbitp
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (< (+ x y) (expt 2 n))
                  (not (logbitp n (+ x y)))))
  :hints (("goal" :use  (:instance unsigned-byte-p-+)
           :in-theory (enable unsigned-byte-p))))


(defthmd expt-bound-as-logbitp-rewrite
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (equal k (expt 2 (1- (integer-length k))))
                (unsigned-byte-p (1- (integer-length k)) x)
                (unsigned-byte-p (1- (integer-length k)) y))
           (equal (< (+ x y) k)
                  (not (logbitp (1- (integer-length k)) (+ x y)))))
  :hints (("goal" :use (:instance expt-bound-as-logbitp (n (1- (integer-length k)))))))

(defthm logbit-logior
  (implies (and (integerp n)
                (integerp a)
                (integerp b)
                (<= 0 n))
           (equal (logbit n (logior a b))
                  (b-ior (logbit n a) (logbit n b))))
  :hints (("goal" :in-theory (enable LRDT logbit))))

(defthm logbit-logand
  (implies (and (integerp n)
                (integerp a)
                (integerp b)
                (<= 0 n))
           (equal (logbit n (logand a b))
                  (b-and (logbit n a) (logbit n b))))
  :hints (("goal" :in-theory (enable LRDT logbit))))

(defthm logbit-logxor
  (implies (and (integerp n)
                (integerp a)
                (integerp b)
                (<= 0 n))
           (equal (logbit n (logxor a b))
                  (b-xor (logbit n a) (logbit n b))))
  :hints (("goal" :in-theory (enable logbitp b-xor))))

(defthm logbit-ash
  (implies (and (integerp n)
                (integerp x)
                (integerp m)
                (<= 0 n))
           (equal (logbit n (ash x m))
                  (if (<= m n) (logbit (- n m) x) 0)))
  :hints (("goal" :in-theory (enable logbit))))

;trying without...
;; (defthm logbit-carry-simple
;;   (implies (and (integerp n)
;;                 (<= 0 n)
;;                 (equal n n2)
;;                 (unsigned-byte-p n x))
;;            (not (logbitp n2 x))))

(defthm logbit-carry-+1
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p n x))
           (equal (logbit n (+ 1 x))
                  (if (equal x (1- (expt 2 n)))
                      1
                    0)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logbitp-logcar
  (equal (logbitp n (logcar x))
         (if (and (integerp n)
                  (< 0 n))
             nil
           (logbitp 0 x))))

(defthm logbit-logext
  (implies (and (integerp i)
                (integerp n)
                (integerp x)
                (<= 0 i)
                (< 0 n))
           (equal (logbit i (logext n x))
                  (if (< i n)
                      (logbit i x)
                    (logbit (1- n) x))))
  :hints (("goal" :in-theory (enable logbit))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logext
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm signed-byte-p-logext-fc
  (implies (and (> size 0)
                (integerp size))
           (signed-byte-p size (logext size i)))
  :rule-classes ((:forward-chaining :trigger-terms ((logext size i)))))

(defthm logext-bound
  (implies (and (integerp m)
                (integerp n)
                (< 0 m)
                (<= (1- m) n))
           (and (<= (- (expt 2 n)) (logext m x))
                (<= (logext m x) (1- (expt 2 n)))))
  :hints (("goal"
           :in-theory (e/d (signed-byte-p) (signed-byte-p-logext))
           :use ((:instance signed-byte-p-logext (i x) (size1 (1+ n)) (size m))))))

;drop?
(defthm ifix-logext
  (equal (ifix (logext x y))
         (logext x y)))

(defthm logext-loghead
  (implies (and (integerp n)
                (integerp m)
                (< 0 n)
                )
           (equal (logext n (loghead m x))
                  (if (<= n m)
                      (logext n x)
                    (loghead m x))))
  :hints (("goal"
           :in-theory (e/d (LRDT) (logext* LOGHEAD*))
           :induct (sub1-sub1-logcdr-induction n m x))))

(defthm logext-ash
  (implies (and (< m n)
                (<= 0 m)
                (integerp m)
                (integerp n)
                )
           (equal (logext n (ash x m))
                  (ash (logext (- n m) x) m)))
  :hints (("goal"; :induct t
           :in-theory (e/d (LRDT) (ASH-RECOLLAPSE
                                   )))))

(defthm logext-logior
  (equal (logext n (logior x y))
         (logior (logext n x) (logext n y)))
  :hints (("goal" :in-theory (enable LRDT zp))))

(defthmd logior-of-logext-and-logext
  (equal (logior (logext n x) (logext n y))
         (logext n (logior x y))))

(theory-invariant (incompatible (:rewrite logext-logior) (:rewrite logior-of-logext-and-logext)))

;; This should be in the loghead section, but it uses so many logext
;; rules we place it here.

(defthm loghead-+-logior-ash-logext-bridge
  (implies (and (integerp n1)
                (integerp n2)
                (integerp n3)
                (integerp x)
                (integerp y)
                (integerp z)
                (<= 0 x)
                (<= 0 n1)
                (< 0 n2)
                (<= 0 n3)
                (<= n1 (+ n3 n2)))
           (equal (loghead n1 (+ x (logior z (ash (logext n2 y) n3))))
                  (loghead n1 (+ x (logior z (ash y n3))))))
  :hints (("goal" :use (:instance logextu-as-loghead (final-size n1) (ext-size (+ n2 n3)) (i (logior z (ash y n3)))))))



;; We need to prove equal-logext---logext.
;; We define a function that handles a little-bigger range
;; through casesplitting.  14 Nov 00


(encapsulate
 ()

 (local (in-theory (enable expt)))

 (local
  (defmacro logext-intN+1 (n s)
    `(let ((s ,s))
       (let ((n ,n))
         (let ((s (if (< s (expt 2 n)) s (+ s (- (expt 2 n))))))
           (let ((s (if (< s (expt 2 (1- n))) s (+ s (- (expt 2 n))))))
             s))))))

 (local
  (defthm +-logext-logext-0-helper
    (implies (and (integerp n)
                  (< 0 n)
                  (unsigned-byte-p n x)
                  (unsigned-byte-p n y))
             (equal (equal (+ (logext-intN+1 n x) (logext-intN+1 n y)) 0)
                    (or (and (equal x 0) (equal y 0))
                        (and (equal (+ x y) (expt 2 n)) (not (equal x y))))))
    :hints (("goal" :in-theory (enable logext unsigned-byte-p)))))

 (local
  (defthm <-+k*j-expt-bridge
    (implies (and (integerp j)
                  (integerp n)
                  (integerp k)
                  (integerp m)
                  (<= 0 j)
                  (<= 0 n)
                  (<= 0 k)
                  (<= 0 m)
                  (<= m n)
                  (equal (loghead m j) 0)
                  (< k (expt 2 m)))
             (equal (< (+ k j) (expt 2 n))
                    (< j (expt 2 n))))
    :rule-classes nil
    :hints (("goal" :induct (sub1-sub1-logcdr-logcdr-induction m n k j)
             :in-theory (e/d (LOGOPS-RECURSIVE-DEFINITIONS-THEORY) (LOGCAR-0-REWRITE))))))

 (local
  (defthm <-+k*j-expt-rewrite-bridge
    (implies (and (integerp j)
                  (integerp n)
                  (integerp k)
                  (<= 0 j)
                  (<= 0 n)
                  (<= 0 k)
                  (< 1 n)
                  (equal (loghead 2 j) 0)
                  (< k 4))
             (equal (< (+ k j) (expt 2 n))
                    (< j (expt 2 n))))
    :hints (("goal" :use (:instance <-+k*j-expt-bridge (m 2))))))

;see unsigned-byte-p-1+
 (local (defthm unsigned-byte-p-1+-yuck
          (implies (and ;(syntaxp (not (quotep x))) ;keeps this from firing on, e.g., (unsigned-byte-p n 500)
                    (unsigned-byte-p n x)
                    (integerp n)
                    (<= 0 n)
                    )
                   (equal (unsigned-byte-p n (+ 1 x))
                          (not (equal x (1- (expt 2 n)))))) ; should this be (loghead n -1) ?
          :hints (("goal" :in-theory (enable LRDT unsigned-byte-p)))))

 (local


  (defthm logext-as-logext-intN+1
    (implies (and (unsigned-byte-p n x) ; hyp could be (1+ n), but stronger thm not needed
                  (integerp n)
                  (< 0 n))
             (equal (logext n x)
                    (logext-intN+1 n x)))
    :hints (("goal" :in-theory (e/d (lrdt signed-byte-p)
                                    (EXPT-2-EQUAL-1-REWRITE

; Modification by Matt K. April 2016 to acccommodate the addition of a type-set
; bit for the set {1}.  The following linear rule started firing, sending the
; proof in another direction -- but this happened after an elim, which makes me
; particularly unconcerned about how ACL2's new heuristics are functioning
; here.

                                     EXPT->-1
                                     ))))))

 (defthm equal-logext---logext
   (implies (and (integerp n)
                 (< 0 n)
                 (unsigned-byte-p n x)
                 (unsigned-byte-p n y))
            (equal (equal (logext n x) (- (logext n y)))
                   (or (and (equal x 0) (equal y 0))
                       (and (equal (+ x y) (expt 2 n))
                            (not (equal x y))))))
   :hints (("goal" :use +-logext-logext-0-helper))))

(encapsulate
 ()

 (local (defthm expt-hack1
          (IMPLIES (AND (INTEGERP J)
                        (INTEGERP N)
                        (< 0 N)
                        (LOGBITP (+ -2 N) J)
                        (NOT (EQUAL N 1)))
                   (EQUAL (EXPT 2 N)
                          (* 2 (EXPT 2 (+ -1 N))))) :hints (("Goal" :in-theory (enable expt)))))


;; DANGER - opening to arithmetic
;should this lemma be disabled?
;see also if-to-logext
;free variable n2
 (defthm logext-open-logbit-sign-known
   (and (implies (and (logbitp n2 x)
                      (equal n2 (1- n))
                      (integerp n)
                      (integerp x)
                      (< 0 n)
                      )
                 (equal (logext n x)
                        (- (loghead n x) (expt 2 n))))
        (implies (and (not (logbitp n2 x))
                      (equal n2 (1- n))
                      (integerp n)
                      (integerp x)
                      (< 0 n)
                      )
                 (equal (logext n x)
                        (loghead n x))))
   :hints (("goal" :in-theory (e/d (LRDT
                                    )
                                   (LOGBITP-OF-LOGCDR2
                                    equal-logext-0))))))



(defthm logext-lognot
  (equal (logext n (lognot x))
         (lognot (logext n x)))
  :hints (("goal" :in-theory (enable LRDT zp))))

(defthm logext-logand
  (equal (logext n (logand x y))
         (logand (logext n x) (logext n y)))
  :hints (("goal" :in-theory (enable LRDT zp))))

(defthmd logand-of-logext-and-logext
  (equal (logand (logext n x) (logext n y))
         (logext n (logand x y))))

(theory-invariant (incompatible (:rewrite logext-logand) (:rewrite logand-of-logext-and-logext)))

(defthm logext-logtail
  (implies (and ; (integerp x)
            (integerp n)
            (integerp m)
            (<= 0 n)
            (< 0 m))
           (equal (logext m (logtail n x))
                  (logtail n (logext (+ m n) x))))
  :hints (("goal" :in-theory (e/d (LRDT logtail*-better) (logtail*)))))

;; turned off in favor of rule above (for consistency with how we treat loghead?)
(defthmd logtail-logext
  (implies (and (integerp n)
                (integerp m)
                (<= 0 n)
                (< 0 m))
           (equal (logtail n (logext m x))
                  (if (< n m)
                      (logext (- m n) (logtail n x))
                    (- (logbit (1- m) x)))))
  :hints (("goal" :in-theory (enable LRDT logbit)
           :induct (sub1-sub1-logcdr-induction n m x))))

(theory-invariant (incompatible (:rewrite logtail-logext) (:rewrite logext-logtail)))

;Which do we prefer to have inside?
;Or should we introduce a new bit slicing function?
;generalize!
;; (defthm logtail-logext-hack-2
;;   (implies (integerp x)
;;            (equal (logtail 15 (logext 32 x))
;;                   (logext 17 (logtail 15 x))))
;;   :hints
;;   (("Goal" :in-theory (enable logext ifix))))


;should be able to open logtail and still have this prove?
;; it reduced to:
;; (EQUAL (FLOOR (LOGEXT 32 X) 65536)
;;        (LOGEXT 16 (FLOOR (IFIX X) 65536)))
;gen this?
;; (defthm logtail-logext-hack
;;   (equal (logtail 16 (logext 32 x))
;;          (logext 16 (logtail 16 x)))
;;   :hints (("Goal" :in-theory (enable ;logtail
;;                                      logext ifix))))



(encapsulate
 ()
 (local
  (defthm logext-logapp-helper
    (implies (and (integerp x)
                  (integerp y)
                  (integerp n)
                  (integerp m)
                  (<= 0 n)
                  (< 0 m))
             (equal (logext m (logapp n x y))
                    (if (<= m n)
                        (logext m x)
                      (logapp n x (logext (- m n) y)))))
    :hints (("goal" :in-theory (enable LRDT)
             :induct (sub1-sub1-logcdr-induction m n x)))))

 (defthm logext-logapp
   (implies (and (<= 0 n)
                 (< 0 m)
                 (integerp n)
                 (integerp m)
                 )
            (equal (logext m (logapp n x y))
                   (if (<= m n)
                       (logext m x)
                     (logapp n x (logext (- m n) y)))))
   :hints (("Goal" :use (:instance logext-logapp-helper)
            :in-theory (disable logext-logapp-helper)))))


;We make this a separate rule so it will be enabled even when logext-logapp is disabled.
(defthm logext-logapp-one-case
   (implies (and (<= m n)
                 (<= 0 n)
                 (< 0 m)
                 (integerp n)
                 (integerp m)
                 )
            (equal (logext m (logapp n x y))
                   (logext m x))))

(defthmd logapp-of-logext
  (implies (and (<= 0 n)
                (< 0 m)
                (integerp n)
                (integerp m)
                )
           (equal (logapp n x (logext m y))
                  (logext (+ m n) (logapp n x y)))))

(theory-invariant (incompatible (:rewrite logapp-of-logext) (:rewrite logext-logapp)))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; ash - part 2
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(local
 (defthm ash-downto-1-or-0-helper
   (implies (and (integerp n)
                 (< 0 n)
                 (unsigned-byte-p (1+ n) x))
            (equal (ash x (- n))
                   (if (unsigned-byte-p n x) 0 1)))
   :hints (("goal" :in-theory (enable LRDT)))
    :rule-classes nil))

(defthm ash-plus-downto-1-or-0
  (implies (and (syntaxp (quotep n))
                (integerp n)
                (< 0 n)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (ash (+ x y) (- n))
                  (if (unsigned-byte-p n (+ x y))
                      0
                    1)))
  :hints (("goal"
           :use (:instance ash-downto-1-or-0-helper (x (+ x y)))
           :in-theory (disable unsigned-byte-p-+))))

(defthm equal-ash-logcdr-x-x
  (equal (equal x (ash (logcdr x) 1))
         (and (equal (logcar x) 0)
              (integerp x)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm ash-plus-downto-1-or-0-bridge
  (implies (and (syntaxp (quotep n))
                (integerp n)
                (integerp x)
                (integerp y)
                (< 0 n)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (ash (+ 1 x y) (- n))
                  (if (unsigned-byte-p n (+ 1 x y)) 0 1)))
  :hints (("goal"
           :in-theory (enable unsigned-byte-p expt)
           :use (:instance ash-downto-1-or-0-helper (x (+ 1 x y))))))

(defthm ash-sbp-downto-1-or-0-helper
  (implies (and (integerp n)
                (< 0 n)
                (signed-byte-p (1+ n) x))
           (equal (ash x (- n))
                  (if (logbitp n x) -1 0)))
  :hints (("goal" :in-theory (enable LRDT)))
  :rule-classes nil)

(defthm ash-logext-downto-1-or-0
  (implies (and (integerp n)
                (integerp m)
                (integerp x)
                (< 0 n)
                (equal n (1+ m)))
           (equal (ash (logext n x) (- m))
                  (if (logbitp m x) -1 0)))
  :hints (("goal" :use (:instance ash-sbp-downto-1-or-0-helper
                                  (n m)
                                  (x (logext n x))))))

(defthm ash-sbp-downto-1-or-0-bridge
  (implies (and (integerp n)
                (< 0 n)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (ash (+ x (- y)) (- n))
                  (if (logbitp n (+ x (- y))) -1 0)))
  :hints (("goal" :use (:instance ash-sbp-downto-1-or-0-helper
                                  (x (+ x (- y))))
           :in-theory (enable unsigned-byte-p signed-byte-p))))



;; Needed just for the FCP models?
(defthm equal-ash-expt-0-fact
  (implies (and (integerp n)
                (integerp x)
                (<= 0 n))
           (equal (equal (ash (+ x (expt 2 n)) (- n)) 0)
                  (and (signed-byte-p (1+ n) x)
                       (logbitp n x))))
  :hints (("goal" :in-theory (enable LRDT expt))))

(defthm equal-ash-expt-0-fact-rewrite
  (implies (and (integerp k)
                (syntaxp (quotep k))
                (integerp n)
                (integerp x)
                (equal k (expt 2 n))
                (equal n (1- (integer-length k))))
           (equal (equal (ash (+ k x) (- n)) 0)
                  (and (signed-byte-p (1+ n) x)
                       (logbitp n x)))))

(defthm ash-sbp-expt-downto-1-or-0-helper
  (implies (and (integerp n)
                (< 0 n)
                (signed-byte-p (1+ n) x))
           (equal (ash (+ (expt 2 n) x) (- n))
                  (if (logbitp n x) 0 1)))
  :hints (("goal" :in-theory (enable LRDT expt)))
  :rule-classes nil)

(defthm ash-sbp-downto-1-or-0-bridge2
  (implies (and (integerp k)
                (syntaxp (quotep k))
                (integerp n)
                (equal k (expt 2 n))
                (equal n (1- (integer-length k)))
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (ash (+ k x (- y)) (- n))
                  (if (logbitp n (+ x (- y))) 0 1)))
  :hints (("goal" :use (:instance ash-sbp-expt-downto-1-or-0-helper
                                  (x (+ x (- y)))))))

(defthm equal-ash-+---expt--1
  (implies (and (integerp n)
                (<= 0 n)
                (signed-byte-p (1+ n) x))
           (equal (equal (ash (+ x (- (expt 2 n))) (- n)) -1)
                  (not (logbitp n x))))
  :hints (("goal" :in-theory (enable LRDT expt))))

(defthm equal-ash-+---expt--1-rewrite
  (implies (and (syntaxp (quotep k)) (integerp k)
                (equal (- (expt 2 (1- (integer-length (- k))))) k)
                (equal n (1- (integer-length (- k))))
                (signed-byte-p (1+ n) x))
           (equal (equal (ash (+ k x) (- n)) -1)
                  (not (logbitp n x))))
  :hints (("goal" :use (:instance equal-ash-+---expt--1
                                  (n (1- (integer-length (- k))))))))

(defthm ash-logext-neg
  (implies (and (integerp n)
                (integerp x)
                (integerp m)
                (< 0 n)
                (< m 0)
                (< 0 (+ n m)))
           (equal (ash (logext n x) m)
                  (logext (+ n m) (ash x m))))
  :hints (("goal" :in-theory (enable LRDT))))

;; (encapsulate
;;  ()

;;  (local
;;   (defthm ash-logand-neg
;;     (implies (and (integerp x)
;;                   (integerp y)
;;                   (integerp n)
;;                   (< n 0))
;;              (equal (ash (logand x y) n)
;;                     (logand (ash x n) (ash y n))))
;;     :hints (("goal"
;;              :induct (add1-induction n)
;;              :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)))))

;;  (local
;;   (defthm ash-logand-pos
;;     (implies (and (integerp x)
;;                   (integerp y)
;;                   (integerp n)
;;                   (<= 0 n))
;;              (equal (ash (logand x y) n)
;;                     (logand (ash x n) (ash y n))))
;;     :hints (("goal" :induct (sub1-induction n)
;;              :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)))))

 ;the above lemma combined with ash-logand-neg, give us the following:
(defthm ash-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp n))
           (equal (ash (logand x y) n)
                  (logand (ash x n) (ash y n))))
  :hints (("goal" :in-theory (e/d (LRDT) (ASH-RECOLLAPSE ;for version 3.0 add theory invariant?
                                          ;ash*
                                          )))))

;; ;shouldn't need if logxor is rewritten
;; (defthm ash-logxor
;;   (implies
;;    (and (integerp x)
;;         (integerp y))
;;    (equal (ash (logxor x y) n)
;;           (ash (logior (logand x (lognot y))
;;                        (logand (lognot x) y))
;;                n))))

(defthm ash-as-logbit
  (implies (and (unsigned-byte-p (1+ n) x)
                (integerp n)
                (<= 0 n)
                )
           (equal (ash x (- n))
                  (logbit n x)))
;  :rule-classes nil
  :hints (("goal"
           :induct (logbitp n x)
           :in-theory (enable LRDT logbit))))
           ;; :induct (sub1-logcdr-induction n x)
;;            :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY logbit))))

;; (defthm ash--15-special
;;   (implies
;;    (unsigned-byte-p 16 x)
;;    (equal (ash x -15) (logbit 15 x))))
;;   :hints (("goal" :use (:instance ash--15-special-helper (n 15)))))

;; ;; NOTE:  The opposite direction of loghead-ash-pos!!
;; (defthm ash-neg-loghead
;;   (implies (and (integerp n1)
;;                 (integerp n2)
;;                 (integerp x)
;;                 (<= 0 n1)
;;                 (< n2 0))
;;            (equal (ash (loghead n1 x) n2)
;;                   (if (<= n1 (- n2))
;;                       0
;;                     (loghead (+ n1 n2) (ash x n2)))))
;;   :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
;;            :induct (add1-sub1-logcdr-induction n2 n1 x))))

;don't we just rewrite ash to logtail when the shift is negative?
(defthm ash-neg-lognot
  (implies (and (< n2 0)
                (integerp n2)
                (integerp x)
                )
           (equal (ash (lognot x) n2)
                  (lognot (ash x n2))))
  :hints (("goal" :in-theory (enable LRDT))))



(encapsulate
 ()

 (local
  (defthm ash-logapp-l1
    (implies (and (integerp x)
                  (integerp y)
                  (integerp n)
                  (integerp m)
                  (<= 0 n)
                  (< m 0))
             (equal (ash (logapp n x y) m)
                    (if (< n (- m))
                        (ash y (+ m n))
                      (logapp (+ n m) (ash x m) y))))
    :hints (("goal"
             :in-theory (enable ash-as-logtail)))))

 (local
  (defthm ash-logapp-l2
    (implies (and (<= 0 m)
                  (integerp x)
                  (integerp y)
                  (integerp n)
                  (integerp m)
                  (<= 0 n))
             (equal (ash (logapp n x y) m)
                    (if (< n (- m))
                        (ash y (+ n m))
                      (logapp (+ n m) (ash x m) Y))))
    :hints (("goal" :in-theory (enable LRDT)))))

 (defthm ash-logapp
   (implies (and (integerp x)
                 (integerp y)
                 (integerp n)
                 (integerp m)
                 (<= 0 n))
            (equal (ash (logapp n x y) m)
                   (if (< n (- m))
                       (ash y (+ n m))
                     (logapp (+ n m) (ash x m) y))))
   :hints (("goal"
            :cases ((< m 0))))))





;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; <
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm sign-+-logext-logext-as-logbitp
  (implies (and (integerp n)
                (< 0 n))
           (equal (< (+ (logext n x) (logext n y)) 0)
                  (logbitp n (+ (logext n x) (logext n y)))))
  :hints (("goal" :use (:instance sign-as-logbitp
                                  (x (+ (logext n x) (logext n y)))))))

(defthm sign-logext-as-logbitp
  (implies (and (integerp n)
                (< 0 n))
           (equal (< (logext n x) 0)
                  (logbitp (1- n) x)))
  :hints (("goal" :use (:instance sign-as-logbitp (x (logext n x)) (n (1- n))))))
