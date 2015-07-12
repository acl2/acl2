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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "Is anyone using this?  If so please remove this error.")




#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; super-ihs-definitions.lisp
;; John D. Powell
;(in-package "SUPER-IHS")

;;
;; This file isolates super-ihs definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the super-ihs book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

;(include-book "ash")

(defthm logext-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logext size i)
                  0))
  :hints (("Goal" :in-theory (enable logext logapp))))

(defthm logext-when-i-is-zero
  (equal (logext size 0)
         0)
  :hints (("goal" :in-theory (e/d (logext
                                   logapp
                                   )
                                  (LOGAPP-0)))))

(defthm logext-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (logext size i)
                  (logext 1 (logcar i))
                  ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :cases ((acl2-numberp size))
           :in-theory (enable logext))))

;rhs?
(defthm logext-when-size-is-0
  (equal (logext 0 i)
         (if (equal (logcar i) 0)
             0
           -1))
  :hints (("Goal" :in-theory (enable logext))))

(defthm logext-when-size-is-non-positive
  (implies (<= size 0)
           (equal (logext size i)
                  (logext 1 (logcar i))
                  ))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logext))))

(DEFTHM LOGEXT*-better
  (IMPLIES (AND (INTEGERP SIZE)
                (> SIZE 0)
     ;(INTEGERP I)
                )
           (EQUAL (LOGEXT SIZE I)
                  (COND ((EQUAL SIZE 1)
                         (IF (EQUAL (LOGCAR I) 0) 0 -1))
                        (T (LOGCONS (LOGCAR I)
                                    (LOGEXT (1- SIZE) (LOGCDR I)))))))
  :RULE-CLASSES
  ((:DEFINITION :CLIQUE (LOGEXT)
                :CONTROLLER-ALIST ((LOGEXT T T))))
  :hints (("Goal" :use (:instance LOGEXT*)
           :in-theory (disable LOGEXT*))))

(defthm evenp-of-logext
  (implies (and (integerp n)
                (<= 0 n))
           (equal (evenp (logext n x))
                  (evenp (ifix x))))
  :hints (("Goal" :in-theory (e/d (logext)
                                  (evenp loghead)))))

(defthm equal-logext-0
  (implies (and; (integerp x)
                (integerp n)
                (< 0 n))
           (equal (equal (logext n x) 0)
                  (equal (loghead n x) 0))))

(defthm equal-logext-minus-1
  (implies (and; (integerp x)
                (integerp n)
                (< 0 n))
           (equal (equal (logext n x) -1)
                  (equal (loghead n x) (loghead n -1))))
  :hints (("goal" :in-theory (enable))))

(defthm logext-does-nothing-rewrite
  (implies (and (integerp n)
                (< 0 n))
           (equal (equal (logext n x) x)
                  (signed-byte-p n x))))

(defthm logext-+-logext-better
  (equal (logext size (+ i (logext size j)))
         (logext size (+ i (ifix j))))
  :hints (("Goal" :use (:instance logext-+-logext (i (fix i)))
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d () ( logext-+-logext)))))

(in-theory (disable LOGEXT-+-LOGEXT))

(defthmd open-logcons
  (implies (syntaxp (constant-syntaxp b))
           (equal (logcons b i)
                  (+ (bfix b) (* 2 (ifix i)))))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm equal-logcons-0
  (equal (equal (logcons x y) 0)
         (and (equal (bfix x) 0)
              (equal (ifix y) 0)))
  :hints (("goal" :in-theory (enable logcons
                                     even-odd-different-2
                                     ))))

(defthm evenp-of-logcons
  (equal (evenp (logcons b i))
         (evenp (bfix b)))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm oddp-of-logcons
  (equal (oddp (logcons b i))
         (oddp (bfix b)))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm logcons-of-0
  (equal (logcons 0 x)
         (ash x 1))
  :hints (("Goal" :in-theory (enable logcons ash))))

(defthm floor-of-logcons
  (equal (floor (logcons b i) 2)
         (ifix i)
         )
  :hints (("Goal" :expand  (logcons b i))))

(defthm logcdr-equal-0-rewrite
  (equal (equal (logcdr c) 0)
         (or (not (integerp c))
             (equal 0 c) (equal 1 c)))
  :hints (("Goal" :in-theory (enable logcdr))))

(defthmd logcdr-of-zero
  (equal (logcdr 0)
         0)
  :hints (("goal" :in-theory (enable logcdr ifix))))

(defthm logcdr-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logcdr i)
                  0))
  :hints (("goal" :in-theory (enable logcdr ifix))))

;more like this?
(defthm logcdr-greater-than-0-rewrite
  (equal (< 0 (logcdr x))
         (and (integerp x)
              (<= 2 x))))

(defthm integer-length-of-logcdr
  (equal (integer-length (logcdr x))
         (if (and (integerp x)
                  (not (equal -1 x))
                  (not (equal 0 x)))
             (+ -1  (integer-length x))
           0))
  :hints (("Goal" :in-theory (e/d (logcdr) (FLOOR-OF-SHIFT-RIGHT-2
                                            FLOOR-BY-TWICE-HACK))
           :do-not '(generalize eliminate-destructors))))

(defthm unsigned-byte-p-of-logcdr
  (equal (unsigned-byte-p n (logcdr x))
         (and (integerp n)
              (<= 0 n)
              (if (integerp x)
                  (unsigned-byte-p (1+ n) x)
                t)))
  :hints (("goal"
           :in-theory (e/d (logcdr unsigned-byte-p ; expt
                                   EXPONENTS-ADD-UNRESTRICTED
                                   )
                           (FLOOR-OF-SHIFT-RIGHT-2
                            )))))

(defthm logcdr--
  (implies (integerp x)
           (equal (logcdr (- x))
                  (if (evenp x)
                      (- (logcdr x))
                    (+ -1 (- (logcdr x))))))
  :hints (("goal" :in-theory (enable logcdr))))

;enable?
(defthmd logcdr-of-sum
  (implies (and (integerp x)
                (integerp y))
           (equal (LOGCDR (+ x y))
                  (+ (logcdr x)
                     (logcdr y)
                     (if (and (oddp x)
                              (oddp y))
                         1
                       0))))
  :hints (("Goal" :in-theory (enable LOGCDR))))

(defthm logcdr-+-1-x
  (implies (and (integerp n)
                (< 0 n))
           (equal (logcdr (+ -1 (expt 2 n)))
                  (+ -1 (expt 2 (1- n)))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+-1-x-v2
  (implies (integerp n)
           (equal (logcdr (+ -1 (* 2 n)))
                  (+ -1 n)))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+-1-x-bridge
  (implies (integerp n)
           (equal (logcdr (+ -1 (- (* 2 n))))
                  (+ -1 (- n))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr---*2
  (implies (integerp x)
           (equal (logcdr (- (* 2 x)))
                  (- x)))
  :hints (("goal" :in-theory (enable logcdr))))


(defthm logcdr-expt
  (implies (and (integerp n)
                (< 0 n))
           (equal (logcdr (expt 2 n))
                  (expt 2 (1- n))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr---expt
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logcdr (- (expt 2 n)))
                  (if (equal n 0)
                      -1
                    (- (expt 2 (1- n))))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+2
  (implies (integerp x)
           (equal (logcdr (+ 2 x))
                  (1+ (logcdr x))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-*-x-expt-bridge
  (implies (and (integerp x)
                (integerp n)
                (< 0 n))
           (equal (LOGCDR (* X (EXPT 2 N)))
                  (* x (expt 2 (1- n)))))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm logcdr-+--1-expt
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logcdr (+ -1 (- (expt 2 n))))
                  (if (zp n)
                      -1
                    (+ -1 (- (expt 2 (1- n)))))))
  :hints (("goal" :in-theory (enable logcdr))))


(defthmd logcdr-*-1/2-expt
  (implies (and (syntaxp (quotep n))
                (integerp (* n m)))
           (equal (logcdr (* n m))
                  (floor (* n m) 2)))
  :hints (("goal" :in-theory (enable logcdr))))

(defthm ash-logcdr-1
  (implies (equal (logcar x) 0)
           (equal (ash (logcdr x) 1)
                  (ifix x)))
  :hints (("goal" :in-theory (enable logcdr ash))))

(in-theory (disable logcar))

(defthm logcar-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logcar i)
                  0))
  :hints (("goal" :in-theory (enable logcar ifix))))

;generalize the 1?
(defthm unsigned-byte-p-logcar
  (unsigned-byte-p 1 (logcar x))
  :hints (("goal" :in-theory (enable logcar)))
  :rule-classes ((:forward-chaining :trigger-terms ((logcar x)))
                 (:rewrite)))

;note the backchain-limit
(defthm logcar-identity
  (implies (unsigned-byte-p 1 x)
           (equal (logcar x)
                  x))
  :hints (("goal" :in-theory (enable logcar)))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm logcar--
  (implies (integerp x)
           (equal (logcar (- x))
                  (logcar x)))
  :hints (("goal" :in-theory (enable logcar))))

(defthm logcar-expt
  (implies (<= 0 n)
           (equal (logcar (expt 2 n))
                  (if (zp n) 1 0)))
  :hints (("goal" :in-theory (enable expt))))

;improve this?
(defthm logcar-+
  (implies (integerp i)
           (equal (logcar (+ i j))
                  (if (integerp j)
                      (b-xor (logcar j) (logcar i))
                    (if (acl2-numberp j)
                        0
                      (logcar i)))))
  :hints (("Goal" ;:do-not '(generalize eliminate-destructors)
           :in-theory (enable oddp logcar b-xor))))

(defthm logcar-+-alt
  (implies (integerp j)
           (equal (logcar (+ i j))
                  (if (integerp i)
                      (b-xor (logcar i) (logcar j))
                    (if (acl2-numberp i)
                        0
                      (logcar j)))))
  :hints (("Goal" :use (:instance logcar-+ (i j) (j i))
           :in-theory (disable logcar-+))))

(defthm logcar-evenp
  (implies (evenp x)
           (equal (logcar x)
                  0))
  :hints (("goal" :in-theory (enable logcar))))

(defthm logcar-*-1/2-expt
  (implies (< 0 n)
           (equal (logcar (* 1/2 (expt 2 n)))
                  (if (equal n 1)
                      1 0)))
  :hints (("goal" :in-theory (enable logcar))))

;or is LOGCAR-+ good enough?
(defthmd logcar-i+j+2*k
  (implies (and (integerp i)
                (integerp j)
                (integerp k))
           (equal (logcar (+ i j (* 2 k)))
                  (logcar (+ i j))))
  :hints (("Goal"
           :use ((:instance logcar-i+2*j (i (+ i j)) (j k))))))

(defthm logcar-range
  (and (<= (logcar i) 1)
       (<= 0 (logcar i))))


(defthm logcar-range-linear
  (and (<= (logcar i) 1)
       (<= 0 (logcar i)))
  :rule-classes :linear)

(defthm logcar-of-logcar
  (equal (logcar (logcar i))
         (logcar i))
  :hints (("Goal" :in-theory (enable logcar))))

(defthmd oddp-to-logcar
  (implies (integerp i)
           (equal (oddp i)
                  (equal 1 (logcar i))))
  :hints (("Goal" :in-theory (enable oddp))))

(defthmd oddp-rewrite-to-logcar-fact
  (implies (integerp x)
           (equal (oddp x)
                  (not (equal 0 (logcar x))))))

(defthm logcar-ash-pos
  (implies (and (< 0 n)
                (integerp n))
           (equal (logcar (ash x n))
                  0))
  :hints (("goal" :in-theory (enable logcar ash))))

(defthm evenp-of-logcar
  (equal (evenp (logcar m))
         (evenp (ifix m))))


;move
;think more about this
;might loop??
(defthm logcar-0-rewrite
  (equal (equal (logcar i) 0)
         (or (not (integerp i))
             (evenp i))))


(defthm logcar-of-times
  (implies (and (integerp x)
                (integerp y))
           (equal (logcar (* x y))
                  (if (or (evenp x)
                          (evenp y))
                      0
                    1))))

(in-theory (disable logbitp))

(defthm logbitp-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logbitp i j)
                  nil))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-when-j-is-zero
  (equal (logbitp i 0)
         nil)
  :hints (("goal" :in-theory (enable logbitp ifix))))

(defthm logbitp-when-i-is-zero
  (equal (logbitp 0 j)
         (equal (logcar j) 1))
  :hints (("goal" :in-theory (enable logbit logbitp))))

;further simplify the RHS?
(defthm logbitp-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logbitp i j)
                  (logbitp 0 j)))
  :hints (("Goal" :in-theory (enable logbitp
                                     ;oddp-rewrite-to-logcar-fact
                                     ))))

(defthm logbitp-when-i-is-non-positive
  (implies (<= i 0)
           (equal (logbitp i j)
                  (not (equal 0 (logcar j)))))
  :hints (("Goal" :in-theory (enable logbitp)
           :do-not '(generalize eliminate-destructors)
           )))

(defthm logbitp-0-minus-1-better-1
  (equal (logbitp pos 0)
         nil)
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbitp-0-minus-1-better-2
  (equal (logbitp pos -1)
         t)
  :hints (("Goal" :in-theory (enable logbitp))))

(in-theory (disable LOGBITP-0-MINUS-1))


;rule for logbit?
(defthm logbitp-of-one
  (equal (logbitp pos 1)
         (zp pos))
  :hints (("Goal" :cases ((zp pos))
           :in-theory (enable logbitp))))

;bzo gen
(defthm logbitp-of-expt-hack
  (implies (and (integerp size) (<= 0 size))
           (logbitp size (expt 2 size)))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm logbit-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logbit pos i)
                  0))
  :hints
  (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-zero
  (equal (logbit pos 0)
         0)
  :hints (("Goal" :in-theory (enable logbit))))

;go the other way too?
(defthm logbitp-forward-to-logbit-one
  (implies (logbitp n x)
           (equal 1 (logbit n x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbitp-forward-to-logbit-zero
  (implies (not (logbitp n x))
           (equal 0 (logbit n x)))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-when-i-is-non-positive
  (implies (<= i 0)
           (equal (logbit i j)
                  (logcar j)))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-logbit
  (equal (logbit pos1 (logbit pos2 i))
         (if (zp pos1)
             (logbit pos2 i)
           0))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm logbit-of-one
  (equal (logbit pos 1)
         (if (zp pos)
             1
           0))
  :hints (("Goal" :cases ((zp pos))
           :in-theory (enable logbit))))

(defthm unsigned-byte-p-of-logbit
  (implies (< 0 n)
           (equal (unsigned-byte-p n (logbit pos i))
                  (integerp n)))
  :hints (("Goal" :in-theory (enable logbit))))

(defthm unsigned-byte-p-of-logbit-fw
  (unsigned-byte-p 1 (logbit pos i))
  :rule-classes ((:forward-chaining :trigger-terms ((logbit pos i)))))

(in-theory (disable logapp))

(in-theory (disable (:TYPE-PRESCRIPTION LOGAPP))) ;we have logapp-type

(defthm logapp-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logapp size i j)
                  (ash j (nfix size))))
  :hints (("Goal" :in-theory (e/d (ash logapp) ()))))

(defthm logapp-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logapp size i j)
                  (loghead size i)))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm logapp-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (logapp size i j)
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logext
                                     LOGAPP))))

(defthm logapp-when-size-is-negative
  (implies (< size 0)
           (equal (logapp size i j)
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logext
                                     LOGAPP))))


(defthm my-logapp-<-0
  (equal (< (logapp size i j) 0)
         (< (ifix j) 0))
  :hints (("Goal" :use (:instance logapp-<-0 (i (ifix i)))
           :in-theory (disable logapp-<-0))))

(in-theory (disable LOGAPP-<-0))

(defthm logapp-non-negative-type-prescription
  (implies (<= 0 j)
           (<= 0 (logapp size i j)))
  :rule-classes :type-prescription)

(defthm logapp-negative-type-prescription
  (implies (and (< j 0)
                (integerp j))
           (< (logapp size i j) 0))
  :rule-classes :type-prescription)

(defthm logapp-non-negative-linear
  (implies (<= 0 j)
           (<= 0 (logapp size i j)))
  :rule-classes :linear)

(defthm logapp-negative-linear
  (implies (and (< j 0)
                (integerp j))
           (< (logapp size i j) 0))
  :rule-classes :linear)

;generalize?
(defthm logapp-of-logapp-with-same-size
  (equal (logapp size (logapp size i j1) j2)
         (logapp size i j2))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logapp))))

(defthm logapp-0-part-2-better
  (equal (logapp size 0 j)
         (ash j (nfix size)) ;(* (ifix i) (expt 2 (nfix size)))
         )
  :hints (("Goal" :in-theory (enable logapp ash))))

(defthm logapp-0-part-1-better
  (equal (logapp size i 0)
         (loghead size i))
  :hints (("Goal" :in-theory (enable logapp))))

(defthm logapp-0-part-3-better
  (equal (logapp 0 i j)
         (ifix j)
         )
  :hints (("Goal" :in-theory (enable logapp)))
  )

(in-theory (disable logapp-0))

(defthm evenp-of-logapp
  (equal (evenp (logapp size a b))
         (if (not (zp size))
             (evenp (ifix a))
           (evenp (ifix b))))
  :hints (("Goal" :in-theory (enable logapp))))

;; (defthm logcdr-logapp
;;   (implies (and (integerp x)
;;                 (integerp y)
;;                 (integerp n)
;;                 (< 0 n)
;;                 )
;;            (equal (LOGCDR (LOGAPP n x y))
;;                   (LOGAPP (+ -1 n) (logcdr x) y)))
;;   :hints (("Goal" :in-theory (enable logapp))))

(defthmd ash-as-logapp
  (implies (<= 0 n)
           (equal (ash x n)
                  (logapp n 0 x)))
  :hints (("goal" :in-theory (enable logapp ash))))

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|                                                                           |#
#|                                                                           |#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|===========================================================================|#
#|                                        ;
In this Acl2 book, we prove that the square root function can be approximated
in Acl2.  In particular, we prove the following theorem:

 (defthm convergence-of-iter-sqrt
   (implies (and (rationalp x)
                 (rationalp epsilon)
                 (< 0 epsilon)
                 (<= 0 x))
            (and (<= (* (iter-sqrt x epsilon) (iter-sqrt x epsilon)) x)
                 (< (- x (* (iter-sqrt x epsilon) (iter-sqrt x epsilon)))
                    epsilon))))

That is, for any non-negative number, we can approximate its square root within
an arbitrary positive epsilon.

The proof follows by introducing the bisection algorithm to approximate square
root.  Our bisection function looks like

    (iterate-sqrt-range low high x num-iters)

where low/high define the range being bisected, x is the number in whose square
root we're interested, and num-iters is the total number of iterations we wish
to perform.  This function returns a pair of numbers low' and high' which
define the resulting range.

The proof consists of two parts.  First of all, we show that for any high/low
range resulting from iterate-sqrt-range, if |high-low| is sufficiently small
(i.e., less than delta, which depends on epsilon) then |x-a^2| is less than
epsilon.  Secondly, we show that for any desired delta, we can find an adequate
num-iters so that calling iterate-sqrt-range with num-iters will result in a
high' and low' returned with |high'-low'| < delta.  The two proofs combined
give us our convergence result.

Note that we did not do the more natural convergence result, namely that after
iterating a number of times |low'-(sqrt x)| < epsilon.  The reason is that the
number (sqrt x) may not exist.  This result is shown in the companion book
"no-sqrt.lisp".  However, for those cases where (sqrt x) does exist, our proof
will naturally imply that (since we'll have a < (sqrt x) < b as a consequence
of a^2 < x < b^2 and also that |b-a| < delta < epsilon).  The interested reader
is encouraged to try that result.

To load this book, it is sufficient to do something like this:

    (certify-book "iter-sqrt" 0 nil)

|#

(local (in-theory (disable MOVE-NEGATED-TERM-TO-OTHER-SIDE-OF-<-TERM-2-ON-LHS ;why?
                           )))
;drop
(local (in-theory (enable (force)))) ;unfortunate that i had to do this

(local (in-theory (disable distributivity-alt)))

;(include-book (:relative :back "arithmetic" "top")
;              :load-compiled-file nil)

;;
;; We start out by defining the bisection approximation to square root.  At one
;; time, we experimented with making this function return two values, but that
;; led to all sorts of confusion.  So, we now return the cons of the new low
;; and high endpoints of the range.  Perhaps we'll go back and change this.
;;
(defun iterate-sqrt-range (low high x num-iters)
  (declare (type rational low high x)
           (type (integer 0 *) num-iters)
           (xargs :measure (nfix num-iters)))
  (if (<= (nfix num-iters) 0)
      (cons (rfix low) (rfix high))
    (let ((mid (/ (+ low high) 2)))
      (if (<= (* mid mid) x)
          (iterate-sqrt-range mid high x (1- num-iters))
        (iterate-sqrt-range low mid x
                            (1- num-iters))))))

;;
;; Acl2 doesn't seem to infer the type of the function above, so we give it
;; some help.  Hmmm, maybe this is a candidate for builtin-clause?
;;
(defthm iterate-sqrt-range-type-prescription
  (and (rationalp (car (iterate-sqrt-range low high x num-iters)))
       (rationalp (cdr (iterate-sqrt-range low high x num-iters)))))

;;
;; We will now show some basic properties of iterate-sqrt-range.  One important
;; property (since it'll be used in the induction hypotheses to come) is that
;; if the initial range is proper (i.e., non-empty and not a singleton), then
;; so are all resulting ranges from iterate-sqrt-root.
;;
(defthm iterate-sqrt-range-reduces-range
  (implies (and (rationalp low)
                (rationalp high)
                (< low high))
           (< (car (iterate-sqrt-range low high x
                                       num-iters))
              (cdr (iterate-sqrt-range low high x
                                       num-iters))))
  :rule-classes (:linear :rewrite))

;;
;; We had foolishly combined the two properties below into one, but then
;; discovered that in some cases we only had one of the needed hypothesis, so
;; we split the halves of the lemma.  The first half says that the high
;; endpoint of the range under consideration can only decrease.
;;
(defthm iterate-sqrt-range-non-increasing-upper-range
  (implies (and (rationalp low)
                (rationalp high)
                (< low high))
           (<= (cdr (iterate-sqrt-range low high x
                                        num-iters))
               high))
  :rule-classes (:linear :rewrite))

;;
;; Similarly, the lower endpoint can only increase.
;;
(defthm iterate-sqrt-range-non-decreasing-lower-range
  (implies (and (rationalp low)
                (rationalp high)
                (< low high))
           (<= low
               (car (iterate-sqrt-range low high x num-iters))))
  :rule-classes (:linear :rewrite))

;;
;; Another property we need is that if the high endpoint starts out above the
;; square root of x, it will never be moved below its square root....
;;
(defthm iterate-sqrt-range-upper-sqrt-x
  (implies (and (rationalp low)
                (rationalp high)
                (rationalp x)
                (<= x (* high high)))
           (<= x
               (* (cdr (iterate-sqrt-range low high x
                                           num-iters))
                  (cdr (iterate-sqrt-range low high x
                                           num-iters))
                  )))
  :rule-classes (:linear :rewrite))

;;
;; ....And likewise for the lower endpoint.
;;
(defthm iterate-sqrt-range-lower-sqrt-x
  (implies (and (rationalp low)
                (rationalp high)
                (rationalp x)
                (<= (* low low) x))
           (<= (* (car (iterate-sqrt-range low high x num-iters))
                  (car (iterate-sqrt-range low high x num-iters)))
               x))
  :rule-classes (:linear :rewrite))

;;
;; We are now trying to prove that if the final range is small enough, then the
;; squares of the endpoints are very close to x.  To do that, we have to prove
;; some inequalities of real numbers (er, I mean rationals).  We're working too
;; hard here, and that makes us suspicious.  We're doing _something_ wrong, and
;; we're very open to suggestions.
;;

;;
;; For the second half of the proof, we have to reason about how quickly the
;; ranges become small.  Since we halve the range at each step, it makes to
;; start out by introducing the computer scientist's favorite function:
;;

;get rid of this by replacing its uses with its body?
(defun 2-to-the-n (n)
  (declare (type (integer 0 *) n))
  (expt 2 n)
  )

;; (defun 2-to-the-n (n)
;;   (declare (type (integer 0 *) n))
;;   (if (<= (nfix n) 0)
;;       1
;;     (* 2 (2-to-the-n (1- n)))))

;;
;; This function is used to figure out how many iterations of iter-sqrt-range
;; are needed to make the final range sufficiently small.  Since one can't
;; recurse on the rationals, we take the ceiling first, so that we can reason
;; strictly about integers.
;;
(defun guess-num-iters-aux (range num-iters)
  (declare (type rational range)
           (type (integer 0 *) num-iters)
           (xargs :measure (nfix (- range (2-to-the-n num-iters)))))
  (if (and (integerp range)
           (integerp num-iters)
           (> num-iters 0)
           (> range (2-to-the-n num-iters)))
      (guess-num-iters-aux range (1+ num-iters))
    (1+ (nfix num-iters))))

;;
;; Now, we're ready to define our square-root approximation function.  All it
;; does is initialize the high/low range, find a suitable delta, convert this
;; to a needed num-iters, and then return the low endpoint of the resulting
;; call to iter-sqrt-range.
;;
(defun iter-sqrt (x epsilon)
  (declare (type rational x epsilon)
           (xargs :guard (< 0 epsilon)))
  (if (and (rationalp x)
           (<= 0 x))
      (let ((low 0)
            (high (if (> x 1) x 1)))
        (let ((range (iterate-sqrt-range
                      low high x
                      (guess-num-iters (- high low)
                                       (/ epsilon
                                          (+ high
                                             high))))))
          (car range)))
    nil))

;;
;; To show how quickly the function converges, we teach Acl2 a simple way to
;; characterize the final range from a given initial range.  As expected, the
;; powers of two feature prominently :-)
;;
(defthm iterate-sqrt-reduces-range-size
  (implies (and (<= (* low low) x)
                (<= x (* high high))
                (rationalp low)
                (rationalp high)
                (integerp num-iters)
                (<= 0 num-iters)
                )
           (let ((range (iterate-sqrt-range low high x
                                            num-iters)))
             (equal (- (cdr range) (car range))
                    (/ (- high low)
                       (2-to-the-n num-iters)))))
  :hints (("Goal" :induct t
           :expand (EXPT 2 NUM-ITERS) ;gross!
           :in-theory (e/d (expt) (ARITH-MOVE-NEGATED-TERM
                                   EXPT-2-CRUNCHER)))))

;;
;; So now, we show that our function to compute needed num-iters does produce a
;; large enough num-iters.  First, we study the recursive function....
;;
(defthm guess-num-iters-aux-is-a-good-guess
  (implies (and (integerp x)
                (integerp num-iters)
                (> x 0)
                (> num-iters 0))
           (< x (2-to-the-n (guess-num-iters-aux x num-iters))))
  :rule-classes (:linear :rewrite)
  :hints (("Goal" :expand ((EXPT 2 (+ 1 NUM-ITERS))))))

;;
;; ...now, we convert that to the non-recursive front-end. This is where we
;; need to reason heavily about ceiling.
;;
(defthm guess-num-iters-is-a-good-guess
  (implies (and (rationalp range)
                (rationalp delta)
                (> range 0)
                (> delta 0))
           (< (/ range delta) (2-to-the-n (guess-num-iters range delta))))
  :hints (("Goal"
           :use ((:instance ceiling-greater-than-quotient (x range) (y delta))
                 (:instance guess-num-iters-aux-is-a-good-guess
                            (x (ceiling range delta))
                            (num-iters 1))
                 (:instance <-*-left-cancel
                            (z delta)
                            (x (ceiling range delta))
                            (y (2-to-the-n (guess-num-iters-aux (ceiling
                                                                 range
                                                                 delta)
                                                                1)))))
           :in-theory (disable ceiling
                               <-*-left-cancel
                               ceiling-greater-than-quotient
                               guess-num-iters-aux-is-a-good-guess))))

(in-theory (disable
            LOGNOT
            LOGCOUNT
            LOGBITP
            TRUE-LIST-LISTP
            SIGNED-BYTE-P
            UNSIGNED-BYTE-P
            INTEGER-LENGTH
            BINARY-LOGAND
            LOGNAND
            BINARY-LOGIOR
            LOGORC1
            LOGORC2
            LOGANDC1
            LOGANDC2
            BINARY-LOGEQV
            BINARY-LOGXOR
            LOGNOR
            BITP
            logcar
            LOGCDR
            LOGCONS
            LOGBIT
            LOGMASK
            LOGMASKP
            LOGHEAD
            LOGTAIL
            LOGAPP
            LOGRPL
            LOGEXT
            LOGREV1
            LOGREV
            LOGSAT
            LOGEXTU
            LOGNOTU
            ASHU
            BSPP
            ))

;; induction schemes

(defun add1-add1-logcdr-induction (x y z)
  (declare (xargs :measure (abs (ifix x))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix x))
      (or y z)
    (add1-add1-logcdr-induction (1+ x) (1+ y) (logcdr z))))

(defun add1-add1-induction (x y)
  (declare (xargs :measure (abs (ifix x))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix x))
      y
    (add1-add1-induction (1+ x) (1+ y))))


(defun add1-logcdr-logcdr-induction (m x y)
  (declare (xargs :measure (abs (ifix m))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix m))
      (or x y)
    (add1-logcdr-logcdr-induction (1+ m) (logcdr x) (logcdr y))))


(defun logcdr-induction (x)
  (if (or (equal x -1) (zip x))
      t
    (logcdr-induction (logcdr x))))


(defun sub1-induction (x)
  (if (zp x)
      x
    (sub1-induction (1- x))))


(defun add1-sub1-induction (a b)
  (declare (xargs :measure (abs (ifix a))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix a))
      b
    (add1-sub1-induction (1+ a) (1- b))))


(defun add1-induction (x)
  (declare (xargs :measure (abs (ifix x))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix x))
      x
    (add1-induction (1+ x))))


(defun sub1-logcdr-logcdr-induction (m x y)
  (if (zp m)
      (or x y)
    (sub1-logcdr-logcdr-induction (1- m) (logcdr x) (logcdr y))))


(defun logcdr-logcdr-logcdr-induction (a b c)
  (declare (xargs :measure (abs (ifix a))
                  :hints (("goal" :in-theory (enable logcdr)))))
  (if (or (equal a -1) (zip a))
      (or b c)
    (logcdr-logcdr-logcdr-induction (logcdr a) (logcdr b) (logcdr c))))


(defun add1-logcdr-induction (m x)
  (declare (xargs :measure (abs (ifix m))
                  :hints (("goal" :in-theory (enable ifix)))))
  (if (<= 0 (ifix m))
      x
    (add1-logcdr-induction (1+ m) (logcdr x))))


(defun logcdr-logcdr-induction (b c)
  (declare (xargs :measure (abs (ifix b))
                  :hints (("goal" :in-theory (enable logcdr)))))
  (if (or (equal b -1) (zip b))
      c
    (logcdr-logcdr-induction (logcdr b) (logcdr c))))


(defun sub1-logcdr-induction (m x)
  (if (zp m)
      x
    (sub1-logcdr-induction (1- m) (logcdr x))))


(defun sub1-sub1-induction (m n)
  (if (zp m)
      n
    (sub1-sub1-induction (1- m) (1- n))))


(defun sub1-sub1-logcdr-induction (a b v)
  (if (zp b)
      (or a v)
    (sub1-sub1-logcdr-induction (1- a) (1- b) (logcdr v))))

(defun sub1-sub1-logcdr-logcdr-induction (a b x v)
  (if (zp b)
      (or a v x)
    (sub1-sub1-logcdr-logcdr-induction (1- a) (1- b) (logcdr x) (logcdr v))))


(defun add1-sub1-logcdr-induction (a b v)
  (if (zp b)
      (or a v)
    (add1-sub1-logcdr-induction (1+ a) (1- b) (logcdr v))))

(defun sub1-logcdr-logcdr-carry-induction (m x y c)
  (if (zp m)
      (or x y c)
    (sub1-logcdr-logcdr-carry-induction
     (1- m)
     (logcdr x)
     (logcdr y)
     (b-ior (b-and (logcar x) (logcar y))
            (b-ior (b-and (logcar x) c)
                   (b-and (logcar y) c))))))

(defun sub1-logcdr-logcdr-logcdr-carry-induction (m x y z c)
  (if (zp m)
      (or x y c z)
    (sub1-logcdr-logcdr-logcdr-carry-induction
     (1- m)
     (logcdr x)
     (logcdr y)
     (logcdr z)
     (b-ior (b-and (logcar x) (logcar y))
            (b-ior (b-and (logcar x) c)
                   (b-and (logcar y) c))))))

(defun sub1-sub1-logcdr-logcdr-carry-induction (m n x y c)
  (if (or (zp m) (zp n))
      (or x y c)
    (sub1-sub1-logcdr-logcdr-carry-induction
     (1- m)
     (1- n)
     (logcdr x)
     (logcdr y)
     (b-ior (b-and (logcar x) (logcar y))
            (b-ior (b-and (logcar x) c)
                   (b-and (logcar y) c))))))

;; now let's try to get acl2 to automatically guess the right inductions to use:

(defund logendp (x)
  (declare (xargs :guard (integerp x)))
  (or (zip x)
      (= x -1)))

(defun b-maj (a b c)
  (declare (xargs :guard (and (bitp a)
                              (bitp b)
                              (bitp c))))
  (b-ior (b-and a b)
         (b-ior (b-and a c)
                (b-and b c))))

;; (if (or (and (equal a 1) (equal b 1))
;;           (and (equal a 1) (equal c 1))
;;           (and (equal b 1) (equal c 1)))
;;       1 0))

(defthm logcdr-logend-acl2-count
  (implies (not (logendp x))
           (< (acl2-count (logcdr x))
              (acl2-count x)))
  :hints (("goal" :in-theory (enable logcdr logendp
                                     )))
  :rule-classes :linear)

(local
 (defthm logcdr-logend-acl2-count-2
   (implies (or (zip x) (equal x -1))
            (equal (logcdr x)
                   (ifix x)))
   :hints (("goal" :in-theory (enable logcdr)))))

(defthm logcdr-logend-acl2-count-3
  (<= (acl2-count (logcdr x))
      (acl2-count x))
  :hints (("goal" :in-theory (enable logcdr)))
  :rule-classes :linear)

(defun +-r (a b c)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))
                  :hints (("goal" :in-theory (disable acl2-count)))))
  (if (and (logendp a)
           (logendp b))
      c
    (+-r (logcdr a)
         (logcdr b)
         (b-maj (logcar a) (logcar b) c))))

(defthm +-induction t
  :rule-classes ((:induction :pattern (+ a b c)
                             :condition (unsigned-byte-p 1 c)
                             :scheme (+-r a b c))))

(defun lognotr (x)
  (declare (xargs :hints (("Goal" :in-theory (enable logendp)))))
  (or (logendp x)
      (lognotr (logcdr x))))

(defthm lognot-induction t
  :rule-classes ((:induction :pattern (lognot x)
                             :condition t
                             :scheme (lognotr x))))

(defun logbinr (x y)
  (declare (xargs :hints (("goal" :in-theory (disable acl2-count)))))
  (or (logendp x)
      (logendp y)
      (logbinr (logcdr x) (logcdr y))))

(defthm logand-induction t
  :rule-classes ((:induction :pattern (logand x y)
                             :condition t
                             :scheme (logbinr x y))))

(defthm logior-induction t
  :rule-classes ((:induction :pattern (logior x y)
                             :condition t
                             :scheme (logbinr x y))))

(defthm logxor-induction t
  :rule-classes ((:induction :pattern (logxor x y)
                             :condition t
                             :scheme (logbinr x y))))

(defun loglistr (n x)
  (if (zp n)
      (ifix x)
    (logcons 0 (loglistr (1- n) (logcdr x)))))

(defun loglist-fwd-r (n x)
  (cond ((zip n) (ifix x))
        ((< n 0) (loglist-fwd-r (1+ n) x))
        (t (logcons 0 (loglist-fwd-r (1- n) (logcdr x))))))

(defun loglist-bwd-r (n x)
  (cond ((zip n) (ifix x))
        ((< n 0) (loglist-bwd-r (1+ n) (logcdr x)))
        (t (logcons 0 (loglist-bwd-r (1- n) x)))))



(defthm logtail-induction t
  :rule-classes ((:induction :pattern (logtail n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm sbp-induction t
  :rule-classes ((:induction :pattern (signed-byte-p n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm ubp-induction t
  :rule-classes ((:induction :pattern (unsigned-byte-p n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm logbitp-induction t
  :rule-classes ((:induction :pattern (logbitp n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm logext-induction t
  :rule-classes ((:induction :pattern (logext n x)
                             :condition t
                             :scheme (loglistr n x))))

(defthm logapp-induction t
  :rule-classes ((:induction :pattern (logapp n x y)
                             :condition t
                             :scheme (loglistr n x))))

(defthm ash-induction t
  :rule-classes ((:induction :pattern (ash x n)
                             :condition t
                             :scheme (loglist-bwd-r n x))))

;; when we see (foo n (ash x m)) where foo is a function that recurses
;; using loglist-fwd-r, we use the following induction.

(defun loglist-ashr (m n x)
  (cond ((or (zip m) (zp n)) x)
        ((< m 0) (loglist-ashr (1+ m) n (logcdr x)))
        (t (loglist-ashr (1- m) (1- n) x))))

(defthm loglist-ash-induction t
  :rule-classes ((:induction :pattern (loglistr n (ash x m))
                             :condition t
                             :scheme (loglist-ashr m n x))))

;swap fwd and bwd if n is negated:

(defthm loglistr-- t
  :rule-classes ((:induction :pattern (loglistr (- n) x)
                             :condition t
                             :scheme (loglist-bwd-r n x))))

(defthm loglist-fwd-r-- t
  :rule-classes ((:induction :pattern (loglist-fwd-r (- n) x)
                             :condition t
                             :scheme (loglist-bwd-r n x))))

(defthm loglist-bwd-r-- t
  :rule-classes ((:induction :pattern (loglist-bwd-r (- n) x)
                             :condition t
                             :scheme (loglist-fwd-r n x))))

;and ignore the negation of x:

(defthm loglistr--2 t
  :rule-classes ((:induction :pattern (loglistr n (- x))
                             :condition t
                             :scheme (loglistr n x))))

(defthm loglist-fwd-r--2 t
  :rule-classes ((:induction :pattern (loglist-fwd-r n (- x))
                             :condition t
                             :scheme (loglist-fwd-r n x))))

(defthm loglist-bwd-r--2 t
  :rule-classes ((:induction :pattern (loglist-bwd-r n (- x))
                             :condition t
                             :scheme (loglist-bwd-r n x))))



;combining the induction schemes for + and the above loglist-fwd-r rules:

(defthm loglist-+-induction t
   :rule-classes ((:induction :pattern (loglistr n (+ x y c))
                              :condition t
                              :scheme (sub1-logcdr-logcdr-carry-induction n
                                                                          x
                                                                          y
                                                                          c))))

;same for lognot:

(defthm loglist-lognot-induction t
  :rule-classes ((:induction :pattern (loglistr n (lognot x))
                             :condition t
                             :scheme (loglistr n x))))

;now some rules combining specific loglist functions with loglist:

(defun loglist-loglistr (m n x)
  (if (or (zp m)
          (zp n))
      x
    (loglist-loglistr (1- m) (1- n) (logcdr x))))

(defthm loglist-loghead t
  :rule-classes ((:induction :pattern (loglistr n1 (loghead n2 x))
                             :condition t
                             :scheme (loglist-loglistr n2 n1 x))))

;; use loglistr instead?
;; (defun logappr (n x y)
;;   (if (zp n)
;;       y
;;     (logcons (logcar x) (logappr (1- n) (logcdr x) y))))


(defun logmaskpr (x)
  (declare (xargs :hints (("goal" :in-theory (disable acl2-count)))))
  (if (logendp x)
      nil
    (logcons nil (logmaskpr (logcdr x)))))



(defthm logmaskp-induction t
  :rule-classes ((:induction :pattern (logmaskp x)
                             :condition t
                             :scheme (logmaskpr x))))

(in-theory (disable logand-bit-0
                    logand-bit-1
                    logand-bfix
                    ))

(local (in-theory (enable open-logcons))) ;why?

(defthm logior-of-sum-with-negative-of-expt-const-version
   (implies (and (syntaxp (quotep k))
                 (equal k (- (expt 2 (expo k))))
                 (unsigned-byte-p (expo k) y))
            (equal (logior k y)
                   (+ y k)))
   :hints (("Goal" :use (:instance logior-of-sum-with-negative-of-expt-alt (n (expo k)))
            :in-theory (disable  logior-of-sum-with-negative-of-expt-alt))))



;; hack for the microprocessor proofs
;compare to logext-open-logbit-sign-known
;; (defthm if-to-logext
;;   (implies (and (integerp n)
;;                 (< 0 n)
;;                 (unsigned-byte-p n y))
;;            (equal (if (equal 0 (logand (expt 2 (1- n)) y))
;;                       y
;;                     (logior (- (expt 2 n)) y))
;;                   (logext n y)))
;;   :rule-classes nil
;;   :hints (("goal" :in-theory (e/d (LOGAND---EXPT-REWRITE
;;                                    ;LOGIOR-AS-+ use this and not the "special-case" lemma above?
;;                                    ) (logext-open-logbit-sign-known))
;;            :use ((:instance logior-of-sum-with-negative-of-expt)
;;                  (:instance logext-open-logbit-sign-known (x y) (n2  (+ -1 N)))))))



; get rid of mention of nth?
;; (defthm logbitp-of-bit-bridge
;;   (implies (and (integerp n)
;;                 (< 0 n)
;;                 (unsigned-byte-p 1 (nth a x)))
;;            (not (logbitp n (nth a x))))
;;   :hints (("goal"
;;            :in-theory (enable unsigned-byte-p logbitp*)
;;            :cases ((equal (nth a x) 0)))))

; These hacks needed for mpc reasoning, since we are concerned about
; carry bit of the lower byte


;bzo ;generalize this?
(defthm unsigned-byte-p-+-*4-bridge
  (implies (and (unsigned-byte-p 2 p)
                (unsigned-byte-p (- n 2) x)
                (< 1 n)
                (integerp n)
                (integerp p)
                )
           (unsigned-byte-p n (+ p (* 4 x))))
  :hints (("Goal" :in-theory (e/d (logapp) ( UNSIGNED-BYTE-P-LOGAPP))
           :use (:instance UNSIGNED-BYTE-P-LOGAPP (size n) (size1 2) (i p) (j x)))))

;; ;drop??? see next lemma
;; (defthmd logcdr-all-ones-lemma
;;   (implies (and (not (unsigned-byte-p n (1+ x)))
;;                 (unsigned-byte-p n x)
;;                 (integerp n)
;;                 (< 0 n)
;;                 )
;;            (equal (logcdr x)
;;                   (loghead (1- n) -1)))
;;   :rule-classes nil
;;   :hints (("goal"
;;            :induct (unsigned-byte-p n x)
;;            :in-theory (enable LRDT))))

;If X is an unsigned-byte of length N, then saying that X+1 is also an unsigned-byte of length N is the same as
;saying that X isn't all ones.
(defthm unsigned-byte-p-of-x+1
  (implies (and (syntaxp (not (quotep x))) ;keeps ACL2 from being fancy with unification
                (unsigned-byte-p n x))
           (equal (unsigned-byte-p n (+ 1 x))
                  (and (integerp n)
                       (<= 0 n)
                       (not (equal x
                                   (loghead n -1) ;all ones!
                                   )))))
  :hints (("goal"
           :induct (unsigned-byte-p n x)
           :in-theory (e/d (LRDT) (unsigned-byte-p* ;for acl2 3.0
                                   )))))

(local (in-theory (disable logcons-of-0)))

(defthm logbitp-to-bound-when-usb
  (implies (UNSIGNED-BYTE-P N X)
           (equal (LOGBITP (+ -1 N) x)
                  (<= (expt 2 (+ -1 n)) x)))
  :hints (("Goal" :in-theory (enable LOGBITP))))

(defthm logbitp-to-bound-when-usb
  (implies (UNSIGNED-BYTE-P N X)
           (equal (LOGBITP (+ -1 N) x)
                  (<= (expt 2 (+ -1 n)) x)))
  :hints (("Goal" :in-theory (enable LOGBITP))))

(defthm logbit-to-bound-when-usb
  (implies (UNSIGNED-BYTE-P N X)
           (equal (equal 0 (LOGBIT (+ -1 N) x))
                  (< x (expt 2 (+ -1 n)))))
  :hints (("Goal" :in-theory (disable LOGBITP-TO-BOUND-WHEN-USB)
           :use (:instance logbitp-to-bound-when-usb))))

(defthm logand-non-negative
  (implies (or (<= 0 x) (<= 0 y))
           (<= 0 (logand x y)))
  :hints (("Goal" :in-theory (enable logand)
           :do-not '(generalize eliminate-destructors))))


(defthm logand-associative
  (equal (logand (logand i j) k)
         (logand i (logand j k))))

(defthm logand-commutative-2
  (equal (logand j i k)
         (logand i j k)))

;slightly different from what we have in rtl
(defthm logand-x-x
  (equal (logand x x)
         (if (integerp x)
             x
           0)))

(defthm logxor-associative
  (equal (logxor (logxor i j) k)
         (logxor i (logxor j k))))

(defthm logxor-commutative-2
  (equal (logxor j i k)
         (logxor i j k)))

(defthm logxor-self
  (equal (logxor i i)
         0))

(defthm logior-associative
  (equal (logior (logior i j) k)
         (logior i (logior j k))))

(defthm logior-commutative-2
  (equal (logior j i k)
         (logior i j k)))

(defthm expt-2-positive-rational-type
  (and (rationalp (expt 2 i))
       (< 0 (expt 2 i)))
  :rule-classes (:rewrite (:type-prescription :typed-term (expt 2 i))))

(defthm integerp-sum-take-out-known-integer
   (implies (integerp n)
            (and (equal (integerp (+ n x))
                        (integerp (fix x)))
                 (equal (integerp (+ x n))
                        (integerp (fix x))))))

(defthm integerp-sum-take-out-known-integer-3
  (implies (integerp n)
           (and ;(equal (integerp (+ n x y))      ;this case not needed?
                 ;      (integerp (fix (+ x y))))
                (equal (integerp (+ x n y))
                       (integerp (fix (+ x y))))
                (equal (integerp (+ x y n))
                       (integerp (fix (+ x y)))))))

;this is better than EXPT2-INVERSE-INTEGER in the RTL books
(defthm integerp-of-inverse-of-expt
  (equal (integerp (/ (expt 2 n)))
         (or (not (integerp n))
             (<= n 0))))

;this is better than the one in RTL
;make a linear rule?
(defthm logior-bnd-eric
  (equal (<= x (logior x y))
         (if (integerp x)
             (if (integerp y)
                 (or (<= 0 y)
                     (< x 0))
               t)
           (<= x (ifix y))))
  :hints (("Goal" :in-theory (e/d () (LESS-THAN-MULTIPLY-THROUGH-BY-INVERTED-FACTOR-FROM-LEFT-HAND-SIDE
                                      FL-<-INTEGER
                                      FL->-INTEGER
;FL-LOGIOR-BY-2
                                      FL-OF-EVEN/2
                                      )
                                  )
           :induct (LOG-INDUCT-allows-negatives x y))
          ("Subgoal *1/2" :use ((:instance logior-def (i x) (j y))
                                (:instance quot-mod (m x) (n 2))
;(:instance mod012)
;(:instance mod012 (x y))
                                ))))

(defthm logior-bnd-eric-linear
  (implies (and (integerp x)
                (or (<= 0 y)
                    (< x 0))
                )
         (<= x (logior x y)))
  :rule-classes ((:linear :trigger-terms ((logior x y))))
  :hints (("Goal" :use (:instance logior-bnd-eric)
           :in-theory (disable logior-bnd-eric)
           )))


;we disable this, because it can cause problems
(DEFthmd MOD-CANCEL
  (IMPLIES
   (SYNTAXP (NOT (AND (QUOTEP Y) (EQUAL (CADR Y) 1))))
   (EQUAL (MOD X Y)
          (IF (ACL2-NUMBERP X)
              (IF (ACL2-NUMBERP Y)
                  (IF (EQUAL 0 Y) X (* Y (MOD (/ X Y) 1)))
                  X)
              0))))



(DEFTHM INTEGERP-SUM-OF-ODDS-OVER-2-LEADING-CONSTANT
  (IMPLIES (AND (SYNTAXP (AND (QUOTEP X)
                              (INTEGERP (* 2 X))
                              (NOT (INTEGERP X))))
                (RATIONALP X)
                (RATIONALP Y)
                (INTEGERP (* 2 X))
                (NOT (INTEGERP X))
                (INTEGERP (* 2 Y))
                (NOT (INTEGERP Y)))
           (INTEGERP (+ X Y))))


(defthm equal-1-hack
  (implies (and (integerp x)
                (< x 2)
                (< 0 x))
           (equal (equal x 1)
                  t)))

;bzo rtl can prove this with equal-1-hack
(defthm rtl-a-million
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (< I Y)
                (NOT (EQUAL I 0))
                (INTEGERP Y)
                (<= 0 Y)
                (INTEGERP (+ (/ Y) (* I (/ Y)))))
           (EQUAL (+ (/ Y) (* I (/ Y))) 1)))

(defthm rtl
  (IMPLIES (AND (INTEGERP I)
                     (INTEGERP I0)
                     (< I 32768)
                     (<= 32768 (+ I (* 32768 I0)))
                     (< 0 I0)
                     (<= 0 I0)
                     (INTEGERP (* 1/2 (FLOOR (* 1/16384 I) 1))))
                (< I 16384)))

;bzo from-rtl
(DEFthm MOD-SUMS-CANCEL-3
  (IMPLIES (AND (CASE-SPLIT (<= 0 Y))
                (CASE-SPLIT (RATIONALP K))
                (CASE-SPLIT (RATIONALP Y))
                (CASE-SPLIT (RATIONALP X1))
                (CASE-SPLIT (RATIONALP X2)))
           (EQUAL (EQUAL (MOD (+ X1 K) Y)
                         (MOD (+ X2 K) Y))
                  (EQUAL (MOD X1 Y) (MOD X2 Y)))))

(defund loghead-30-exec (i)
  (declare (type (unsigned-byte 31) i))
  (the-usb 31 (logand 1073741823 i)))

(defthm loghead-30-exec-rewrite
  (equal (loghead-30-exec i)
         (loghead 30 i))
  :hints (("Goal" :in-theory (enable loghead-30-exec))))

(defund logbitp-30-exec (j)
  (declare (type (unsigned-byte 31) j))
  (not (equal 0 (logand 1073741824 j))))

(defthm logbitp-30-exec-rewrite
  (equal (logbitp-30-exec i)
         (logbitp 30 i))
  :hints (("Goal" :cases ((integerp i))
           :in-theory (enable logbitp-30-exec))))

;bzo I think this version doesn't do the chop that logapp does.  Make a
;version that does do the chop (and that won't need the (unsigned-byte-p 31 x)
;hyp to be equal to (logext 31 x)?
;
;bzo inline the function calls here?
(defund logext-31-exec (x)
  (declare (type (unsigned-byte 31) x))
  (the-sb 31 (if (not (equal 0 (logand 1073741824 x))) ;(logbitp-30-exec x)
                 (the-sb 31 (+ -1073741824 (the-usb 30 (logand 1073741823 x) ;(loghead-30-exec x)
                                                    ))) ;(logapp 30 x -1);
               x)))

(defthm logext-31-exec-rw
  (implies (unsigned-byte-p 31 x)
           (equal (logext-31-exec x)
                  (logext 31 x)))
  :hints (("Goal" :in-theory (enable LOGEXT logext-31-exec))))

(in-theory (disable evenp))

;; (defthm evenp-fc
;;   (implies (evenp x)
;;            (integerp (* 1/2 x)))
;;   :rule-classes :forward-chaining)

;; (defthm evenp-rw
;;   (implies (integerp (* 1/2 x))
;;            (evenp x))
;;   :rule-classes ((:rewrite :backchain-limit-lst 2)))

;better than the version in the RTL library
(defthmd even-int-implies-int2
  (implies (integerp (* 1/2 x))
           (equal (integerp x)
                  (acl2-numberp x)
                  ))
  :rule-classes ((:rewrite :backchain-limit-lst (1)))
  :hints (("Goal" :in-theory (disable integerp-prod)
           :use (:instance integerp-prod (x (* 1/2 x)) (y 2)))))

(defthm evenp-when-not-integerp
  (implies (not (integerp x))
           (equal (evenp x)
                  (not (acl2-numberp x))))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm evenp-forward-to-integerp
  (implies (and (evenp x)
                (acl2-numberp x))
           (integerp x))
  :rule-classes :forward-chaining)

;improve?
(defthm evenp-
  (implies (integerp a)
           (equal (evenp (- a))
                  (evenp a)))
  :hints (("goal" :in-theory (enable evenp))))

;move hyps to conclusion?
(defthm evenp-expt
  (implies (and (<= 0 y)
                (integerp y)
                (integerp x) ; usually x will be 2
                )
           (equal (evenp (expt x y))
                  (and (not (equal y 0))
                       (evenp x))))
  :hints (("goal" :in-theory (enable expt))))

;special case when the base of exponentiation is 2
;
(defthm evenp-of-expt2-better
  (equal (evenp (expt 2 y))
         (and (integerp y)
              (< 0 y)))
  :hints (("Goal" :in-theory (e/d (evenp) ()))))

;;
;; ODDP
;;

(in-theory (disable oddp))

;redundant?
;more like this?
(defthm oddp-forward-to-not-evenp
  (implies (oddp x)
           (not (evenp x)))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

(defthm evenp-forward-to-not-oddp
  (implies (evenp x)
           (not (oddp x)))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

(defthm not-oddp-forward-to-evenp
  (implies (not (oddp x))
           (evenp x))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

(defthm not-evenp-forward-to-oddp
  (implies (not (evenp x))
           (oddp x))
  :hints (("Goal" :in-theory (enable oddp)))
  :rule-classes :forward-chaining)

;induction shouldn't be needed here if we improve evenp-expt-2?
(defthm oddp-of-expt
  (equal (oddp (expt 2 j))
         (or (not (integerp j))
             (<= j 0)))
  :hints (("Goal" :in-theory (enable oddp
                                     expt ;improve evenp rule and drop
                                     EXPONENTS-ADD-UNRESTRICTED))))

;consider adding (disabled!) versions of these without the backchain-limits?
(defthmd even-odd-different-1
  (implies (and (evenp a)
                (not (evenp b)))
           (not (equal a b)))
  :rule-classes ((:rewrite :backchain-limit-lst 5)))

;bzo do we need both of these rules?
;consider adding (disabled!) versions of these without the backchain-limits?
(defthmd even-odd-different-2
  (implies (and (not (evenp a))
                (evenp b))
           (not (equal a b)))
  :rule-classes ((:rewrite :backchain-limit-lst 5)))

(defthm oddp-+
  (implies (and (integerp a) (integerp b))
           (equal (oddp (+ a b))
                  (not (equal (oddp a) (oddp b)))))
  :hints (("Goal" :in-theory (enable oddp))))

;improve?
(defthm oddp-minus
  (implies (integerp x)
           (equal (oddp (- x))
                  (oddp x)))
  :hints (("Goal" :in-theory (enable oddp))))

(defthm oddp-of-*
  (implies (and (integerp a)
                (integerp b)
                )
           (equal (oddp (* a b))
                  (and (oddp a) (oddp b))))
  :hints (("Goal" :in-theory (enable oddp))))



;clean this up!

(defthm *ark*-|+1-*2-is-different-from-*2|
  (implies (and (integerp a) (integerp b))
           (not (equal (1+ (* 2 a)) (* 2 b))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))

;generalize to say expt is not equal to something odd?
(defthm *ark*-equal-1+-*2
  (implies
   (and (integerp a) (integerp b)
         (<= 0 a))
   (equal (equal (expt 2 a) (1+ (* 2 b)))
          (and (zp a) (zip b))))
  :hints (("goal" :in-theory (enable expt))))

(defthm *ark*-equal-1+-+-*2-*2
  (implies (and (integerp a) (integerp b) (integerp c)
                (<= 0 a))
           (equal (equal (expt 2 a) (+ 1 (* 2 b) (* 2 c)))
                  (and (zp a) (zip (+ b c)))))
  :hints (("goal" :use (:instance *ark*-equal-1+-*2 (b (+ b c))))))


;dividing through by 2 should get this...
(defthmd *ark*-+3-*2-is-different-from-*2
        (implies (and (integerp a) (integerp b))
                 (not (equal (+ 3 (* 2 a)) (* 2 b))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))

(defthm *ark*-equal-+3-*2
  (implies
   (and (integerp a) (integerp b)
        (<= 0 a))
   (equal
    (equal (expt 2 a) (+ 3 (* 2 b)))
    (and (zp a) (equal b -1))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))

;why induction here?
(defthm *ark*-equal-+3-+-*2-*2
  (implies (and (integerp a) (integerp b) (integerp c)
                (<= 0 a))
           (equal (equal (expt 2 a) (+ 3 (* 2 b) (* 2 c)))
                  (and (zp a) (equal (+ b c) -1))))
  :hints (("Goal" :in-theory (enable EVEN-ODD-DIFFERENT-1
                                     EVEN-ODD-DIFFERENT-2))))


(defthm equal-i+-*2
  (implies (and (integerp a)
                (integerp b)
                (integerp i)
                (<= 0 a)
                (not (evenp i)))
           (equal (equal (expt 2 a) (+ i (* 2 b)))
                  (and (zp a) (equal b (- (* 1/2 (+ -1 i)))))))
  :hints (("Goal" :in-theory (enable even-odd-different-2 even-odd-different-1))))

(defthm equal-i+-+-*2-*2
  (implies (and (integerp a)
                (integerp b)
                (integerp c)
                (integerp i)
                (<= 0 a)
                (not (evenp i)))
           (equal (equal (expt 2 a) (+ i (* 2 b) (* 2 c)))
                  (and (zp a) (equal (+ b c) (- (* 1/2 (+ -1 i)))))))
    :hints (("Goal" :in-theory (enable even-odd-different-2 even-odd-different-1))))


;; (defthm +i-*2-is-different-from-*2
;;   (implies (and (integerp a)
;;                 (integerp b)
;;                 (integerp i)
;;                 (not (evenp i)))
;;            (not (equal (+ i (* 2 a)) (* 2 b)))))
;;   :hints (("goal"
;;            :use ((:instance evenp-+
;;                             (a i)
;;                             (b (* 2 a)))))))

(defthm mod-by-2-equals-1--rewrite-to-oddp
  (implies (integerp i)
           (equal (equal (mod i 2) 1)
                  (oddp i)))
  :hints (("Goal" :in-theory (enable oddp evenp))))

(defthm evenp-collapse
  (equal (integerp (* 1/2 x))
         (evenp x))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm evenp-collect-1
  (equal (integerp (+ (* 1/2 x) (* 1/2 y)))
         (evenp (+ x y)))
  :hints (("Goal" :in-theory (e/d (evenp) (evenp-collapse)))))

(defthm odd-equal-expt-cheap
  (implies (and (not (evenp x))
                (integerp x)
                (integerp n)
                )
           (equal (equal x (expt 2 n))
                  (and (equal x 1)
                       (equal n 0))))
  :rule-classes ((:rewrite :backchain-limit-lst (0 nil nil)))
  )

;This file contains stuff proven using rtl's arithmetic.
(local (in-theory (disable expt)))

(defthm integer-range-p-extend-upper
  (implies (and (ACL2::INTEGER-RANGE-P lower upper x)
                (<= upper upper+))
           (ACL2::INTEGER-RANGE-P lower upper+ x))
  :hints (("Goal" :in-theory (enable ACL2::INTEGER-RANGE-P))))

(defthm integer-range-p-extend-lower
  (implies (and (ACL2::INTEGER-RANGE-P lower upper x)
                (<= lower- lower))
           (ACL2::INTEGER-RANGE-P lower- upper x))
  :hints (("Goal" :in-theory (enable ACL2::INTEGER-RANGE-P))))

(local (in-theory (enable expt-split)))

;necessary for the stuff below
(defund fl (x)
  (declare (xargs :guard (real/rationalp x)))
  (floor x 1))

(defun expo-measure (x)
;  (declare (xargs :guard (and (real/rationalp x) (not (equal x 0)))))
  (cond ((not (rationalp x)) 0)
        ((< x 0) '(2 . 0))
        ((< x 1) (cons 1 (fl (/ x))))
        (t (fl x))))

(defund expo (x)
  (declare (xargs :guard t
                  :measure (expo-measure x)))
  (cond ((or (not (rationalp x)) (equal x 0)) 0)
        ((< x 0) (expo (- x)))
        ((< x 1) (1- (expo (* 2 x))))
        ((< x 2) 0)
        (t (1+ (expo (/ x 2))))))

(defund power2p-measure (x)
  (declare (xargs :guard (and (rationalp x) (not (equal x 0)))))
  (cond ((or (not (rationalp x))
             (<= x 0)) 0)
        ((< x 1) (cons 1 (fl (/ x))))
        (t (fl x))))

;disabled
(defund power2p (x)
  (declare (xargs :guard t :measure (power2p-measure x)
                  :hints (("goal" :in-theory (enable power2p-measure)))))
  (cond ((or (not (rationalp x)) (<= x 0)) nil)
        ((< x 1) (power2p (* 2 x)))
        ((<= 2 x) (power2p (* 1/2 x)))
        ((equal x 1) t)
        (t nil)))

;feed back to AMD?
(defthm expt-expo-when-power2p
  (implies (power2p x)
           (equal (expt 2 (expo x))
                  x))
  :hints (("Goal" :in-theory (e/d (expo power2p) (EXPO-MINUS-ERIC
                                                  EXPO-MINUS
                                                  expo-double
                                                  expo-half)))))

;consider and -alt form with LHS (unsigned-byte-p (+ m n) (* x (expt 2 m)))
(defthm unsigned-byte-p-shift-by-power-of-2
  (implies (and (unsigned-byte-p n x)
                (acl2::natp n)
                (<= 0 m) ;drop?
                (integerp m)
                )
           (unsigned-byte-p (+ m n) (* (expt 2 m) x)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;generalize this?
(defthm unsigned-byte-p-shift-by-constant-power-of-2
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (integerp k)
                (unsigned-byte-p (- n (expo k)) x)
                )
           (equal (unsigned-byte-p n (* k x))
                  (natp n)))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-shift-by-power-of-2)
           :use (:instance unsigned-byte-p-shift-by-power-of-2
                           (m (expo k))
                           (n (- n (expo k)))))))

;bzo somehow, the arithmetic is stronger here than when we have the aamp model loaded?  why?
;bzo books/arithmetic is being used here.  consider using books/arithmetic-3 instead
;(local (include-book "arithmetic-3/bind-free/top" :dir :system))

(defthm expo-expt2
  (equal (expo (expt 2 i))
         (if (integerp i)
             i
             0)))

;these are gross hacks that eric found rtl could prove but super-ihs couldn't.
;these should be cleaned up, or we should make a better floor-mod book.

(defthmd eric1
  (IMPLIES (AND (NOT (EQUAL B (FLOOR X (EXPT 2 SIZE))))
                (<= (FLOOR X (EXPT 2 SIZE)) B)
                (INTEGERP SIZE)
                (INTEGERP B)
                (INTEGERP X)
                )
           (<= X (* B (EXPT 2 SIZE)))))

;rtl can prove this
(defthmd eric2
  (IMPLIES (AND (NOT (EQUAL B (FLOOR X (EXPT 2 SIZE))))
                (< B (FLOOR X (EXPT 2 SIZE)))
                (INTEGERP SIZE)
      ;              (<= 0 SIZE)
                (INTEGERP B)
      ;               (<= 0 B)
                (INTEGERP X)
      ;                (<= 0 X)
                )
           (< (* B (EXPT 2 SIZE)) X)))

;rtl can prove this
(defthm rtl1
  (IMPLIES (AND (< I (* 2 Y))
                (NOT (INTEGERP (* 1/2 (FLOOR I Y))))
;(INTEGERP I)
                (<= 0 I)
                (rationalp y)
                )
           (EQUAL (FLOOR I Y)
                  1)))


(defthm eric3
  (IMPLIES (AND (< B (FLOOR X (EXPT 2 SIZE)))
                (INTEGERP SIZE)
;                (<= 0 SIZE)
                (INTEGERP A)
;               (<= 0 A)
                (INTEGERP B)
;              (<= 0 B)
                (INTEGERP X)
;             (<= 0 X)
                )
           (< (+ (* B (EXPT 2 SIZE))
                 (* (EXPT 2 SIZE)
                    (MOD (* A (/ (EXPT 2 SIZE))) 1)))
              X)))

(defthm eric4
  (IMPLIES (AND (<= (FLOOR X (EXPT 2 SIZE)) B)
                (NOT (EQUAL B (FLOOR X (EXPT 2 SIZE))))
                (INTEGERP SIZE)
;                (<= 0 SIZE)
                (INTEGERP A)
;               (<= 0 A)
                (INTEGERP B)
;              (<= 0 B)
                (INTEGERP X)
;             (<= 0 X)
                )
           (<= X
               (+ (* B (EXPT 2 SIZE))
                  (* (EXPT 2 SIZE)
                     (MOD (* A (/ (EXPT 2 SIZE))) 1))))))

(defthm eric700
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (< I 32768)
                )
           (equal (INTEGERP (* 1/32768 I))
                  (equal i 0))))

(defthm eric9
  (IMPLIES (AND (INTEGERP X)
                (<= 0 X)
                (< X 65536)
                (NOT (ODDP (FLOOR X 32768))))
           (< X 32768))
  :hints (("Goal" :in-theory (enable oddp evenp))))

;bzo does RTL's ability to prove this reveal some rules we should add to super-ihs?
;should this be disabled?
(defthm floor-determined-1
  (implies (and (< i (* 2 j))
                (<= j i)
                (rationalp j)
                (rationalp i)
                )
           (equal (floor i j)
                  1)))

;rename?
;see lemma rtl1?
(defthm floor-simple-cases
  (implies (and (< i (* 2 j))
                (<= 0 i)
                (rationalp j)
                (rationalp i)
                )
           (equal (floor i j) ;floor-by-twice-hack took a term out of the normal form -huh?
                  (if (< i j)
                      0
                    1))))

;Should more of less of this "C stuff" be in this library?

;;
;; C_CONDITIONAL
;;

(defund c_conditional (a b c)
  (declare (type (signed-byte 32) a)
           (type (signed-byte 32) b)
           (type (signed-byte 32) c))
  (if (= a 0)
      c
    b))

;; We want to open c_conditional when the test value is a constant, since in
;; that case we can always resolve the test.
;;
(defthm c_conditional-constant-opener
  (implies (syntaxp (quotep a))
           (equal (c_conditional a b c)
                  (if (equal a 0) c b)))
  :hints (("Goal" :in-theory (enable c_conditional))))

(defthm +_c_conditional_c_conditional_constants-2
  (implies (and (syntaxp (quotep b1))
                (syntaxp (quotep c1))
                (syntaxp (quotep b2))
                (syntaxp (quotep c2)))
           (equal (+ (c_conditional a1 b1 c1)
                     (c_conditional a2 b2 c2)
                     z)
                  (+ (if (equal a1 0) c1 b1)
                     (if (equal a2 0) c2 b2)
                     z)))
  :hints (("Goal" :in-theory (enable c_conditional))))

;try just enabling c_conditional throughout?
(defthm sbp-c_conditional
  (implies (and (signed-byte-p n a)
                (signed-byte-p n b))
           (signed-byte-p n (c_conditional c a b)))
  :hints (("goal" :in-theory (enable c_conditional))))

;try just enabling c_conditional throughout?
(defthm usbp-c_conditional
  (implies (and (unsigned-byte-p n a)
                (unsigned-byte-p n b))
           (unsigned-byte-p n (c_conditional c a b)))
  :hints (("goal" :in-theory (enable c_conditional))))

(defthm loghead-c_conditional
  (equal (loghead n (c_conditional a b c))
         (c_conditional a (loghead n b) (loghead n c)))
  :hints (("Goal" :in-theory (enable c_conditional))))

(defthmd c_conditional-to-logext-16
  (implies (unsigned-byte-p 16 y)
           (equal (c_conditional (logand 32768 y) (logior -65536 y) y)
                  (logext 16 y)))
  :hints (("goal" :in-theory (enable c_conditional))))

;;
;; C_BIT
;;

;do we ever use c_bit

;; This function is defined elsewhere.  By adding it here, we
;; make this book independent of that code.
(defund c_bit (x) (if x 1 0))

(defthm logand-c_bit
  (and (equal (logand (c_bit x) y) (b-and (c_bit x) (logcar y)))
       (equal (logand y (c_bit x)) (b-and (c_bit x) (logcar y)))
       (equal (logand (c_bit b1) (c_bit b2)) (c_bit (and b1 b2))))
  :hints (("Goal" :in-theory (enable c_bit))))


;;
;; ADD32
;;

(defund add32 (a b)
  (declare
    (xargs :guard
         (and (signed-byte-p 32 a)
              (signed-byte-p 32 b))))
  (logext 32 (+ a b)))

(defthm signed-byte-p-of-add32
  (signed-byte-p 32 (add32 a b))
  :hints (("Goal" :in-theory (enable add32))))

;;
;; ADDU32
;;

;is this ever used?
;I'm somewhat surprised that this doesn't chop its result down to 32 bits or something. -ews
(defun addu32 (a b)
  (declare (xargs :guard (and (unsigned-byte-p 32 a)
                              (unsigned-byte-p 32 b))))
  (+ a b))

;;
;; ADDU16
;;

;I'm somewhat surprised that this doesn't chop its result down to 16 bits or something. -ews
(defun addu16 (a b)
  (declare (xargs :guard (and (unsigned-byte-p 16 a)
                              (unsigned-byte-p 16 b))))
  (+ a b))

;could make a fw-chaining rule about unsigned-byte-p of this?
(defthm integerp-of-addu16
  (implies (and (integerp a)
                (integerp b))
           (integerp (acl2::addu16 a b)))
  :hints (("Goal" :in-theory (enable acl2::addu16))))


;; ;; Due to GCL compiler limitations, logxor does not seem to get
;; ;; optimized for integers.  Thus we define xor32 and do compiler
;; ;; replacments on it.
;; ;does this ever get used?
;; (defun xor32 (a b)
;;   (declare
;;     (xargs :guard
;;          (and (signed-byte-p 32 a)
;;               (signed-byte-p 32 b))))
;;   (logxor a b))

(defund carry (n x y)
  (logtail n (+ (loghead n x) (loghead n y))))

(defthm carry-type
  (implies
   (and
    (integerp x)
    (integerp y)
    (natp n))
   (unsigned-byte-p 1 (carry n x y)))
  :hints (("Goal" :in-theory (enable carry carry3 sumn sum)
           :use (:instance carry3-type
                           (c 0)))))

(defthm logtail-+-carry
  (implies
   (and
    (integerp x)
    (integerp y)
    (natp m))
   (equal (logtail m (+ x y))
          (+ (logtail m x) (logtail m y)
             (carry m x y))))
  :hints (("Goal" :in-theory (enable sum sumn carry carry3)
           :use (:instance logtail-sum-carry
                           (c 0)))))

(defthm carry-0
  (implies
   (natp n)
   (and
    (equal (carry n 0 y) 0)
    (equal (carry n x 0) 0)))
  :hints (("Goal" :in-theory (e/d (carry)
                                  (logtail-+-carry)))))

(local (in-theory (enable FALSIFY-UNSIGNED-BYTE-P)))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; signed-byte-p, unsigned-byte-p
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


(defthm unsigned-byte-p-+-helper
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (unsigned-byte-p 1 c)
                (integerp n)
                (< 0 n)
                )
           (equal (unsigned-byte-p n (+ x y c))
                  (not (logbitp n (+ x y c)))))
  :rule-classes nil
  :hints (("goal" :in-theory (enable ash LRDT open-logcons))))

;; included in overflow-bits theory
(defthm unsigned-byte-p-+
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
                (integerp n)
                (< 0 n)
                )
           (equal (unsigned-byte-p n (+ x y))
                  (not (logbitp n (+ x y)))))
  :hints (("goal" :use (:instance unsigned-byte-p-+-helper (c 0)))))

;; included in overflow-bits theory
(defthm unsigned-byte-p-+-bridge2
  (implies (and (integerp x)
                (integerp z)
                (integerp n)
                (< 0 n)
                (unsigned-byte-p n x)
                (unsigned-byte-p n y))
           (equal (unsigned-byte-p n (+ 1 x y))
                  (not (logbitp n (+ 1 x y)))))
  :hints (("goal" :use (:instance unsigned-byte-p-+-helper (c 1)))))

(defthm signed-byte-p-+
  (implies (and (signed-byte-p (1- n) x)
                (signed-byte-p (1- n) y)
                (integerp n)
                (< 0 n)
                )
           (signed-byte-p n (+ x y)))
  :hints (("goal" :in-theory (enable signed-byte-p EXPONENTS-ADD-UNRESTRICTED))))

(defthm signed-byte-p-unsigned-byte-p
  (implies (and (unsigned-byte-p free x) ;free is a free variable
                (< free n)
                )
           (equal (signed-byte-p n x)
                  (integerp n)))
  :hints (("goal"
           :in-theory (enable signed-byte-p unsigned-byte-p)
           :use ((:instance EXPT-IS-INCREASING-FOR-BASE>1
                            (r 2)
                            (i free)
                            (j (1- n)))))))

(defthm unsigned-byte-p-subtype
  (implies (and (unsigned-byte-p free x) ;free is a free variable
                (<= free n)
                )
           (equal (unsigned-byte-p n x)
                  (integerp n)
                  ))
  :hints (("goal"
           :in-theory (enable signed-byte-p unsigned-byte-p)
           :use ((:instance EXPT-IS-INCREASING-FOR-BASE>1
                            (r 2)
                            (i free)
                            (j n))))))


;make a version that matches on constants?
(defthm sbp-bound
  (implies (signed-byte-p (1+ n) x)
           (and (<= (- (expt 2 n)) x)
                (<= x (+ -1 (expt 2 n)))))
  :hints (("goal" :in-theory (enable signed-byte-p))))

;disable?
(defthm sbp-bound-1
  (implies (and (signed-byte-p n x)
                (<= (expt 2 (1- n)) m))
           (and (<= (- m) x)
                (<= x (+ -1 m))))
  :hints (("goal" :in-theory (enable signed-byte-p))))

(defthm unsigned-byte-p-logcdr-bridge5
  (implies (and (unsigned-byte-p (1+ n) (1+ x))
                (equal (logcar x) 1)
                (integerp x)
                (integerp n)
                (<= 0 x)
                (<= 0 n)
                )
           (unsigned-byte-p n (1+ (logcdr x))))
  :hints (("goal"
           :use ((:instance unsigned-byte-p-of-logcdr (x (1+ x))))))
  )

(defthm signed-byte-p--1
 (implies (and (signed-byte-p (1- n) x)
               (integerp n)
               (integerp x)
               (< 0 n))
          (signed-byte-p n (- x)))
 :hints (("goal" :in-theory (enable signed-byte-p EXPONENTS-ADD-UNRESTRICTED)))
 :rule-classes ((:forward-chaining :trigger-terms ((- x)))))

(defthm signed-byte-p--2
 (implies (and (signed-byte-p n x)
               (integerp n)
               (integerp x)
               (<= 0 n)
               (not (equal x (- (expt 2 (1- n))))))
          (signed-byte-p n (- x)))
 :hints (("goal" :in-theory (enable signed-byte-p expt))))

(defthm unsigned-byte-p-ash-neg
  (implies (and (<= m 0)
                (integerp n)
                (integerp m)
                (integerp x)
                (<= 0 n)
                )
           (equal (unsigned-byte-p n (ash x m))
                  (unsigned-byte-p (- n m) x)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm unsigned-byte-p-ash-pos
  (implies (and (<= 0 m)
                (integerp n)
                (integerp m)
                (<= 0 n)
                (integerp x))
           (equal (unsigned-byte-p n (ash x m))
                  (unsigned-byte-p (max 0 (- n m)) x)))
  :hints (("goal"
           :in-theory (e/d (LRDT
                            unsigned-byte-p*)
                           (ash* ;fixes a loop that manifested itself in the move to 3.0
                            open-logcons)))))


(defthm arith-cancel
  (implies (and (rationalp x)
                (rationalp y)
                (< 0 y)
                )
           (equal (< (* 2 X y) y)
                  (< (* 2 X) 1)))
  :hints (("Goal" :nonlinearp t)))


;gen
;make alt
(defthm signed-byte-p-of-shift
  (implies (and (integerp x)
                (integerp m)
                (integerp n)
                (< 0 n)
                (<= 0 m)
                (<= 0 x)
                (<= m n)
                )
           (equal (SIGNED-BYTE-P N (* X (EXPT 2 M)))
                  (if (equal 0 x)
                      t
                    (SIGNED-BYTE-P (- N m) X))))

  :otf-flg t
  :hints (("Goal" ; :induct (logcdr-induction x)
;:nonlinearp t
           :cases ((< x 0))
           :in-theory (enable ;lrdt
                       SIGNED-BYTE-P
                       EXPONENTS-ADD-UNRESTRICTED
                       ))))

;; (defthm signed-byte-p-of-shift2
;;   (implies (and (integerp x)
;;                 (integerp m)
;;                 (integerp n)
;;                 (< 0 n)
;;                 (<= 0 m)
;; ;'                (<= 0 x)
;;                 (<= m n)
;;                 )
;;            (equal (SIGNED-BYTE-P N (* X (EXPT 2 M)))
;;                   (if (equal 0 x)
;;                       t
;;                     (SIGNED-BYTE-P (- N m) X))))
;;   :hints (("Goal" :in-theory (disable signed-byte-p-of-shift)
;;            :use ((:instance signed-byte-p-of-shift)
;;                  (:instance signed-byte-p-of-shift (x (- x)))))))


;;   :otf-flg t
;;   :hints (("Goal" ; :induct (logcdr-induction x)
;; ;:nonlinearp t
;;            :cases ((< x 0))
;;            :in-theory (enable ;lrdt
;;                        SIGNED-BYTE-P
;;                        EXPONENTS-ADD-UNRESTRICTED
;;                        ))))



(defthm unsigned-byte-p-1+
  (implies (and (syntaxp (not (quotep x))) ;keeps this from firing on, e.g., (unsigned-byte-p n 500)
                (unsigned-byte-p n x)
                (integerp n)
                (<= 0 n)
                )
           (equal (unsigned-byte-p n (+ 1 x))
                  (not (equal x (1- (expt 2 n)))))) ; should this be (loghead n -1) ?
  :hints (("goal" :in-theory (enable LRDT unsigned-byte-p))))

;see unsigned-byte-p-+-helper
(defthm unsigned-byte-p-+-bridge-helper
  (implies (and (integerp n)
                (< 0 n)
                (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y)
                (unsigned-byte-p 1 c))
           (unsigned-byte-p n (+ c x y)))
  :rule-classes nil
  :hints (("goal" :in-theory (e/d (unsigned-byte-p EXPONENTS-ADD-UNRESTRICTED)
                                  (unsigned-byte-p-+)))))

(defthm unsigned-byte-p-+-bridge
  (implies (unsigned-byte-p (1- n) x)
           (equal (unsigned-byte-p n (+ 1 x (loghead (1- n) y)))
                  (integerp n)
                  ))
  :hints (("goal" :use ((:instance unsigned-byte-p-+-bridge-helper (y (loghead (1- n) y)) (c 1)))
           :in-theory (e/d (FALSIFY-UNSIGNED-BYTE-P) ( UNSIGNED-BYTE-P-1+)))))

;more general than unsigned-byte-p-+-bridge
(defthm unsigned-byte-p-+-bridge-eric
  (implies (and (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y))
           (equal (unsigned-byte-p n (+ 1 x y))
                  (integerp n)
                  ))
  :hints (("goal" :use ((:instance unsigned-byte-p-+-bridge-helper (y y) (c 1)))
           :in-theory (e/d (FALSIFY-UNSIGNED-BYTE-P) ( UNSIGNED-BYTE-P-1+)))))

(defthm signed-byte-p-+----simple
  (implies (and (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y)
                (integerp n)
                (< 0 n)
                )
           (signed-byte-p n (+ x (- y))))
  :hints (("goal" :in-theory (enable unsigned-byte-p signed-byte-p))))

(local (in-theory (disable <-+-NEGATIVE-0-1))) ;why?

(defthm unsigned-byte-p-+-expt---simple
  (implies (and (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y)
                (integerp n)
                (< 0 n)
                )
           (unsigned-byte-p n (+ x (- y) (expt 2 (1- n)))))
  :hints (("goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED
                                     unsigned-byte-p signed-byte-p))))

(defthm unsigned-byte-p-+-expt---simple-rewrite
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 (1- n)))
                ;(integerp k)
                (integerp n)
                (equal n (integer-length k))
                (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y))
           (unsigned-byte-p n (+ k x (- y))))
  :hints (("goal" :use (:instance unsigned-byte-p-+-expt---simple))))

(defthm unsigned-byte-p-logbit
  (equal (unsigned-byte-p n (logbit m x))
         (and (integerp n)
              (<= 0 n)
              (or (not (equal n 0))
                  (not (logbitp m x)))))
  :hints (("goal" :in-theory (enable logbit unsigned-byte-p))))

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

;Which do we prefer to have inside?
;Or should we introduce a new bit slicing function?
;generalize!
;; (defthm logtail-logext-hack-2
;;   (implies (integerp x)
;;            (equal (logtail 15 (logext 32 x))
;;                   (logext 17 (logtail 15 x))))
;;   :hints
;;   (("Goal" :in-theory (enable logext ifix))))

;gen this?
;; (defthm logtail-logext-hack
;;   (equal (logtail 16 (logext 32 x))
;;          (logext 16 (logtail 16 x)))
;;   :hints (("Goal" :in-theory (enable ;logtail
;;                                      logext ifix))))

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

(in-theory (disable
            B-NOT
            B-AND
            B-IOR
            B-XOR
            B-EQV
            B-NAND
            B-NOR
            B-ANDC1
            B-ANDC2
            B-ORC1
            B-ORC2))

(defthm associativity-of-b-and
  (equal (b-and (b-and a b) c)
         (b-and a (b-and b c)))
  :hints (("Goal" :in-theory (enable b-and))))

(defthm associativity-of-b-ior
  (equal (b-ior (b-ior a b) c)
         (b-ior a (b-ior b c)))
  :hints (("Goal" :in-theory (enable b-ior))))

(local (in-theory (enable b-xor b-eqv b-nand b-nor
                          b-andc1 b-andc2 b-orc1 b-orc2 b-not)))


(defthm simplify-bit-functions-2
  (and (equal (b-and a (b-and (b-not a) b)) 0)
       (equal (b-ior a (b-ior (b-not a) b)) 1)
       (equal (b-and a (b-and a b)) (b-and a b))
       (equal (b-ior a (b-ior a b)) (b-ior a b)))
  :hints (("goal" :in-theory (enable b-and b-ior b-not))))
;           :in-theory (disable associativity-of-bit-functions)

(defthm b-and-b-ior
  (and (equal (b-and i (b-ior j k))
              (b-ior (b-and i j) (b-and i k)))
       (equal (b-and (b-ior i j) k)
              (b-ior (b-and i k) (b-and j k))))
  :hints (("goal" :in-theory (enable b-and b-ior))))

(defthm b-xor-b-not
  (and (equal (b-xor a (b-not b)) (b-not (b-xor a b)))
       (equal (b-xor (b-not a) b) (b-not (b-xor a b))))
  :hints (("goal" :in-theory (enable b-not b-xor))))

(defthm b-xor-constant
  (implies (and (equal y 0)
                (syntaxp (quotep y))
                (not (equal x y))
                (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 z))
           (equal (b-xor x z) (b-not z)))
  :hints (("goal" :in-theory (enable unsigned-byte-p b-xor b-not))))

;drop?
(defthmd b-not-open-0
  (implies (and (equal x 0)
                (unsigned-byte-p 1 x))
           (equal (b-not x)
                  1))
  :hints (("goal" :in-theory (enable b-not unsigned-byte-p))))

(defthm b-not-open-1
  (implies (and (not (equal x 0))
                (unsigned-byte-p 1 x))
           (equal (b-not x)
                  0))
  :hints (("goal" :in-theory (enable b-not unsigned-byte-p))))

(defthm bfix-b-functions
  (and (equal (bfix (b-not x))   (b-not x))
       (equal (bfix (b-and x y)) (b-and x y))
       (equal (bfix (b-ior x y)) (b-ior x y))
       (equal (bfix (b-xor x y)) (b-xor x y)))
  :hints (("goal" :in-theory (enable b-ior b-and b-xor b-not))))

(defthm commutativity2-of-b-functions
  (and (equal (b-ior a (b-ior b c))
              (b-ior b (b-ior a c)))
       (equal (b-xor a (b-xor b c))
              (b-xor b (b-xor a c)))
       (equal (b-and a (b-and b c))
              (b-and b (b-and a c))))
  :hints (("goal" :in-theory (enable b-ior b-and b-xor b-not))))

(defthm equal-k-b-and
  (and (equal (equal 0 (b-and x y))
              (or (zbp x) (zbp y)))
       (equal (equal 1 (b-and x y))
              (and (not (zbp x)) (not (zbp y)))))
  :hints (("goal" :in-theory (enable b-and))))

(defthm equal-k-b-ior
  (and (equal (equal 0 (b-ior x y))
              (and (zbp x) (zbp y)))
       (equal (equal 1 (b-ior x y))
              (not (and (zbp x) (zbp y)))))
  :hints (("goal" :in-theory (enable b-ior))))

;why not just define them this way and leave them enabled?
(defthm b-xor-rewrite
  (equal (b-xor a b)
         (b-ior (b-and a (b-not b))
                (b-and (b-not a) b))))

(defthm b-eqv-rewrite
  (equal (b-eqv a b)
         (b-ior (b-and a b)
                (b-and (b-not a) (b-not b)))))

(defthm b-nor-rewrite
  (equal (b-nor a b)
         (b-not (b-ior a b))))

(defthm b-nand-rewrite
  (equal (b-nand a b)
         (b-not (b-and a b))))

(defthm b-andc1-rewrite
  (equal (b-andc1 a b)
         (b-and (b-not a) b)))

(defthm b-andc2-rewrite
  (equal (b-andc2 a b)
         (b-and a (b-not b))))

(defthm b-orc1-rewrite
  (equal (b-orc1 a b)
         (b-ior (b-not a) b)))

(defthm b-orc2-rewrite
  (equal (b-orc2 a b)
         (b-ior a (b-not b))))


;bzo more like this?
;separate rw from fc rules?
;generalize the size in the rw version?
(defthm unsigned-byte-p-b-xor
  (unsigned-byte-p 1 (b-xor x y))
  :hints (("goal" :in-theory (enable b-xor)))
  :rule-classes ((:forward-chaining :trigger-terms ((b-xor x y)))
                 (:rewrite)))

(defthm unsigned-byte-p-b-and
  (unsigned-byte-p 1 (b-and x y))
  :hints (("goal" :in-theory (enable b-and)))
  :rule-classes ((:forward-chaining :trigger-terms ((b-and x y)))
                 (:rewrite)))

(defthm unsigned-byte-p-b-ior
  (unsigned-byte-p 1 (b-ior x y))
  :hints (("goal" :in-theory (enable b-ior)))
  :rule-classes ((:forward-chaining :trigger-terms ((b-ior x y)))
                 (:rewrite)))

(defthm unsigned-byte-p-b-functions
  (and (equal (unsigned-byte-p n (b-and x y))
              (and (integerp n)
                   (<= 0 n)
                   (or (< 0 n)
                       (equal (b-and x y) 0) ;improve
                       )))
       (equal (unsigned-byte-p n (b-ior x y))
              (and (integerp n)
                   (<= 0 n)
                   (or (< 0 n)
                       (equal (b-ior x y) 0) ;improve
                       ))))
  :hints (("goal" :in-theory (enable b-ior b-and unsigned-byte-p))))

(defthmd b-xor-equal-0-rewrite
  (equal (equal (b-xor x y) 0)
         (equal (zbp x) (zbp y)))
  :hints (("goal" :in-theory (enable b-xor b-not))))

(defthmd b-xor-equal-1-rewrite
  (equal (equal (b-xor x y) 1)
         (not (equal (zbp x) (zbp y))))
  :hints (("goal" :in-theory (enable b-xor b-not))))

(defthm b-ior-upper-bound
  (<= (b-ior x y) 1)
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable b-ior))))

(defthm unsigned-byte-p-b-not
  (implies (and (integerp size)
                (< 0 size))
           (unsigned-byte-p size (b-not x)))
  :hints (("Goal" :in-theory (enable b-not))))

(defthm logext-16-of-b-not
  (implies (and (integerp n)
                (< 1 n))
           (equal (logext n (b-not bit))
                  (b-not bit)))
  :hints (("Goal" :in-theory (enable b-not))))

(defthm loghead-of-b-not
  (implies (and (integerp n)
                (< 0 n))
           (equal (loghead n (b-not bit))
                  (b-not bit)))
  :hints (("Goal" :in-theory (enable b-not))))

(defthm logtail-of-b-not
  (implies (and (integerp n)
                (< 0 n))
           (equal (logtail n (b-not bit))
                  0))
  :hints (("Goal" :in-theory (enable b-not))))

(in-theory (enable natp))

;since UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP is built into acl2 and we have acl2::unsigned-byte-p-forward-to-expt-bound:
(in-theory (disable ACL2::UNSIGNED-BYTE-P-FORWARD))

(local (in-theory (enable FALSIFY-UNSIGNED-BYTE-P)))

(in-theory (disable
;            (:REWRITE ZP-OPEN)
 ;           (:REWRITE ZIP-OPEN)

   ;         (:DEFINITION NTHCDR)
  ;          (:DEFINITION LAST)

 ;           (:DEFINITION THE-ERROR)
;            (:DEFINITION ZPF)
;;             (:DEFINITION LOGTEST)
;;             (:DEFINITION SUBSEQ-LIST)
;;             (:DEFINITION SUBSEQ)
;;             (:DEFINITION BUTLAST)
;;             (:REWRITE LEN-UPDATE-NTH)
;;             (:DEFINITION PAIRLIS2)
;;             (:DEFINITION DUPLICATES)
;;             (:DEFINITION ADD-TO-SET-EQUAL)
;;             (:DEFINITION INTERSECTION-EQ)
;;             (:REWRITE RIGHT-CANCELLATION-FOR-+)
;;             (:REWRITE INVERSE-OF-+-AS=0)
;;             (:REWRITE RIGHT-CANCELLATION-FOR-*)
;;             (:REWRITE EQUAL-*-X-Y-X)
;;             (:FORWARD-CHAINING NUMERATOR-NONZERO-FORWARD)
;;             (:REWRITE TIMES-ZERO)
;;             (:REWRITE /R-WHEN-ABS-NUMERATOR=1)
;;             (:TYPE-PRESCRIPTION EXPT-TYPE-PRESCRIPTION-RATIONALP)
;;             (:GENERALIZE EXPT-TYPE-PRESCRIPTION-RATIONALP)
;;             (:REWRITE LEFT-NULLITY-OF-1-FOR-EXPT)
;;             (:REWRITE EXPONENTS-ADD-FOR-NONNEG-EXPONENTS)
;;             (:REWRITE DISTRIBUTIVITY-OF-EXPT-OVER-*)
;;             (:REWRITE EXPT-1)
;;             (:REWRITE EQUAL-CONSTANT-+)
;;             (:REWRITE APPEND-PRESERVES-RATIONAL-LISTP)
;;             (:FORWARD-CHAINING RATIONALP-CAR-RATIONAL-LISTP)
;;             (:REWRITE <-*-RIGHT-CANCEL)
;;             (:REWRITE /-INVERTS-ORDER-1)
;;             (:REWRITE <-*-0)
;;             (:REWRITE |0-<-*|)
;;             (:REWRITE /-INVERTS-ORDER-2)
;;             (:REWRITE /-INVERTS-WEAK-ORDER)
;;             (:REWRITE *-PRESERVES->=-FOR-NONNEGATIVES)
;;             (:REWRITE *-PRESERVES->-FOR-NONNEGATIVES-1)
;;             (:REWRITE X*Y>1-POSITIVE-LEMMA)
;;             (:LINEAR X*Y>1-POSITIVE)
;;             (:REWRITE X*Y>1-POSITIVE)
;;             (:REWRITE <-*-X-Y-Y)
;;             (:REWRITE <-Y-*-X-Y)
;            (:REWRITE <-0-+-NEGATIVE-1)
;            (:REWRITE <-0-+-NEGATIVE-2)
;            (:REWRITE <-+-NEGATIVE-0-1)
;           (:REWRITE <-+-NEGATIVE-0-2)
;dsh  Removed for ACL2 2.9.2, where NATP-CR and POSP-CR no longer exist.
;     This change doesn't appear to affect proofs under ACL2 2.9.
;            (:COMPOUND-RECOGNIZER NATP-CR)
;            (:COMPOUND-RECOGNIZER POSP-CR)
;;             (:FORWARD-CHAINING NATP-FC-1)
;;             (:FORWARD-CHAINING NATP-FC-2)
;;             (:FORWARD-CHAINING POSP-FC-1)
;;             (:FORWARD-CHAINING POSP-FC-2)
;;             (:REWRITE |(natp a)  <=>  (posp a+1)|)
;;             (:REWRITE POSP-NATP)
;;             (:REWRITE NATP-*)
;;             (:REWRITE NATP-POSP)
;;             (:REWRITE NATP-POSP--1)
;;             (:TYPE-PRESCRIPTION |x < y  =>  0 < -x+y|)
;;             (:TYPE-PRESCRIPTION |x < y  =>  0 < y-x|)
;;             (:REWRITE DENOMINATOR-UNARY-MINUS)
;;             (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION
;;                      . 1)
;;             (:LINEAR NUMERATOR-GOES-DOWN-BY-INTEGER-DIVISION
;;                      . 2)
;;             (:REWRITE DENOMINATOR-PLUS)
;;             (:REWRITE NUMERATOR-/X)
            ))

(in-theory (enable
 ;           (:DEFINITION ZP) trying..
  ;          (:DEFINITION ZIP)
;            (:DEFINITION NATP)
 ;           (:DEFINITION POSP)
  ;          (:INDUCTION STANDARD-CHAR-LISTP)
   ;         (:INDUCTION STRING<-L)
    ;        (:EXECUTABLE-COUNTERPART ABORT!)
     ;       (:INDUCTION LEXORDER)
            ))

(defthm lognot-zip
  (implies (zip a)
           (equal (lognot a) -1))
  :hints (("goal" :in-theory (enable lognot ifix))))

;consider disabling these for the user? since they might be expensive. probably okay?
(defthm logior-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logior i j)
                  (ifix j)))
  :hints (("goal" :in-theory (enable logior ifix))))

(defthm logior-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logior i j)
                  (ifix i)))
  :hints (("goal" :in-theory (enable logior ifix))))

(defthm logior*-better
  (equal (logior i j)
         (logcons (b-ior (logcar i) (logcar j))
                  (logior (logcdr i) (logcdr j))))
  :hints (("Goal" :use (:instance logior*)))
  :rule-classes
  ((:definition :clique (binary-logior)
                :controller-alist
                ((binary-logior t t)))))

;(in-theory (disable LOGIOR*)) ;ours is better

(defthm logand-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logand i j)
                  0))
  :hints (("goal" :in-theory (enable logand))))

(defthm logand-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logand i j)
                  0))
  :hints (("goal" :in-theory (enable logand))))

(defthm logand*-better
  (equal (logand i j)
         (logcons (b-and (logcar i) (logcar j))
                  (logand (logcdr i) (logcdr j))))
  :hints (("Goal" :use (:instance logand*)))
  :rule-classes
  ((:definition :clique (binary-logand)
                :controller-alist ((binary-logand t t)))))

(defthm lognot*-better
  (equal (lognot i)
         (logcons (b-not (logcar i))
                  (lognot (logcdr i))))
  :rule-classes ((:definition :clique (lognot)
                              :controller-alist ((lognot t))))
  :hints (("Goal" :use (:instance lognot*))))

(defthm logxor-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logxor i j)
                  (ifix j)))
  :hints (("goal" :in-theory (enable logxor logeqv logorc1))))

(defthm logxor-when-j-is-not-an-integerp
  (implies (not (integerp j))
           (equal (logxor i j)
                  (ifix i)))
  :hints (("goal" :in-theory (enable logxor logeqv logorc1))))

(defthm logxor*-better
  (equal (logxor i j)
         (logcons (b-xor (logcar i) (logcar j))
                  (logxor (logcdr i) (logcdr j))))
  :rule-classes
  ((:definition :clique (binary-logxor)
                :controller-alist ((binary-logxor t t))))
  :hints (("Goal" :use (:instance logxor*))))


(defthm logbitp*-better
  (implies (and (integerp pos)
                (<= 0 pos)
                )
           (equal (logbitp pos i)
                  (cond ((equal pos 0) (equal (logcar i) 1))
                        (t (logbitp (1- pos) (logcdr i))))))
  :rule-classes
  ((:definition :clique (logbitp)
                :controller-alist ((logbitp t t))))
  :hints (("Goal" :use (:instance logbitp*))))

(in-theory (disable LRDT))

(in-theory (disable unsigned-byte-p-plus)) ;; an unneeded rule, that slows things down

;redo? trying disabled
(defthmd equal-b-not-logcar
  (and (equal (equal (b-not (logcar x)) 0)
              (equal (logcar x) 1))
       (equal (equal (b-not (logcar x)) 1)
              (equal (logcar x) 0)))
  :hints (("goal" :in-theory (enable b-not logcar))))

(in-theory (disable ash))
(local (in-theory (disable evenp-collapse))) ;bzo

(defthm ash-when-c-is-not-an-integerp
  (implies (not (integerp c))
           (equal (ash i c)
                  (ifix i)))
  :hints (("goal" :in-theory (enable ash ifix))))

(defthm ash-when-c-is-zero
  (equal (ash i 0)
         (ifix i))
  :hints (("goal" :in-theory (enable ash ifix))))

;(in-theory (disable ash-0)) ;bzo move this to a place where ash-0 is defined

(defthm ash-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (ash i c)
                  0))
  :hints (("Goal" :in-theory (enable ash))))

(defthm ash-when-i-is-zero
  (equal (ash 0 count)
         0)
  :hints (("Goal" :in-theory (enable ash))))

(defthm ifix-ash
  (equal (ifix (ash x y))
         (ash x y)))

(defthm ash-negative-rewrite
  (implies (and (<= 0 n)
                (integerp n)
                )
           (equal (< (ash x n) 0)
                  (< (ifix x) 0)))
  :hints (("Goal" :in-theory (enable ash))))

;bzo think more about the type of ash

(defthm equal-ash-pos-0
  (implies (<= 0 c)
           (equal (equal (ash i c) 0)
                  (equal (ifix i) 0)))
  :hints (("goal" :in-theory (enable ash))))


(defthm ash-bound1
  (implies (and (<= s 0)
                (<= x b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-bound1a
  (implies (and (<= s 0)
                (< x b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(local (in-theory (disable FLOOR-OF-SHIFT-RIGHT-2)))

(defthm ash-bound2
  (implies (and (<= s 0)
                (<= b x)
                (<= b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= b (ash x s)))
  :hints (("goal" :in-theory (enable ash expt))))




(defthm ash-bound2a
  (implies (and (<= s 0)
                (< b x)
                (< b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< b (ash x s)))
  :hints (("goal" :in-theory (e/d (ash expt)
                                  (FLOOR-OF-SHIFT-RIGHT-2)))))

(defthm ash-bound3
  (implies (and (<= (* x (expt 2 s)) b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-bound3a
  (implies (and (< (* x (expt 2 s)) b)
                (<= 0 b)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< (ash x s) b))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-bound4
  (implies (and (<= b (* x (expt 2 s)))
                (<= b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (<= b (ash x s)))
  :hints (("goal" :in-theory (enable  ash expt))))

(defthm ash-bound4a
  (implies (and (<= 0 s)
                (< b (* x (expt 2 s)))
                (< b 0)
                (integerp s)
                (integerp b)
                (integerp x)
                )
           (< b (ash x s)))
  :hints (("goal" :in-theory (enable  ash expt))))




;can't quite combine with ASH-ASH-RIGHT-TO-ASH because of the case where m<0
(defthm *ark*-ash-ash-left
  (implies (and (<= 0 m)
                (<= 0 n)
                (integerp n)
                (integerp m)
                (integerp x)
                )
           (equal (ASH (ASH x m) n)
                  (ash x (+ m n))))
  :hints (("goal" :in-theory (enable ash ; LOGOPS-RECURSIVE-DEFINITIONS-THEORY
                                     expt
                                     ))))

;generalize?
(defthm ash-expt-neg
  (implies (and (integerp n)
                (< 0 n))
           (equal (ash (expt 2 n) (- n))
                  1))
  :hints (("goal" :in-theory (enable ;LRDT
                              ash
                              ))))

(defthm ash--1-neg
  (implies (and (<= n 0)
                (integerp n)
                )
           (equal (ash -1 n)
                  -1))
  :hints (("goal" :in-theory (enable ash ;LRDT
                                     ))))

(defthm ash-non-decreasing
  (implies (and (integerp k)
                (<= 0 k)
                (integerp n)
                (<= 0 n))
           (<= k (ASH k n)))
  :hints (("goal" :in-theory (enable ash expt))))

(defthm ash-1-when-c-is-negative
  (implies (< c 0)
           (equal (ASH 1 c)
                  (if (integerp c)
                      0
                    1)))
  :hints (("Goal" :in-theory (enable ash expt))))

(defthmd ash-1-expt-rewrite
  (equal (ash 1 c)
         (if (<= 0 c)
             (expt 2 c)
           (if (integerp c)
               0
             1)))
  :hints (("Goal" :in-theory (enable ash expt))))

;improve?
(defthmd ash-1-lessp
  (implies (and (integerp k)
                (<= 0 k))
           (< 0 (ASH 1 k)))
  :hints (("Goal" :in-theory (enable ash acl2::commutativity-of-* expt))))

;bzo drop hyps and generalize
(defthm ash-of-1-equal-65536
  (implies (and (integerp c)
                (<= 0 c))
           (equal (equal (ash 1 c) 65536)
                  (equal c 16)))
  :hints (("Goal" :cases ((< c 16) (> c 16))
           :in-theory (enable ash))))

(defthm ash-to-0
  (implies (unsigned-byte-p n x)
           (equal (ash x (- n))
                  0))
  :hints (("Goal" :in-theory (enable ash))))


;; (defthm ash-ash-right-to-ash
;;   (implies (and (<= n 0)
;;                 (integerp n)
;;                 (integerp m)
;;                 (integerp x)
;;                 )
;;            (equal (ash (ash x m) n)
;;                   (ash x (+ m n))))
;;   :hints (("goal"
;;            :in-theory (e/d (;LRDT expt2* ;ash-as-logtail ash-as-logapp open-logcons
;;                             expt
;;                             ash
;;                                  ) (EXPT-2-CRUNCHER)))))



;bzo make a version without the free variable
;; (DEFTHM ASH-GOES-TO-0
;;   (IMPLIES (AND (UNSIGNED-BYTE-P SIZE I)
;;                 (INTEGERP COUNT)
;;                 (<= COUNT 0)
;;                 (<= SIZE (- COUNT)))
;;            (EQUAL (ASH I COUNT) 0))
;; )

(defthm ash-not-equal
  (implies (and (integerp i)
                (integerp j)
                (not (equal i j)))
           (not (equal (ash i 1) (ash j 1))))
  :hints (("Goal" :in-theory (enable ash))))

;generalize
(defthm ash-evenp
  (evenp (ash i 1))
  :hints (("Goal" :in-theory (enable ash))))

(defthm ash-not-equal
  (implies (and (integerp i)
                (integerp j)
                (not (equal i j)))
           (not (equal (ash i 1) (ash j 1))))
  :hints (("Goal" :in-theory (enable ash))))

;bzo gen
(defthm ash-1-monotonic
  (implies (and (integerp i)
                (integerp j))
           (equal (< (ash i 1) (ash j 1))
                  (< i j)))
  :hints (("Goal" :in-theory (enable ash))))


;can we get rid of this?
;or generalize?  ash isn't equal to something odd?
;foward chain to evenp/oddp facts?
(defthm ash-plus1-not-equal
  (implies (and (integerp i)
                (integerp j)
                (not (equal i j)))
           (not (equal (ash i 1) (+ 1 (ash j 1)))))
  :hints (("Goal" :in-theory (enable ACL2::EVEN-ODD-DIFFERENT-1
                                     ACL2::EVEN-ODD-DIFFERENT-2))))

(defthm ash-plus-addr2
  ;; notice this is rule-classes nil because it loops with
  ;; several lemmas in the ash theory.
  (implies (and (integerp addr)
                (integerp k))
           (equal (+ (* 2 k) (ash addr 1))
                  (ash (+ k addr) 1)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable ash acl2::commutativity-of-*))))



;generalize the 1
(defthm ash-equal-constant
  (implies (and (syntaxp (quotep k))
                (acl2-numberp k)
                (integerp x) ;drop?
                )
           (equal (EQUAL (ASH x 1) k)
                  (EQUAL x (/ k 2))))
  :hints (("Goal" :in-theory (enable ash))))

(defthmd ash-+-pos
  (implies (and (integerp x)
                (integerp y)
                (integerp m)
                (<= 0 m))
           (equal (ash (+ x y) m)
                  (+ (ash x m) (ash y m))))
  :hints (("goal" :in-theory (enable ash))))

;handle  (< 0 (ash v n))?

;move
(defthm <=-0-ash
  (implies (and (integerp v)
                (integerp n)
                )
           (equal (< (ash v n) 0)
                  (< v 0)))
  :hints (("goal" :in-theory (enable ASH-BOUND3A
                                     ASH-BOUND4
                                     ))))

(defthm half-ash-by-two
  (equal (* 1/2 (ash x 1))
         (ifix x))
  :hints (("Goal" :in-theory (enable ash))))

(defthm evenp-of-ash
  (equal (evenp (ash 1 n))
         (and (integerp n)
              (not (equal 0 n))))
  :hints (("Goal" :cases ((< 0 n))
           :in-theory (e/d (oddp evenp ;bzo prove a rule for evenp
                                 ash) (acl2::evenp-collapse)))))

(defthm oddp-of-ash
  (equal (oddp (ash 1 n))
         (or (not (integerp n))
             (equal 0 n)))
  :hints (("Goal" :cases ((< 0 n))
           :in-theory (e/d (oddp) ()))))


(defthm ash-recollapse
  (implies (and (< 0 n)
                (integerp n))
           (equal (* 2 (ash x (+ -1 n)))
                  (ash x n)))
  :hints (("Goal" :in-theory (enable ash))))

;bzo decide whether to use ash or *2
(defthm ash-times-2-hack
  (implies (integerp j)
           (equal (equal (ash j 1) (* 2 j))
                  t))
  :hints (("Goal" :in-theory (enable ash))))

;this was causing lots of generalization to occur, introducing mod into goals which had nothing to do with mod.
(in-theory (disable (:generalize MOD-X-Y-=-X+Y)))

(in-theory (disable
            (:DEFINITION NONNEGATIVE-INTEGER-QUOTIENT)
            (:DEFINITION FLOOR)
            (:DEFINITION CEILING)
            (:DEFINITION TRUNCATE)
            (:DEFINITION ROUND)
            (:DEFINITION MOD)
            (:DEFINITION REM)
            (:DEFINITION EXPT)
            ))

;alternate form of the built-in rule distributivity
(defthm distributivity-alt
  (equal (* (+ y z) x)
         (+ (* x y) (* x z))))

;generalize?
(defthm expt-2-cruncher
  (implies (integerp m)
           (equal (* 2 (expt 2 (+ -1 m)))
                  (expt 2 m)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-unary-
  (equal (integerp (- a))
         (integerp (fix a)))
  :hints (("Goal" :cases ((integerp a)))))

(defthm <-+-constant-constant
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b)))
           (and (equal (< a (+ b c))
                       (< (- a b) c))
                (equal (< (+ b c) a)
                       (< c (- a b))))))

(defthm move---to-constant-in-equal
  (implies (and (syntaxp (quotep y))
                (acl2-numberp y)
                (acl2-numberp x))
           (equal (equal y (- x))
                  (equal (- y) x)))
  :hints (("goal" :in-theory (enable fix)))
  :rule-classes ((:rewrite :loop-stopper nil)))

(defthm integerp-0-1
  (implies (or (and (< 0 x) (< x 1))
               (and (< -1 x) (< x 0)))
           (not (integerp x)))
  :rule-classes nil)

(defthm integerp-/
  (implies (and (integerp n)
                (not (equal n 0)))
           (equal (integerp (/ n))
                  (or (equal n 1) (equal n -1))))
  :hints (("goal" :use ((:instance integerp-0-1 (x (/ n)))
                        (:instance integerp-0-1 (x (/ n)))))))

;rename?
;where should this go?
;compare to EXPT-TYPE-PRESCRIPTION-INTEGERP
(defthm integerp-expt-1
  (implies (and (<= 0 i) (integerp r))
           (integerp (expt r i))))

(defthm integerp-expt
  (implies (integerp n)
           (equal (integerp (expt 2 n))
                  (<= 0 n)))
  :hints (("goal" :in-theory (enable expt))))

;for some reason, this is still needed for the rule below
(defthm integerp-*-constant-means-1
  (implies (and (rationalp x)
                (integerp (* 1/2 x)))
           (integerp x)))

;; (defthm integerp-*-constant-means-2
;;   (implies (and (integerp (* 1/4 x))
;;                 (rationalp x))
;;            (integerp x))
;;   :rule-classes :forward-chaining)


(defthm integerp-*-1/2-expt
  (iff (integerp (* 1/2 (expt 2 n)))
       (not (zp n)))
  :hints (("goal" :in-theory (e/d (expt exponents-add)))))

(defthm integerp-*-1/4-expt
  (implies (and (integerp n)
                (<= 0 n))
           (equal (integerp (* 1/4 (expt 2 n)))
                  (and (not (zp n)) (not (equal n 1)))))
  :hints (("goal" :in-theory (enable expt))))

(defthm integer-length-expt
  (equal (integer-length (expt 2 n))
         (if (integerp n)
             (if (<= 0 n)
                 (1+ n)
               0)
           1))
  :hints (("goal" :in-theory (enable expt integer-length))))

(defthm <-integer-length-1
  (implies (integerp x)
           (equal (< (integer-length x) 1)
                  (or (equal x -1) (equal x 0))))
  :hints (("goal" :in-theory (enable integer-length))))

;; from guard-lemmas.lisp
(defthm expt-less-1
  (implies (and (integerp s)
                (integerp n)
                (<= s 0)
                (<= 0 n))
           (<= (expt n s) 1))
  :hints (("goal" :in-theory (enable expt))))

(defthm <-1-expt
  (equal (< 1 (expt 2 n))
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-*-1/2*x*expt-bridge
  (implies (and (integerp a)
                (integerp (* b c)))
           (integerp (* b a c))))

(defthm integerp-*-1/2*x*expt-bridge2
  (implies (and (integerp a)
                (integerp b)
                (integerp (* c d)))
           (integerp (* c a d b))))

(defthm floor-1-helper
  (implies (and (rationalp x)
                (rationalp y)
                (<= x y))
           (<= (floor x 1) y)))


(defthm expt-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (expt r i)
                  1))
  :hints (("Goal" :in-theory (enable expt))))

(defthm integerp-floor
  (integerp (floor x y)))

;bzo move
(defthm mod-by-2-less-than-1
  (implies (integerp x)
           (equal (< (mod x 2) 1)
                  (equal 0 (mod x 2)))))

(defthm collect-constants-+-lemma
  (implies (syntaxp (and (quotep k1) (quotep k2)))
           (equal (< (+ k1 a) (+ k2 b))
                  (< (+ (- k1 k2) a) b))))

(defthm arithhack
  (equal (+ (- x) (* 2 x) y)
         (+ x y)))

(defthm denominator-of-unary-/
 (implies (and (integerp x) ;generalize?
               ;(< 0 x)
;               (not (equal 0 x))
               )
          (equal (denominator (/ x))
                 (if (equal x 0)
                     1
                   (abs x)
                   )))
 :hints (("Goal" :use ((:instance acl2::Rational-implies2 (acl2::x (/ x))) (:instance acl2::numerator-/x (acl2::x x)))
          :in-theory (e/d (denominator) (acl2::Rational-implies2 ACL2::NUMERATOR-/X ACL2::*-R-DENOMINATOR-R)))))

(defthm mod-when-x-is-not-an-acl2-numberp
  (implies (not (acl2-numberp x))
           (equal (mod x y)
                  0))
  :hints (("Goal" :in-theory (enable mod floor))))

(defthm mod-when-y-is-not-an-acl2-numberp
  (implies (not (acl2-numberp y))
           (equal (mod x y)
                  (fix x)))
  :hints (("Goal" :in-theory (enable mod floor))))

;generalize?

(defthm odd-number-mod-1
  (IMPLIES (AND (INTEGERP I)
                (NOT (INTEGERP (* 1/2 I)))
                )
           (EQUAL (MOD (* 1/2 I) 1)
                  1/2))
  :hints (("Goal" :in-theory (e/d (evenp mod) (;ACL2::EVENP-COLLAPSE
                                               )))))

;restrict to when y is a constant?
(defthmd mod-stretch-base
  (IMPLIES (AND (INTEGERP (* 1/2 (FLOOR x y)))
                (INTEGERP y)
                (INTEGERP x) ;(rationalp x)
                )
           (EQUAL (MOD x y)
                  (if (equal 0 y)
                      x
                    (if (equal 0 x)
                        0
                      (MOD x (* 2 y))))))
  :hints (("Goal" :in-theory (enable mod-cancel))))

;can we generalize this?
(defthm mod-of-prod-of-mod
  (implies (and (integerp k)
                (integerp x)
                (integerp y)
                )
           (equal (mod (* k (mod x y)) y)
                  (mod (* k x) y)))
  :hints (("Goal" :in-theory (disable mod-cancel))))


;; (defthm floor-of-shift-right-2agen
;;   (implies (and (and (rationalp x)
;;                      (integerp n)
;;                      (<= 0 n))
;;                 (integerp (* (/ n) (floor x 1))))
;;            (equal (floor (* (/ n) x) 1)
;;                   (/ (floor x 1) n)))
;; )


;like  FL-EQUAL-REWRITE in RTL but about floor and a hyp is moved to conclusion
;arithmetic-3 doesn't have this
(defthm floor-equal-rewrite
  (implies (rationalp x)
           (equal (equal (floor x 1) n)
                  (and (<= n x)
                       (integerp n)
                       (< x (+ 1 n))))))

;generalize the 2's and 1/2's?
(defthm floor-of-shift-right-2
  (implies (rationalp x)
           (equal (floor (* 1/2 x) 1)
                  (if (integerp (* 1/2 (floor x 1)))
                      (* 1/2 (floor x 1))
                    (+ -1/2 (* 1/2 (floor x 1))))))
  :hints (("Goal" :in-theory (enable))))

(defthm floor-by-0
  (equal (FLOOR i 0)
         0
         )
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-by-twice-hack
 (implies (and (rationalp x)
               (rationalp y))
          (equal (FLOOR X (* 2 Y))
                 (FLOOR (* 1/2 X) Y)))
 :hints (("Goal" :cases ((equal 0 y)))))

;this may loop too
;trying to prove this without opening mod might yield some nice lemmas?
(defthmd mod-stretch-base-2
  (implies (and (not (integerp (* 1/2 (floor x y))))
                (integerp y)
                (integerp x) ;(rationalp a)
                )
           (equal (mod x y)
                  (- (mod x (* 2 y))
                     y)))
  :otf-flg t
  :hints (("Goal" :in-theory (e/d (evenp mod
                                         FLOOR-NORMALIZES-TO-HAVE-J-BE-1)
                                  (;acl2::evenp-collapse
                                   mod-cancel)))))

(DEFTHM INTEGERP-+-MINUS-*-1
  (IMPLIES (INTEGERP I) (INTEGERP (- I))))

(DEFTHM INTEGERP-+-MINUS-*-2
  (IMPLIES (AND (INTEGERP I) (INTEGERP J))
           (INTEGERP (+ I J))))

(DEFTHM INTEGERP-+-MINUS-*-3
  (IMPLIES (AND (INTEGERP I) (INTEGERP J))
           (INTEGERP (- I J))))

(DEFTHM INTEGERP-+-MINUS-*-4
  (IMPLIES (AND (INTEGERP I) (INTEGERP J))
           (INTEGERP (* I J))))

(in-theory (disable INTEGERP-+-MINUS-*)) ;bzo


(defthm ifix-integerp
  (implies (integerp x)
           (equal (ifix x) x)))


;bzo
;this seems like it could be expensive; do we need it?
(defthmd integer-=>-rational
  (implies (integerp x)
           (rationalp x)))

;is this fact built into acl2's type system? maybe that's why this isn't a t=p rule
(defthm denominator-is-positive
  (< 0 (denominator x))
  :rule-classes (:rewrite :linear))

;make t-p rules too?
(defthm positive-numerator
  (implies (rationalp v)
           (equal (< 0 (numerator v))
                  (< 0 v))))

(defthm negative-numerator
  (implies (rationalp v)
           (equal (< (numerator v) 0)
                  (< v 0))))

(defthm floor-when-i-is-not-an-acl2-numberp
  (implies (not (acl2-numberp i))
           (equal (floor i j)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

(defthm floor-when-j-is-not-an-acl2-numberp
  (implies (not (acl2-numberp j))
           (equal (floor i j)
                  0))
  :hints (("Goal" :in-theory (enable floor))))

;bzo The move-negated-term rules cover just a few of the many cases that can arise.
;Come up with a general theory (a :meta rule?) to handle this?
;Does such a rule already exist?

(defthm move-negated-term-to-other-side-of-<-term-1-on-lhs
  (implies (syntaxp (not (quotep x))) ;without the not-quotep test, the rule matches things like: (< -1 x)
           (equal (< (- x) y)
                  (< 0 (+ x y)))))

(defthm move-negated-term-to-other-side-of-<-term-1-on-rhs
  (implies (syntaxp (not (quotep y))) ;without the not-quotep test, the rule matches things like: (< x -1) ?
           (equal (< x (- y))
                  (< (+ y x) 0))))

(defthm move-negated-term-to-other-side-of-<-term-2-on-lhs
  (equal (< (+ Y (- x)) z)
         (< Y (+ x z))))

(defthm move-negated-term-to-other-side-of-<-term-2-on-rhs
  (equal (< z (+ Y (- x)))
         (< (+ x z) Y)))

(defthm expt-plus-expt-special-case
  (implies (integerp n)
           (equal (+ (expt 2 (+ -1 n)) (expt 2 (+ -1 n)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable exponents-add-unrestricted))))


(defthm equal-negation-same-sign
  (implies (and (integerp x)
                (integerp y)
                (equal (<= 0 x)
                       (<= 0 y)))
           (equal (equal x (- y))
                  (and (equal x 0) (equal y 0)))))


(defthm integerp-prod-3
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (integerp (* x y z))))


(defthm floor-when-j-is-0
  (equal (FLOOR i 0)
         0)
  :hints (("Goal" :in-theory (enable floor))))


;disable other one
(DEFTHM FLOOR-BOUNDS-better
  (IMPLIES (AND (RATIONALP X)
                (RATIONALP Y)
                ;(FORCE (NOT (EQUAL 0 Y)))
                )
           (AND (< (- (/ X Y) 1) (FLOOR X Y))
                (<= (FLOOR X Y) (/ X Y))))
  :RULE-CLASSES
  ((:LINEAR :TRIGGER-TERMS ((FLOOR X Y)))
   (:GENERALIZE))
:hints (("Goal" :use (:instance FLOOR-BOUNDS) :in-theory (disable FLOOR-BOUNDS))))

(in-theory (disable FLOOR-BOUNDS))


(defthm integer-length-of-floor-by-2
  (implies (integerp x)
           (equal (integer-length (floor x 2))
                  (if (and (not (equal 0 x)) (not (equal -1 x)))
                      (+ -1 (integer-length x))
                    0)))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable integer-length))))


(defthm integer-length-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (integer-length i)
                  0)))

(defthm truncate-when-j-is-zero
  (equal (truncate i 0)
         0)
  :hints (("Goal" :in-theory (enable truncate))))

;bzo ACL2::TRUNCATE-TYPE should be improved (for instance, it shouldn't require j not to be 0 so often).
(defthm truncate-nonnegative-type
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (<= 0 J)
                (INTEGERP J))
           (<= 0 (TRUNCATE I J)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

(defthm truncate-nonpositive-type
  (IMPLIES (AND (INTEGERP I)
                (<= 0 I)
                (<= J 0) ;note this
                (INTEGERP J))
           (<= (TRUNCATE I J) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

(defthm truncate-nonpositive-type2
  (IMPLIES (AND (INTEGERP I)
                (<= I 0) ;note this
                (<= 0 J) ;bzo
                (INTEGERP J))
           (<= (TRUNCATE I J) 0))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

(defthm truncate-nonnegative-type-2
  (IMPLIES (AND (INTEGERP I)
                (<= I 0) ;note this
                (<= J 0) ;note this
                (INTEGERP J))
           (<= 0 (TRUNCATE I J)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use (:instance ACL2::TRUNCATE-TYPE (acl2::x i) (acl2::y j))
           :in-theory (disable ACL2::TRUNCATE-TYPE))))

;loops with expt-minus
;add theory-inv
(defthmd unary-/-of-expt
  (equal (/ (EXPT 2 M))
         (expt 2 (- m))))

;loops!
;add theory-inv
(defthmd expt-gather
 (implies (and (integerp m)
               (integerp n))
          (equal (* (EXPT 2 m) (EXPT 2 n))
                 (expt 2 (+ m n))))
 :hints (("Goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED))))


(defthm expt-less-than-1-hack
  (implies (and (< n 0)
                (integerp n))
           (< (expt 2 n) 1)
           )
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable expt))))

(defthm expt-2-equal-1-rewrite
  (equal (equal (expt 2 n) 1)
         (or (not (integerp n))
             (= n 0)))
  :hints (("Goal" :use (:instance expt-less-than-1-hack)
           :in-theory (disable expt-less-than-1-hack))))

(DEFTHM FLOOR-BOUNDS-BETTER-1-alt
  (IMPLIES (AND (< 0 y)
                (RATIONALP X)
                (RATIONALP Y)
                )
           (<= (* y (FLOOR X Y)) X))
  :RULE-CLASSES
  (:rewrite (:LINEAR :TRIGGER-TERMS ((FLOOR X Y))))
  :HINTS
  (("Goal" :USE (:INSTANCE FLOOR-BOUNDS)
    :IN-THEORY (DISABLE FLOOR-BOUNDS))))

(DEFTHM FLOOR-BOUNDS-BETTER-2-alt
  (IMPLIES (AND (< 0 y)
                (RATIONALP X)
                (RATIONALP Y)
                )
           (< X (+ y (* y (FLOOR X Y)))))
  :RULE-CLASSES
  (:rewrite (:LINEAR :TRIGGER-TERMS ((FLOOR X Y))))
  :HINTS
  (("Goal" :USE (:INSTANCE FLOOR-BOUNDS)
    :IN-THEORY (DISABLE FLOOR-BOUNDS))))

(defthm integerp-of-quotient-of-expts
  (implies (and (integerp n1)
                (integerp n2))
           (equal (integerp (* (expt 2 n1) (/ (expt 2 n2))))
                  (<= n2 n1)))
  :hints (("Goal" :use (:instance acl2::integerp-expt (n (- n1 n2)))
           :in-theory (disable acl2::integerp-expt))))

(defthm integerp-prod-of-3-first-two
  (implies (and (integerp (* a b))
                (integerp c))
           (integerp (* a b c)))
  :hints (("Goal" :in-theory (disable acl2::integerp-+-minus-*-4)
           :use (:instance acl2::integerp-+-minus-*-4 (acl2::i (* a b)) (acl2::j c)))))


;drop?
(defthm expt-hack-1
  (implies (integerp n)
           (equal (+ (EXPT 2 (+ -1 N)) (EXPT 2 (+ -1 N)))
                  (expt 2 n)))
  :hints (("Goal" :in-theory (enable EXPONENTS-ADD-UNRESTRICTED))))


(defthm arith-move-negated-term
  (implies (and (acl2-numberp x)
                (acl2-numberp z))
           (equal (EQUAL (+ x (- y)) z)
                  (equal x (+ y z)))))

(defthm mod-same
  (equal (mod x x)
         0)
  :hints (("Goal" :in-theory (enable acl2::mod-cancel))))

(defthm combine-constants-in-equal-of-times
  (implies (and (syntaxp (and (quotep k) (quotep j)))
                (acl2-numberp k)
                (acl2-numberp x)
                (acl2-numberp j)
                )
           (equal (EQUAL (* k x) j)
                  (if (equal 0 k)
                      (equal 0 j)
                    (equal x (/ j k))))))

(DEFTHM my-EQUAL-/
  (IMPLIES (AND (syntaxp (not (quotep x))) ;otherwise can loop with ACL2::COMBINE-CONSTANTS-IN-EQUAL-OF-TIMES
                (FC (ACL2-NUMBERP X))
                (FC (NOT (EQUAL 0 X))))
           (EQUAL (EQUAL (/ X) Y)
                  (EQUAL 1 (* X Y))))
  :HINTS (("Goal" :by EQUAL-/)))

(in-theory (disable EQUAL-/))


;for example, rewrites (<= 2 n) to t, when we know (<= 5 n)
(defthm remove-redundant-<=-hyps
  (implies (and (syntaxp (quotep small))
                (<= large N) ;large is a free variable - will this match?
                (syntaxp (quotep large))
                (<= small large)
                )
           (equal (< n small)
                  nil)))

;for example, rewrites (< 2 n) to t, when we know (< 5 n)
(defthm remove-redundant-less-thans
  (implies (and (syntaxp (quotep small))
                (< large N) ;large is a fre variable
                (syntaxp (quotep large))
                (<= small large)
                )
           (equal (< small n)
                  t)))

;trying disabled
(defthmd floor-*-1/2-expt-2
  (implies (and (integerp n)
                (< 1 n))
           (equal (floor (* 1/2 (expt 2 n)) 2)
                  (* 1/4 (expt 2 n))))
  :hints (("goal" :in-theory (enable expt floor))))

(in-theory (disable loghead))

(defthm integerp-of-loghead
  (integerp (loghead size i)))

(defthm loghead-nonnegative-rewrite
  (<= 0 (loghead size i)))


;see also LOGHEAD-TYPE
(defthm loghead-nonnegative-linear
  (<= 0 (loghead size i))
  :rule-classes :linear)

(defthm loghead-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (loghead size i)
                  0))
  :hints (("Goal" :in-theory (enable loghead))))

(defthm loghead-when-i-is-0
  (equal (loghead size 0)
         0)
  :hints (("Goal" :in-theory (enable loghead))))

(in-theory (disable loghead-size-0)) ;loghead-when-i-is-0 is better

(defthm loghead-when-size-is-not-positive
  (implies (<= size 0)
           (equal (loghead size i)
                  0))
  :hints (("Goal" :in-theory (enable loghead))))

(in-theory (disable loghead-0-i)) ;since we have LOGHEAD-WHEN-SIZE-IS-NON-POSITIVE

(defthm loghead-when-size-is-not-an-integerp
  (implies (not (integerp size))
           (equal (loghead size i)
                  0))
  :hints (("Goal" :in-theory (enable loghead))))

(defthm unsigned-byte-p-loghead-better
  (implies (<= size bits)
           (equal (unsigned-byte-p bits (loghead size i))
                  (and (integerp bits)
                       (<= 0 bits))))
  :hints (("Goal" :use (:instance unsigned-byte-p-loghead (size1 bits) (size size))
           :in-theory (disable unsigned-byte-p-loghead))))

(in-theory (disable unsigned-byte-p-loghead)) ;we'll use unsigned-byte-p-loghead-better instead

(defthm unsigned-byte-p-loghead-forward-chaining
  (implies (and (integerp n)
                (<= 0 n))
           (unsigned-byte-p n (loghead n x)))
  :hints (("goal" :in-theory (enable unsigned-byte-p loghead)))
  :rule-classes ((:forward-chaining :trigger-terms ((loghead n x)))))

;we could use min in the conclusion
(defthm loghead-loghead-better
  (equal (loghead size1 (loghead size i))
         (if (< (nfix size1) (nfix size))
             (loghead (nfix size1) i)
           (loghead (nfix size) i)))
  :hints (("Goal" :in-theory (e/d ()
                                  (loghead-loghead
                                   loghead-leq))
           :use loghead-loghead)))

(in-theory (disable loghead-loghead))

(defthm loghead-does-nothing-rewrite
  (equal (equal (loghead n x) x)
         (unsigned-byte-p (nfix n) x))
  :hints (("Goal" :in-theory (enable LOGHEAD UNSIGNED-BYTE-P INTEGER-RANGE-P))))

;gen?
(defthm loghead-1
  (equal (loghead 1 x)
         (logcar x))
  :hints (("goal" :in-theory (enable loghead logcons))))

(defthm loghead-<
  (implies (and (< x y)
                (<= 0 x))
           (< (loghead n x) y))
  :hints (("goal" :in-theory (enable loghead))))

(defthm loghead-<=
  (implies (and (<= x y)
                (<= 0 x))
           (<= (loghead n x) y))
  :hints (("goal" :in-theory (enable loghead))))


;this version doesn't have the FORCEd hyps (or any hyps for that matter)
(defthm logcar-loghead-better
  (equal (logcar (loghead size i))
         (if (or (not (integerp size))
                 (<= size 0))
             0
           (logcar i)))
  :hints
  (("Goal" :use logcar-loghead
    :in-theory (e/d (
                     )
                    (logcar-loghead)))))

(in-theory (disable logcar-loghead))



;this really should go in lrdt instead of logehead*??
(defthm loghead*-better
  (implies (and (integerp size)
                (<= 0 size)
                )
           (equal (loghead size i)
                  (if (equal size 0)
                      0
                    (logcons (logcar i)
                             (loghead (1- size) (logcdr i))))))
  :rule-classes
  ((:definition :clique (loghead)
                :controller-alist ((loghead t t))))
  :hints (("Goal" :use (:instance loghead*) :in-theory (disable loghead*))))

;(in-theory (disable LOGHEAD*)) ;already disabled?

(defthm loghead-+-cancel-better
  (implies (and ;(integerp size)
                ;(>= size 0)
                (integerp i)
                (integerp j)
                (integerp k))
           (equal (equal (loghead size (+ i j))
                         (loghead size (+ i k)))
                  (equal (loghead size j)
                         (loghead size k))))
  :hints (("Goal" :use (:instance loghead-+-cancel)
           :in-theory (disable loghead-+-cancel))))

(in-theory (disable loghead-+-cancel))

;make more versions of this
;bzo normalize the leading constant of things like (LOGHEAD 16 (+ 65535 x)).
(defthm loghead-+-cancel-better-alt
  (implies (and ;(integerp size)
                ;(>= size 0)
                (integerp i)
                (integerp j)
                (integerp k))
           (equal (equal (loghead size (+ j i))
                         (loghead size (+ k i)))
                  (equal (loghead size j)
                         (loghead size k))))
  :hints (("Goal" :use (:instance loghead-+-cancel)
           :in-theory (disable loghead-+-cancel))))

;see also the :meta rule about loghead. -ews
(defthm loghead-+-loghead-better
  (equal (loghead size (+ i (loghead size j)))
         (if (integerp j)
             (loghead size (+ i j))
           (loghead size i)))
  :hints (("Goal" :cases ((integerp i) (not (acl2-numberp i)))
           :in-theory (enable loghead-+-loghead))))

(in-theory (disable LOGHEAD-+-LOGHEAD)) ;our rule is better

(defthm loghead-+-loghead-better-alt
  (equal (loghead size (+ (loghead size i) j))
         (if (integerp i)
             (loghead size (+ i j))
           (loghead size j)))
  :hints (("Goal" :use (:instance  loghead-+-loghead-better (i j) (j i)))))

(defthm loghead-+-loghead-better-alt-three-addends
  (equal (loghead size (+ i1 i2 (loghead size j)))
         (if (integerp j)
             (loghead size (+ i1 i2 j))
           (loghead size (+ i1 i2))))
  :hints (("Goal" :use (:instance loghead-+-loghead-better (i (+ i1 i2)) (j j)))))

; improve loghead-cancel-better-alt, etc.
(defthm loghead-sum-subst-helper
  (implies (and (equal (loghead n x) y)
                (syntaxp (quotep y))
;                (integerp x)
                (integerp z)  ; could we say (or (integerp x) (integerp z)) ?
                )
           (equal (loghead n (+ x z))
                  (if (integerp x)
                      (loghead n (+ y z))
                    (if (acl2-numberp x)
                        0
                      (loghead n z)
                      ))))
  :hints (("Goal" :in-theory (enable LOGHEAD-+-LOGHEAD-better))))



(defthm loghead-sum-subst
  (implies (and (equal (loghead n x) (loghead n y))
                (syntaxp (and (term-order y x)
                              (not (equal y x))))
;                (integerp x)
                (integerp y)
                (integerp z) ;bzo can we drop this? improve loghead-cancel-better-alt, etc. similarly
                )
           (equal (loghead n (+ x z))
                  (if (integerp y)
                      (if (integerp x)
                          (loghead n (+ y z))
                        (if (acl2-numberp x)
                            0
                          (loghead n z)
                          ))
                    (loghead n z)
                    )))
  :hints (("Goal" :cases ((integerp z) (not (acl2-numberp z))))))


;improve this
(defthm loghead-sum-subst-alt
  (implies (and (equal (loghead n x) (loghead n y))
                (syntaxp (and (term-order y x)
                              (not (equal y x))))
                (case-split (integerp x))
                (case-split (integerp y))
;                (integerp z) ;bzo improve loghead-cancel-better-alt, etc. similarly
                )
           (equal (loghead n (+ z x))
                  (loghead n (+ z y))))
  :hints (("Goal" :cases ((integerp z) (not (acl2-numberp z))))))

(defthm loghead-of-minus
  (equal (loghead n (- x))
         (if (integerp x)
             (if (equal 0 (loghead n x))
                 0
               (- (expt 2 n) (loghead n x)) ;the usual case
               )
           0))
  :otf-flg t
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable loghead
                              EXPONENTS-ADD-UNRESTRICTED))))

(defthm loghead-equal-move-minus
  (implies (and (integerp a)
                (integerp j)
                (integerp k))
           (equal (EQUAL (LOGHEAD size A) (LOGHEAD size (+ (- J) K)))
                  (EQUAL (LOGHEAD size (+ j A)) (LOGHEAD size K))))
  :hints (("Goal" :use (:instance LOGHEAD-+-CANCEL-BETTER (size size) (i j) (j a) (k (- k j)))))
  )

(defthm loghead-plus-constant-equal-constant
  (implies (and (syntaxp (and (quotep j)
                              (quotep k)))
                (integerp a)
                (integerp j)
                (integerp k)
                (<= 0 size)
                (integerp size)
                )
           (equal (equal (loghead size (+ j a)) k)
                  (and (unsigned-byte-p size k)
                       (equal (loghead size a) (loghead size (- k j)))))))

;This can lead to case splits, so we disable it by default.
(defthmd loghead-of-one-less-than-x
  (implies (and (syntaxp (not (quotep x))) ;don't unify (+ 1 x) with a constant
                (integerp x)
                (<= 0 n))
           (equal (loghead n (+ -1 x))
                  (if (equal (loghead n x) 0)
                      (+ -1 (expt 2 n))
                    (+ -1 (loghead n x)))))
  :hints (("Goal" :in-theory (e/d (loghead
                                     UNSIGNED-BYTE-P
                                     INTEGER-RANGE-P ;prove a rule for integer-range-p of (+ 1 x)
                                     imod
                                     )
                                  (mod-cancel
                                   MOD-STRETCH-BASE ;looped!
                                   MOD-STRETCH-BASE-2 ;looped!
                                   )))))

;can this loop?
;generalize?
(defthm loghead-+-reduce
  (implies (and (equal (loghead size y) z) ;z is a free variable
                (syntaxp (and (quotep z) (not (quotep y))))
                (integerp x)
                (integerp y)
                )
           (equal (loghead size (+ x y))
                  (loghead size (+ x z)))))

(defthm LOGHEAD-of-*-expt
  (implies (and (integerp x)
                (<= n m) ;handle the other case
                (integerp n)
                (<= 0 n)
                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* (expt 2 m) X))
                  0))
  :hints (("Goal" :in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus EXPONENTS-ADD))
           :do-not '(generalize eliminate-destructors))))

(defthm LOGHEAD-of-*-expt-alt
  (implies (and (integerp x)
                (<= n m) ;handle the other case
                (integerp n)
                (<= 0 n)
                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* X (expt 2 m)))
                  0))
  :hints (("Goal" :in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus EXPONENTS-ADD))
           :do-not '(generalize eliminate-destructors))))

(defthm LOGHEAD-of-*-expt-const
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (>= (expo k) n)
                (integerp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (LOGHEAD n (BINARY-* k X))
                  0))
  :hints (("Goal" :in-theory (disable LOGHEAD-of-*-expt)
           :use (:instance  LOGHEAD-of-*-expt (m (expo k))))))

(defthm loghead-of-*-expt-2-special
  (implies (integerp x)
           (equal (loghead n (binary-* (expt 2 n) x))
                  (logapp n 0 (loghead 0 x))
                  ))
  :hints (("Goal" :in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus exponents-add))
           :do-not '(generalize eliminate-destructors))))


(defthm loghead-of-*-expt-2-special-const
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n))
                (integerp x))
           (equal (loghead n (binary-* k x))
                  (logapp n 0 (loghead 0 x))
                  ))
  :hints (("Goal" :use (:instance loghead-of-*-expt-2-special (n (expo k)))
           :in-theory (disable loghead-of-*-expt-2-special))))

(defthm loghead-of-prod-lemma
  (implies (integerp y)
           (equal (loghead n (* (loghead n x) y))
                  (loghead n (* (ifix x) y))))
  :hints (("Goal" :in-theory (enable loghead imod))))

(defthm loghead-of-prod-lemma-alt
  (implies (integerp y)
           (equal (loghead n (* y (loghead n x)))
                  (loghead n (* (ifix x) y))))
  :hints (("Goal" :use (:instance loghead-of-prod-lemma)
           :in-theory (disable loghead-of-prod-lemma))))

;why is denominator suddenly showing up?

;make a version that matches on constants
(defthm LOGHEAD-of-*-expt-other-case
  (implies (and (integerp x)
                (< m n) ;handle the other case
                (integerp n)
                (<= 0 n)
                (<= 0 m)
                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* (expt 2 m) X))
                  (BINARY-* (expt 2 m) (LOGHEAD (- n m) X))
                  ))
  :hints (("Goal" ;:in-theory (e/d (unary-/-of-expt loghead expt-gather) (expt-minus EXPONENTS-ADD))
           :use (:instance INTEGERP-EXPT (n (- n m)))
           :in-theory (e/d (loghead ifix
                                    mod-cancel)
                           (INTEGERP-OF-INVERSE-OF-EXPT
                                          MOD-X-I*J ;yucky force!
                                           ))
           :do-not '(generalize eliminate-destructors))))



(defthm LOGHEAD-of-*-expt-other-case-constant-version
  (implies (and (syntaxp (quotep k))
                (power2p k)
                (integerp x)
                (< (expo k) n) ;handle the other case
                (integerp n)
                (<= 0 n)
                (<= 0 (expo k))
;                (integerp m)
                )
           (equal (LOGHEAD n (BINARY-* k X))
                  (BINARY-* k (LOGHEAD (- n (expo k)) X))
                  ))
  :hints (("Goal" :use (:instance  LOGHEAD-of-*-expt-other-case (m (expo k)))))
  )


(defthm loghead-of-sum-of-prod-of-loghead-lemma
  (implies (and (integerp x)
                (integerp y)
                (integerp a)
                )
           (equal (loghead n (+ a (* y (loghead n x))))
                  (loghead n (+ a (* x y)))))
  :hints (("Goal" :in-theory (disable loghead-of-prod-lemma
                                      loghead-of-prod-lemma-alt

                                      )
           :use (:instance loghead-of-prod-lemma (x x) (y y) (N n)))))


(defthm loghead-of-sum-of-prod-of-loghead-lemma-better2
  (implies (and (integerp x)
                (integerp y)
                (integerp a)
                )
           (equal (loghead n (+ a (- (loghead n x))))
                  (loghead n (+ a (- x)))))
  :hints (("Goal" :in-theory (disable loghead-of-sum-of-prod-of-loghead-lemma
                                      LOGHEAD-+-CANCEL-0 ;was forcing
                                      LOGHEAD-LOGHEAD-BETTER
                                      LOGHEAD-OF-MINUS
                                      )
           :use (:instance loghead-of-sum-of-prod-of-loghead-lemma (y -1)))))


(defthm loghead-hack
  (equal (loghead 16 (+ -65535 off))
         (loghead 16 (+ 1 off)))
  :hints (("Goal" :in-theory (enable loghead
                                     imod ifix))))

(defthm loghead-induction t
  :rule-classes ((:induction :pattern (loghead n x)
                             :condition t
                             :scheme (loglistr n x))))

;move to loghead.lisp
;trying disabled
(defthmd loghead-almost
  (implies (and (not (unsigned-byte-p n x))
                (unsigned-byte-p (1+ n) x)
                )
           (equal (loghead n x)
                  (if (integerp n)
                      (- x (ash 1 n)) ;use expt here?
                    0
                    )))
  :hints (("goal" ; :induct t
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d ( ;LRDT ;open-logcons
                            logcdr-of-sum
                            ;ash* ;bzo seems to loop with LOGCONS-OF-0 (problem only arose in the move to acl2 version 3.0)
                            loghead*-better
                            unsigned-byte-p*
                            logcdr--

                            ) ( ;evenp-of-logcons
                            UNSIGNED-BYTE-P-FORWARD
                            ARITH-MOVE-NEGATED-TERM
                            expt-2-cruncher)))))

;See also the rule loghead-almost.
;Is this rule too expensive to leave enabled?
(defthmd loghead-split-into-2-cases
  (implies (and (< x (* 2 (expt 2 n)))
                (<= 0 x)
                (integerp x)
                (integerp n) ;drop?
                )
           (equal (loghead n x)
                  (if (< x (expt 2 n))
                      x
                    (- x (expt 2 n)))))
  :hints (("Goal" :use (:instance LOGHEAD-ALMOST (n n) (x x))
           :expand (UNSIGNED-BYTE-P (+ 1 N) X)
           :in-theory (e/d (ash EXPONENTS-ADD-UNRESTRICTED) (ARITH-MOVE-NEGATED-TERM
                                                             LOGHEAD-ALMOST)))))

;Is this rule too expensive to leave enabled?
(defthmd loghead-sum-split-into-2-cases
  (implies (and (integerp i)
                (integerp j)
;                (integerp n)
        ;        (<= 0 n)
                )
           (equal (loghead n (+ i j))
                  (if (< (+ (loghead n i) (loghead n j)) (expt 2 n))
                      (+ (loghead n i) (loghead n j))
                    (+ (loghead n i) (loghead n j) (- (expt 2 n))))))
  :hints (("Goal" :in-theory (disable loghead-split-into-2-cases)
           :use (:instance loghead-split-into-2-cases
                           (n n)
                           (x (+ (loghead n i) (loghead n j)))
                           ))))

(defthm loghead-sum-split-into-2-when-i-is-a-constant
  (implies (and (syntaxp (quotep i))
                (integerp i)
                (integerp j)
;                (integerp n)
 ;               (<= 0 n)
                )
           (equal (loghead n (+ i j))
                  (if (< (+ (loghead n i) (loghead n j)) (expt 2 n))
                      (+ (loghead n i) (loghead n j))
                    (+ (loghead n i) (loghead n j) (- (expt 2 n))))))
  :hints (("Goal" :in-theory (enable  loghead-sum-split-into-2-cases))))



;; (defstub foo (x) t)

(defthm loghead-sum-chop-first-arg-when-constant
  (implies (and (syntaxp (and (quotep x)
                              (quotep n) ;bzo without this we got a loop; change other rules similarly
                              ))
                (not (unsigned-byte-p n x))
                (<= 0 n)
                (integerp n)
                (integerp x)
                (integerp y))
           (equal (loghead n (+ x y))
                  (loghead n (+ (loghead n x) y)))))



;bzo generalize
(defthm loghead-bound
  (and ;(<= 0 (loghead 32 x))
       (<= (loghead 32 x) (1- (expt 2 32))))
  :hints (("goal" :in-theory (disable unsigned-byte-p-loghead)
           :use ((:instance unsigned-byte-p-loghead (i x) (size1 32) (size 32)))))
  :rule-classes :linear)  ;;why not :rewrite too?

;; ;acl2 does something gross here and loses the (integerp x) fact
;; ;kill this one?
;; (defthm loghead-cancel-hack
;;   (implies (and (integerp k)
;;                 (<= 0 x)
;;                 (integerp x)
;;                 (integerp n)
;;                 (<= 0 n)
;;                 )
;;            (equal (equal x (loghead n (+ k x)))
;;                   (and (unsigned-byte-p n x)
;;                        (equal 0 (loghead n k)))))
;;   :otf-flg t
;;   :hints ( ("Goal" :use (:instance loghead-identity (size n) (i x))
;;             :do-not-induct t
;;             :in-theory (e/d (loghead-sum-split-into-2-cases
;;      ;UNSIGNED-BYTE-P-FORWARD-TO-NONNEGATIVE-INTEGERP
;;                              )
;;                             (LOGHEAD-TYPE ;bzo these disables are gross!
;;                              loghead-identity
;;                              LOGHEAD-DOES-NOTHING-REWRITE
;;                              UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING)))))

(defthm loghead-cancel-lemma
  (implies (and (integerp a)
                (integerp size)
                (<= 0 size)
                )
           (equal (equal k (loghead size (+ a k)))
                  (and (unsigned-byte-p size k)
                       (equal 0 (loghead size a)))))
  :hints (("Goal" :use (:instance loghead-plus-constant-equal-constant (size size) (j k) (a a) (k k))
           :in-theory (disable loghead-plus-constant-equal-constant))))

(defthm loghead-cancel-lemma-alt
  (implies (and (integerp a)
                (integerp size)
                (<= 0 size)
                )
           (equal (equal k (loghead size (+ k a)))
                  (and (unsigned-byte-p size k)
                       (equal 0 (loghead size a)))))
  :hints (("Goal" :use (:instance loghead-cancel-lemma)
           :in-theory (disable loghead-cancel-lemma))))

;;Help proofs go faster by essentially doing some substitution before ACL2 would get around to substituting.
;;does this rule match both ways on an (equal x y) term?
;; this rule allows ACL2 to quickly realize that these two facts contradict:
;;       (EQUAL x (LOGHEAD 16 (+ 4 y)))
;;       (EQUAL x (LOGHEAD 16 (+ -1 y))))

(defthm loghead-compare-hack
  (implies (and (equal x (loghead n z)) ;z is a free variable
                (not (equal 0 (loghead n (- z y))))
                (integerp y)
                (integerp z)
                )
           (not (equal x (loghead n y)))))

(defthm loghead-cancel-lemma-3
  (implies (and (integerp a)
                (integerp b)
                (integerp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (EQUAL (LOGHEAD n (+ A b X)) X)
                  (and (unsigned-byte-p n x)
                       (EQUAL (LOGHEAD n (+ a b)) 0))))
  :hints (("Goal" :use (:instance loghead-cancel-lemma (size n) (k x) (a (+ a b)))
           :in-theory (disable loghead-cancel-lemma))))

;; (thm
;;  (implies (and (syntaxp (quotep k))
;;                (integerp b)
;;                (integerp a)
;;                (integerp k)
;;                (<= 0 k)
;;                (< k (* 2 65536))
;;                )
;;           (implies (equal (loghead 16 k) (loghead 16 (+ a b)))
;;                    (equal k (+ (loghead 16 a) (loghead 16 b)))))
;;  :hints (("Goal" :in-theory (enable loghead-sum-split-into-2-cases))))

;expensive!

(defthmd loghead-hack2
  (implies (and (equal (expt 2 n) (+ (loghead n a) (loghead n b)))
                (integerp a)
                (integerp b)
                )
           (equal (loghead n (+ a b))
                  0))
  :hints (("Goal" :in-theory (enable loghead-sum-split-into-2-cases))))

;; Allows ACL2 to quicly see that facts like this contradict:
;; (EQUAL x (LOGHEAD 16 (+ 4 y)))
;; (EQUAL (LOGHEAD 16 (+ 3 x)) y))

(defthm loghead-compare-hack-2
  (implies (and (equal y (loghead n (+ a x)))
                (not (equal 0 (loghead n (+ a b))))
                (integerp a)
                (integerp b)
                )
           (equal (equal x (loghead n (+ b y)))
                  nil))
  :hints (("Goal" :use (:instance loghead-cancel-lemma-3 (n n) (b b))
           :in-theory (disable loghead-cancel-lemma-3))))

(defthm evenp-of-loghead
  (equal (evenp (loghead size i))
         (or (zp size)
             (evenp (ifix i))))
  :hints (("Goal" :in-theory (e/d (loghead imod)
                                  (mod-cancel)))))

;; ;bzo zz will going against acl2's order be bad?

;; ;Just like term-order, except it calls our-lexorder
;; (defun our-lexorder (x y)
;;   "Documentation available via :doc"
;;   (declare (xargs :guard t))
;;   (cond ((atom x)
;;          (cond ((atom y) (our-alphorder x y)) (t t)))
;;         ((atom y) nil)
;;         ((equal (car x) (car y))
;;          (our-lexorder (cdr x) (cdr y)))
;;         (t (our-lexorder (car x) (car y)))))

;; ;Just like term-order, except it calls our-lexorder
;; (defun our-term-order (term1 term2)
;;   (mv-let (var-count1 fn-count1 p-fn-count1)
;;           (var-fn-count term1)
;;           (mv-let (var-count2 fn-count2 p-fn-count2)
;;                   (var-fn-count term2)
;;                   (cond ((< var-count1 var-count2) t)
;;                         ((> var-count1 var-count2) nil)
;;                         ((< fn-count1 fn-count2) t)
;;                         ((> fn-count1 fn-count2) nil)
;;                         ((< p-fn-count1 p-fn-count2) t)
;;                         ((> p-fn-count1 p-fn-count2) nil)
;;                         (t (our-lexorder term1 term2))))))

;can this loop (if y is a loghead call?)?
(defthm loghead-subst
  (implies (and (equal (loghead m x) y) ;y and m are free variables
                (syntaxp (smaller-term y x))
                (<= n m)
                (integerp m)
                )
           (equal (loghead n x)
                  (loghead n y))))

;The proof of this was a little tricky (due to ACL2 trying to get smart with substitution?). -ews
(defthm loghead-subst2
  (implies (and (equal (loghead m x) (loghead m y)) ;y and m are free variables
                (syntaxp (smaller-term y x))
                (<= n m)
                (integerp m)
                )
           (equal (loghead n x)
                  (loghead n y)))
  :hints (("Goal" :use ((:instance loghead-subst (y (loghead m y)))
                        (:instance LOGHEAD-LOGHEAD-BETTER (size1 n) (size m) (i y)))
           :in-theory (disable loghead-subst LOGHEAD-LOGHEAD-BETTER))))

(defthm loghead-+-cancel-0-better
  (implies (and (integerp j)
                (integerp i)
                )
           (equal (equal (loghead size (+ i j))
                         (loghead size i))
                  (equal (loghead size j) 0)))
  :hints (("Goal" :use (:instance acl2::loghead-+-cancel-0 (acl2::i i) (acl2::j j) (acl2::size size))
           :in-theory (disable acl2::loghead-+-cancel-0))))

(in-theory (disable acl2::loghead-+-cancel-0))

(defthm loghead-+-cancel-0-alt
  (implies (and (integerp m)
                (integerp k)
                )
           (equal (equal (loghead n k) (loghead n (+ m k)))
                  (equal 0 (loghead n m)))))

(defthm loghead-sum-equality-move-negated-addend
  (implies (and (integerp j)
                (integerp k)
                (integerp m)
                (integerp a)
                )
           (equal (equal (loghead 16 j) (loghead 16 (+ k (- a) m)))
                  (equal (loghead 16 (+ j a)) (loghead 16 (+ k m))))))

(defthm loghead-cancellation-hack
  (implies (and (not (equal (loghead size j) (loghead size k)))
                (integerp x)
                (integerp j)
                (integerp k))
           (equal (equal (loghead size (+ j x)) (+ k x))
                  nil))
  :hints (("Goal" :in-theory (disable acl2::loghead-+-cancel-better-alt
                                      acl2::loghead-sum-subst
                                      acl2::loghead-compare-hack)
           :use (:instance acl2::loghead-+-cancel-better-alt (acl2::size size) (acl2::j j) (acl2::k k) (acl2::i x)))))

;more like this? this lets' things get done faster, since ACL2 doesn't have to get around to substituting...
(defthmd loghead-compare-hack-2-alt
  (implies (and (equal y (+ a x))
                (not (equal 0 (loghead n (+ a b))))
                (integerp a)
                (integerp b)
                )
           (equal (equal x (loghead n (+ b y)))
                  nil))
  :hints (("Goal" :use (:instance acl2::loghead-cancel-lemma-3 (acl2::n n) (acl2::b b) (acl2::x x) (acl2::a a))
           :in-theory (disable acl2::loghead-cancel-lemma-3))))



(defthmd loghead-sum-equality-move-negative
  (implies (and (syntaxp (quotep k))
                (< k 0)
                (integerp k)
                (integerp a)
                )
           (equal (equal (loghead 16 (+ k a)) b)
                  (and (equal (loghead 16 a) (loghead 16 (+ (- k) b)))
                       (unsigned-byte-p 16 b))))
  :hints (("Goal" :use (:instance acl2::loghead-+-cancel (acl2::size 16) (acl2::i (- k)) (acl2::j (+ k a)) (acl2::k b))
           :in-theory (disable acl2::loghead-+-cancel
                               ))))
;bzo gen
(defthm loghead-expt-hack
  (equal (loghead size (expt 2 size))
         0)
  :hints (("Goal" :in-theory (enable loghead))))


(defthm loghead-of-minus-2-to-the-size
  (equal (loghead size (- (expt 2 size)))
         0)
  :hints (("Goal" :in-theory (enable loghead))))


(defthm loghead-cancel-hack
  (implies (and (integerp a)
                (integerp freek)
                (integerp offset2)
                (integerp freeoff))
           (equal (equal (loghead size (+ a offset2)) (loghead size (+ freek freeoff a)))
                  (equal (loghead size offset2) (loghead size (+ freek freeoff))))))
;; ;gen
;; (defthm loghead-sum-loghead-alt
;;   (equal (loghead 16 (+ y (loghead 16 x)))
;;          (if (integerp x)
;;              (if (integerp y)
;;                  (loghead 16 (+ x y))
;;                (if (acl2-numberp y)
;;                    0
;;                  (loghead 16 x)))
;;            (loghead 16 y)))
;;   :otf-flg t
;;   :hints (("Goal" :use (:instance LOGHEAD-+-LOGHEAD (size 16) (i y) (j (fix x)))
;;            :in-theory (disable LOGHEAD-+-LOGHEAD))))

;; ;gen
;; (defthm loghead-sum-loghead
;;   (equal (loghead 16 (+ (loghead 16 x) y))
;;          (if (integerp x)
;;              (if (integerp y)
;;                  (loghead 16 (+ x y))
;;                (if (acl2-numberp y)
;;                    0
;;                  (loghead 16 x)))
;;            (loghead 16 y))))

(defthm loghead-subst-weird
  (implies (and (syntaxp (quotep k))
                (equal (loghead 16 offset2)
                       (loghead 16 (+ freek freeoff)))
                (syntaxp (quotep freek))
                (syntaxp (smaller-term freeoff offset2))
                (integerp k)
                (integerp freek)
                (integerp offset2)
                (integerp freeoff))
           (equal (loghead 16 (+ k offset2))
                  (loghead 16 (+ k (+ freek freeoff)))
                  ))
  :otf-flg t
  :hints (("Goal" :use (:instance LOGHEAD-+-LOGHEAD-BETTER (size 16) (acl2::i offset2) (acl2::j k))
           :in-theory (disable acl2::loghead-+-cancel-better
                               acl2::loghead-subst2
                               acl2::loghead-subst
                               acl2::loghead-+-loghead-better))))


(defthm loghead-+-expt-alt
  (implies (integerp x)
           (equal (loghead n (+ (expt 2 n) x))
                  (loghead n x)))
  :hints (("goal" :cases ((natp n)))))

;could allow k to be the negative of a power of 2...
;more generally, k could be any integer multiple of 2^n
(defthm loghead-+-expt-constant-version
  (implies (and (syntaxp (quotep k))
                (equal (expt 2 n) k)
                (integerp x)
                )
           (equal (loghead n (+ k x))
                  (loghead n x))))

(defthm loghead-ignores-subtraction-of-expt-alt
  (implies (integerp x)
           (equal (loghead n (+ (- (expt 2 n)) x))
                  (loghead n x))))

(defthm loghead-of-sum-with-multiple-of-expt-2-size
  (implies (and (integerp j)
                (<= 0 size)
                (integerp size)
                (integerp x)
                )
           (equal (loghead size (+ x (* j (expt 2 size))))
                  (loghead size x))))

(defthm loghead-of-sum-with-multiple-of-expt-2-size-alt
  (implies (and (integerp j)
                (<= 0 size)
                (integerp size)
                (integerp x)
                )
           (equal (loghead size (+ (* j (expt 2 size)) x))
                  (loghead size x))))

(defthm loghead-of-sum-integer-and-non-integer
  (implies (and (integerp size2)
                (not (integerp size1)))
           (equal (loghead (+ size1 size2) i)
                  (if (acl2-numberp size1)
                      (loghead 0 i)
                    (loghead size2 i)))))

;drop?
(defthmd equal-loghead-+-simple
  (implies (and (equal (loghead n x) 0)
                (integerp n)
                (integerp x)
                (integerp y)
                (< 0 n)
                )
           (equal (equal (loghead n (+ x y)) 0)
                  (equal (loghead n y) 0)))
  :hints (("goal" :in-theory (enable loghead*-better open-logcons))))

(defthmd expt2*
  (implies (and (equal x 2)
                (integerp n)
                (<= 0 n))
           (equal (expt x n)
                  (if (equal n 0)
                      1
                    (logcons 0 (expt x (1- n))))))
  :hints (("goal" :in-theory (enable expt ash)))
  :rule-classes :definition)

(in-theory (disable expt))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; lognot
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm signed-byte-p-lognot
  (implies (signed-byte-p size i)
           (signed-byte-p size (lognot i)))
  :rule-classes ((:rewrite)
                 (:forward-chaining :trigger-terms ((lognot i)))))

(defthm lognot-neg
  (implies (integerp a)
           (equal (< (lognot a) 0)
                  (<= 0 a)))
  :hints (("goal" :in-theory (enable lognot))))

(defthm lognot-logior
  (implies (and (integerp x)
                (integerp y))
           (equal (lognot (logior x y))
                  (logand (lognot x) (lognot y))))
  :hints (("goal" :in-theory (enable LRDT logendp))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logand
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm logand-logior-2
  (implies (and (force (integerp i))
                (force (integerp j))
                (force (integerp k)))
           (equal (logand (logior i j) k)
                  (logior (logand i k) (logand j k)))))


(defthmd logand-zip
  (implies (zip a)
           (and (equal (logand a b) 0)
                (equal (logand b a) 0)))
  :hints (("goal" :in-theory (enable logand ifix))))

;; taken from logops-lemmas.lisp, where it's a local theorem
(defthm signed-byte-p-logand
  (implies (and (signed-byte-p size i)
                (signed-byte-p size j))
           (signed-byte-p size (logand i j)))
  :rule-classes ((:forward-chaining :trigger-terms ((logand i j)))))

(defthm logand-neg
  (implies (and (integerp a)
                (integerp b))
           (equal (< (logand a b) 0)
                  (and (< a 0) (< b 0))))
  :hints (("goal" :in-theory (enable logand))))

(defthm ifix-logand
  (equal (ifix (logand x y))
         (logand x y)))


;should 0 really count as a logmaskp?
;bzo add the other commutative form of this rule?
(defthm logand-with-mask-eric
  (implies (logmaskp mask)
           (equal (logand mask i)
                  (loghead (integer-length mask) i)))
  :hints (("Goal" :use (:instance logand-with-mask (size  (INTEGER-LENGTH MASK)))
           :in-theory (e/d () (logand-with-mask)))))

(in-theory (disable logand-with-mask))




;disable the other one?
(defthm my-logextu-as-loghead
  (implies (and ;(FORCE (INTEGERP FINAL-SIZE))
;                (FORCE (>= FINAL-SIZE 0))
                (FORCE (INTEGERP EXT-SIZE))
                (FORCE (>= EXT-SIZE 0))
                (<= final-size ext-size)
                )
           (equal (loghead final-size (logext ext-size i))
                  (loghead final-size i)))
  :hints
  (("Goal" :in-theory (e/d (
;                            LOGHEAD-WITH-SIZE-NON-POSITIVE
                            )
                           (logextu-as-loghead))
    :use  logextu-as-loghead)))

(defthm logand-bit-0
  (implies (unsigned-byte-p 1 x)
           (equal (logand x y)
                  (b-and x (logcar y))))
  :hints (("goal" :in-theory (e/d (LRDT logand-zip) (LOGHEAD* logand*))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

;prove from the other
(defthm logand-bit-1
  (implies (unsigned-byte-p 1 x)
           (equal (logand y x)
                  (b-and x (logcar y))))
  :hints (("goal" :in-theory (e/d (LRDT logand-zip) (LOGHEAD* logand*))))
  :rule-classes ((:rewrite :backchain-limit-lst 1)))

(defthm logand-lognot
  (equal (logand x (lognot x))
         0)
  :hints (("goal" :in-theory (enable LRDT logand-zip logendp))))



;drop or redo?
(defthmd logand-commutative-2-helper
   (implies (and (integerp b)
                 (not (equal b 0))
                 (not (equal b -1))
                 (equal (logand a c) 0)
                 (integerp a)
                 (integerp c))
            (equal (logand a b c)
                   0))
   :hints (("goal" :in-theory (enable LRDT
                                      logendp
                                      even-odd-different-1
                                      even-odd-different-2
                                      ))))



(defthm equal-logand-logcons
  (implies (and (integerp b)
                (integerp x)
                (integerp y)
                (unsigned-byte-p 1 a))
           (equal (equal (logand (logcons a b) x) y)
                  (and (equal (b-and a (logcar x)) (logcar y))
                       (equal (logand b (logcdr x)) (logcdr y)))))
  :hints (("goal" :in-theory (enable LRDT))))


;bzo move
(defthm integer-length-<-1-rewrite
  (equal (< (integer-length n) 1)
         (or (equal n 0)
             (equal n -1)
             (not (integerp n)))
         )
  :hints (("Goal" :in-theory (enable integer-length))))

(defthm logand-expt-constant-version
  (implies (and (syntaxp (quotep n))
                (equal (expt 2 (1- (integer-length n))) n)
                (integerp n))
           (equal (logand n x)
                  (if (logbitp (1- (integer-length n)) x)
                      (expt 2 (1- (integer-length n)))
                    0)))
  :hints (("Goal" :use (:instance logand-expt (n (1- (integer-length n)))))))

;bzo just use logand-expt ?
(defthm equal-logand-expt
  (implies (<= 0 n) ;bzo
           (equal (equal (logand (expt 2 n) x) k)
                  (if (logbitp n x)
                      (equal k (expt 2 n))
                    (equal k 0)))))

;just use logand-expt-constant-version?
(defthm equal-logand-expt-rewrite
  (implies (and (syntaxp (quotep n))
                (equal (expt 2 (1- (integer-length n))) n)
                (integerp n)
                )
           (equal (equal (logand n x) k)
                  (if (logbitp (1- (integer-length n)) x)
                      (equal k n)
                    (equal k 0))))
  :hints (("goal"
           :in-theory (e/d (LRDT) (logand*))
           :use (:instance equal-logand-expt
                           (n (1- (integer-length n)))))))

(defthm logand---expt
  (implies (and (integerp n)
                (<= 0 n)
                (signed-byte-p (1+ n) x))
           (equal (logand (- (expt 2 n)) x)
                  (if (logbitp n x) (- (expt 2 n)) 0)))
  :hints (("goal"
           :in-theory (enable LRDT expt2* ash open-logcons))))

(defthm logand---expt-rewrite
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (equal (- (expt 2 (1- (integer-length (- k))))) k)
                (signed-byte-p (integer-length (- k)) x))
           (equal (logand k x)
                  (if (logbitp (1- (integer-length (- k))) x) k 0)))
  :hints (("goal" :use (:instance logand---expt (n (1- (integer-length (- k))))))))

(defthm equal-0-logand-bit
  (implies (and (unsigned-byte-p 1 x)
                (integerp y))
           (and (equal (equal 0 (logand y x))
                       (or (equal x 0) (equal (logcar y) 0)))
                (equal (equal 0 (logand x y))
                       (or (equal x 0) (equal (logcar y) 0)))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm equal-bit-logand-bit
  (implies (and (integerp y)
                (unsigned-byte-p 1 x))
           (and (equal (equal x (logand y x))
                       (or (equal x 0) (equal (logcar y) 1)))
                (equal (equal x (logand x y))
                       (or (equal x 0) (equal (logcar y) 1)))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logand-logand-const
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b))
                ;(integerp a)
                ;(integerp b)
                ;(integerp c)
                )
           (equal (logand a (logand b c))
                  (logand (logand a b) c))))

(defthm equal-logand-ash-0
  (implies (and (unsigned-byte-p n x)
;                (integerp y)
                (integerp n)
                (<= 0 n)
                )
           (and (equal (logand (ash y n) x) 0)
                (equal (logand x (ash y n)) 0)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logand-bfix
  (and (equal (logand (bfix x) y)
              (b-and (bfix x) (logcar y)))
       (equal (logand y (bfix x))
              (b-and (bfix x) (logcar y)))))

(defthm *ash*-equal-logand-ash-pos-0
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (< 0 n))
           (equal (equal (logand x (ash y n)) 0)
                  (equal (logand (ash x (- n)) y) 0)))
  :hints (("goal" :in-theory (enable LRDT)
           :induct (sub1-logcdr-induction n x))))

(defthm *ash*-equal-logand---expt---expt-helper
  (implies (and (integerp n)
                (integerp x)
                (<= 0 n))
           (equal (equal (- (expt 2 n)) (logand (- (expt 2 n)) x))
                  (equal (ash x (- n)) -1)))
  :rule-classes nil
  :hints (("goal"
           :in-theory (e/d (LRDT expt2*
                                 )
                           (LOGCONS-OF-0
                            )))))

(defthm equal-logand---expt---expt
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (integerp x)
                (equal (- (expt 2 (1- (integer-length (- k))))) k))
           (equal (equal k (logand k x))
                  (equal (ash x (- (1- (integer-length (- k))))) -1)))
  :hints (("goal"
           :use (:instance *ash*-equal-logand---expt---expt-helper
                           (n (1- (integer-length (- k))))))))

(defthm logand---expt-v2
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p (1+ n) x))
           (equal (logand (- (expt 2 n)) x)
                  (if (logbitp n x) (expt 2 n) 0)))
  :hints (("goal" :in-theory (enable LRDT expt2*))))

(defthm logand---expt-rewrite-v2
  (implies (and (syntaxp (quotep k))
                (integerp k)
                (equal (- (expt 2 (1- (integer-length (- k))))) k)
                (unsigned-byte-p (integer-length (- k)) x))
           (equal (logand k x)
                  (if (logbitp (1- (integer-length (- k))) x)
                      (expt 2 (1- (integer-length (- k))))
                    0)))
  :hints (("goal" :use (:instance logand---expt-v2
                                  (n (1- (integer-length (- k))))))))

(defthm equal-logand---expt-0
  (implies (and (integerp n)
                (integerp x)
                (<= 0 n))
           (equal (equal (logand (- (expt 2 n)) x) 0)
                  (unsigned-byte-p n x)))
  :hints (("goal"
           :in-theory (e/d (LRDT)
                           (logand---expt-v2
                            logand---expt-rewrite-v2
                            logand---expt)))))

(defthm equal-logand---expt-0-rewrite
  (implies (and (integerp x)
                (syntaxp (quotep k)) (integerp k)
                (equal (- (expt 2 (1- (integer-length (- k))))) k))
           (equal (equal (logand k x) 0)
                  (unsigned-byte-p (1- (integer-length (- k))) x)))
  :hints (("goal" :use (:instance equal-logand---expt-0
                                  (n (1- (integer-length (- k))))))))

;see from-rtl.lisp for more stuff about logand (and perhaps other functions...)

(defthm logand-lognot-1
  (equal (logand x (lognot x) y)
         0)
  :hints (("goal" :use ((:instance logand-associative
                                   (i x)
                                   (j (lognot x))
                                   (k y))))))
(defthm logand-duplicate-1
  (equal (logand x x y)
         (logand x y))
  :hints (("Goal" :in-theory (e/d (LOGAND-ZIP)
                                  (logand
                                   COMMUTATIVITY-OF-LOGAND
                                   logand-associative))
           :use (:instance logand-associative
                           (i x)
                           (j x)
                           (k y)))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logior
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm ifix-logior
  (equal (ifix (logior x y))
         (logior x y)))

(defthm signed-byte-p-logior
  (implies (and (signed-byte-p size i)
                (signed-byte-p size j))
           (signed-byte-p size (logior i j)))
  :rule-classes ((:forward-chaining :trigger-terms ((logior i j)))))

(defthm logior-as-b-ior
  (implies (and (unsigned-byte-p 1 x)
                (unsigned-byte-p 1 y))
           (equal (logior x y) (b-ior x y)))
  :hints (("goal" :in-theory (enable LRDT
                                      )))
  :rule-classes ((:rewrite :backchain-limit-lst 2)))

(defthm logcons-0-expt-hack
  (implies (and(integerp n)
               (<= 0 n))
           (equal (logcons 0 (expt 2 n))
                  (expt 2 (+ 1 n)))))

(defthm twice-logcdr-hack
  (equal (equal (* 2 (logcdr x)) x)
         (if  (integerp x)
             (evenp x)
           (equal 0 x))))

(defthm logbitp-of-logcdr
  (implies (and (integerp n)
                (<= 0 n)
                )
           (equal (logbitp n (logcdr y))
                  (logbitp (+ 1 n) y)))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logbitp
                            logcdr
                            exponents-add-unrestricted)
                           (FLOOR-OF-SHIFT-RIGHT-2)))))

;similarly for logtail?
;drop the hyps the way i did for logbitp-of-logcdr2?
(defthm logbit-of-logcdr
  (implies (and (integerp n) (<= 0 n))
           (equal (logbit n (logcdr y))
                  (logbit (+ 1 n) y)))
  :hints (("Goal" :in-theory (enable logbit))))


(defthm logbitp-of-logcdr2
  (equal (logbitp n (logcdr y))
         (if (and (integerp n)
                  (<= 0 n))
             (logbitp (+ 1 n) y)
           (logbitp 0 (logcdr y)) ;simplify this?
           ))
  :hints (("Goal" :use (:instance  logbitp-of-logcdr)
           :in-theory (disable  logbitp-of-logcdr))))

;bzo speed this up?
;trying to improve the proof of this and in the process discover new rules
;gross proof!
(defthm equal-logior-single-bit
  (implies (and (syntaxp (quotep x))
                (equal (expt 2 (1- (integer-length x))) x) ;x is a power of 2
                (integerp x)
                (integerp y)
                (integerp z)
                (< 0 x)
                )
           (equal (equal (logior y z) x)
                  (and (logbitp (1- (integer-length x)) (logior y z))
                       (equal 0 (logand (lognot x) (logior y z))))))
  :hints (("goal"
           :do-not '(;generalize eliminate-destructors
                      ;          fertilize ;bzo. why didn't it fertilize completely?
                                )
           :in-theory (e/d (LRDT
                              even-odd-different-2
                              even-odd-different-1
                              expt2*
                              EQUAL-B-NOT-LOGCAR
                              ;ash
                              )
                           (integer-length*
                            LOGCONS-OF-0
                            ))
           :induct (logcdr-logcdr-logcdr-induction x y z))))

(defthm logior-logior-const
  (implies (and (syntaxp (quotep a))
                (syntaxp (quotep b))
                ;(integerp a)
                ;(integerp b)
                ;(integerp c)
                )
           (equal (logior a (logior b c))
                  (logior (logior a b) c))))

;Trying disabled, since this looked expensive... -ews
(defthmd equal-logior-const-const
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep z))
                (integerp x)
                (integerp y)
                (integerp z)
                (not (equal x 0)) (not (equal x -1)))
           (equal (equal (logior x y) z)
                  (and (equal (b-ior (logcar x) (logcar y)) (logcar z))
                       (equal (logior (logcdr x) (logcdr y)) (logcdr z)))))
  :hints (("goal" :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
           :induct (logcdr-logcdr-logcdr-induction z x y))))

(defthmd equal-logior-*2
  (implies (and (integerp x)
                (integerp y)
                (integerp z))
           (equal (equal (logior x y) (* 2 z))
                  (and (equal (logcar x) 0)
                       (equal (logcar y) 0)
                       (equal (logior (logcdr x) (logcdr y)) z))))
  :hints (("goal" :in-theory (enable LRDT))))

;; The follow bridge lemmas are needed for the PC calculation
(defthm logior-expt-ash-loghead-bridge-helper
  (implies (and (integerp n)
                (integerp x)
                (integerp m)
                (< 0 n)
                (<= 0 m))
           (equal (logior (expt 2 (1- n))
                          (ash (loghead m (logcdr x)) n))
                  (if (equal (logcar x) 0)
                      (ash (loghead (1+ m) (1+ x)) (1- n))
                    (ash (loghead (1+ m) x) (1- n)))))
  :rule-classes nil
  :hints (("goal"
           :in-theory (e/d (LRDT loghead* equal-logior-*2) (LOGHEAD-SUM-SPLIT-INTO-2-WHEN-I-IS-A-CONSTANT
                                                            LOGCONS-OF-0))
           :induct (sub1-induction n))))

(defthmd logior-expt-ash-loghead-bridge
  (implies (and (integerp x)
                (integerp m)
                (integerp v)
                (<= 0 m)
                (<= 0 n)
                (equal v (expt 2 (1- (integer-length v))))
                (equal n (integer-length v)))
           (equal (logior v (ash (loghead m (logcdr x)) n))
                  (if (equal (logcar x) 0)
                      (ash (loghead (1+ m) (1+ x)) (1- n))
                    (ash (loghead (1+ m) x) (1- n)))))
  :hints (("goal" :use (:instance logior-expt-ash-loghead-bridge-helper
                                  (n (integer-length v))))))

(defthm logior-expt-ash-loghead-bridge-bridge
  (implies (and (syntaxp (quotep v))
                (integerp x)
                (integerp m)
                (integerp v)
                (integerp a)
                (<= 0 m)
                (<= 0 n)
                (equal v (expt 2 (1- (integer-length v))))
                (equal n (integer-length v)))
           (equal (logior v (logior a (ash (loghead m (logcdr x)) n)))
                  (if (equal (logcar x) 0)
                      (logior a (ash (loghead (1+ m) (1+ x)) (1- n)))
                    (logior a (ash (loghead (1+ m) x) (1- n))))))
  :hints (("goal" :in-theory (enable logior-expt-ash-loghead-bridge))))

;; logior-as-+ - not part of our strategy, but useful for proving rules!
(defthmd logior-as-+
  (implies (and (integerp b)
                (integerp c)
                (equal (logand b c) 0))
           (equal (logior b c) (+ b c)))
  :hints (("goal" :in-theory (e/d (LRDT logendp open-logcons) (LOGCONS-OF-0)))))

;; push a + into a logior if the logior args don't overlap

(defthm +-logior-ash
  (implies (and (integerp v)
                (integerp x)
                (integerp n)
                (<= 0 n)
                (<= 0 x)
                (unsigned-byte-p n a)
                (unsigned-byte-p n (+ v a)))
           (equal (+ v (logior a (ash x n)))
                  (logior (+ v a) (ash x n))))
  :hints (("goal" :in-theory (enable logior-as-+))))



;bzo gross subgoal hint
(defthm +-logior-ash-v2
  (implies (and (integerp v)
                (integerp x)
                (integerp n)
                (< 0 n)
                (<= 0 x)
                (unsigned-byte-p n a)
                (unsigned-byte-p n v)
                (not (unsigned-byte-p n (+ v a))))
           (equal (+ v (logior a (ash x n)))
                  (logior (loghead n (+ v a))
                          (ash (1+ x) n))))
  :hints (("goal" :in-theory (e/d (logior-as-+
;                                   ash-+-pos
                                   LOGHEAD-ALMOST
                                   )
                                  ( UNSIGNED-BYTE-P-+-EASY
                                   UNSIGNED-BYTE-P-+)))
          ("goal''" :in-theory (e/d (ash-+-pos
                                     LOGHEAD-ALMOST
                                     )
                                    ( UNSIGNED-BYTE-P-+)))))




(defthm logior-lognot
  (equal (logior x (lognot x))
         -1)
  :hints (("goal"
           :in-theory (enable LRDT logendp))))

(defthm logor-lognot-1
  (implies (and (integerp x)
                (integerp y))
  (equal (logior x (lognot x) y) -1))
  :hints (("goal" :use ((:instance logior-associative
                                   (i x)
                                   (j (lognot x))
                                   (k y))))))

(defthm logior-duplicate
  (equal (logior x x)
         (ifix x))
  :hints (("goal"
           :induct (logcdr-induction x)
           :in-theory (enable LRDT zip
                              ))))

;add to rtl library?
(defthm logior-duplicate-1
  (equal (logior x x y)
         (logior x y))
  :hints (("goal"
           :in-theory (e/d () ( logior-associative))
           :use ((:instance logior-associative
                            (i x)
                            (j x)
                            (k y))))))

;; ;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; ;; logxor
;; ;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

;; ;; These are Wilding lemmas that seem general-purpose

;; (defthm signed-byte-p-logxor
;;   (implies (and (signed-byte-p size i)
;;                 (signed-byte-p size j))
;;            (signed-byte-p size (logxor i j)))
;;   :rule-classes ((:rewrite)
;;                  (:forward-chaining :trigger-terms ((logxor i j)))))

;; ;; moved to logcar
;; ;; (defthm logcar-logxor
;; ;;   (implies (and (integerp a)
;; ;;                 (integerp b))
;; ;;            (equal (logcar (logxor a b))
;; ;;                   (b-xor (logcar a) (logcar b))))
;; ;;   :hints (("goal" :in-theory (enable
;; ;;                               LOGOPS-RECURSIVE-DEFINITIONS-THEORY
;; ;;                               simplify-bit-functions))))

;; (defthm logxor-lognot
;;   (implies (and (integerp a)
;;                 (integerp b))
;;            (and (equal (logxor (lognot a) b) (lognot (logxor a b)))
;;                 (equal (logxor a (lognot b)) (lognot (logxor a b)))))
;;   :hints (("goal"
;;            :in-theory (enable LRDT simplify-bit-functions))))



;; (defthm logxor-cancel2
;;   (implies (and (integerp a)
;;                 (integerp b))
;;            (equal (logxor b (logxor b a)) a))
;;   :hints (("goal" :use (:instance commutativity-of-logxor
;;                                   (i b) (j (logxor b a))))))

;; (defthm logxor-neg
;;   (implies (and (integerp a)
;;                 (integerp b))
;;            (equal (< (logxor a b) 0)
;;                   (not (equal (< a 0) (< b 0)))))
;;   :hints (("goal" :in-theory (enable logxor logeqv logorc1))))

;; ;; Perhaps we should just open logxor.  But for now, we'll open it
;; ;; only when used in conjuction with logical bit-operations.
;; (defthm logxor-open
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (equal (logxor x y)
;;                   (logior (logand x (lognot y))
;;                           (logand (lognot x) y))))
;;   :hints (("goal" :in-theory (enable LRDT))))
;;            ;; :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY)
;; ;;            :induct (logcdr-logcdr-induction x y))))

;; (in-theory (disable logxor-open))

;; (defthm logior-logxor
;;   (implies (and (integerp x)
;;                 (integerp y))
;;            (and
;;             (equal (logior z (logxor x y))
;;                    (logior z
;;                            (logior (logand x (lognot y))
;;                                    (logand (lognot x) y))))
;;             (equal (logior (logxor x y) z)
;;                    (logior (logior (logand x (lognot y))
;;                                    (logand (lognot x) y))
;;                            z))))
;;   :hints (("goal" :in-theory (enable logxor-open))))

;; (defthm logxor-logior
;;   (implies (and (integerp x)
;;                 (integerp y)
;;                 (integerp z))
;;            (and (equal (logxor (logior x y) z)
;;                        (logior (logand (logior x y) (lognot z))
;;                                (logand (lognot (logior x y)) z)))
;;                 (equal (logxor z (logior x y))
;;                        (logior (logand (logior x y) (lognot z))
;;                                (logand (lognot (logior x y)) z)))))
;;   :hints (("goal" :in-theory (enable logxor-open))))


;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; get rid of logops other than logand, logior, and lognot
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm lognot-logand
 (implies (and (integerp x)
               (integerp y))
          (equal (lognot (logand x y))
                 (logior (lognot x) (lognot y))))
 :hints (("goal" :in-theory (enable LRDT logendp))))
          ;; :induct (logcdr-logcdr-induction x y)
;;            :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY))))

(defthm lognand-rewrite
 (implies (and (integerp x)
               (integerp y))
          (equal (lognand x y)
                 (logior (lognot x) (lognot y))))
 :hints (("goal" :in-theory (enable lognand))))

(defthm lognor-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (lognor x y)
                  (logand (lognot x) (lognot y))))
  :hints (("goal" :in-theory (enable lognor))))

(in-theory (enable logandc1 logandc2 logorc1 logorc2))

(defthm logeqv-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (logeqv x y)
                  (logior (logand x y)
                          (logand (lognot x) (lognot y)))))
  :hints (("goal" :in-theory (enable logeqv))))

(defthm logxor-rewrite
  (implies (and (integerp x)
                (integerp y))
           (equal (logxor x y)
                  (logior (logand x (lognot y))
                          (logand (lognot x) y))))
   :hints (("goal" :in-theory (enable logeqv logxor))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; and similarly for binary operations:
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


(defthm logand-upper-bound-eric
  (implies (<= 0 i)
           (<= (logand i j) i))
  :hints (("Goal" :cases ((integerp j))))
  :rule-classes
  ((:linear :corollary
            (implies (and (>= i 0))
                     (<= (logand i j) i)))
   (:linear :corollary
            (implies (and (>= i 0))
                     (<= (logand j i) i)))))

(in-theory (disable logand-upper-bound))

(defthm equal-logapp-x-y-z-constants
  (implies (and (syntaxp (quotep z))
                (syntaxp (quotep n)))
           (equal (equal (logapp n x y) z)
                  (and (integerp z)
                       (if (integerp x)
                           (equal (loghead n x) (loghead n z))
                         (equal (ash y (nfix n)) z))
                       (if (integerp y)
                           (equal y (logtail n z))
                         (equal z (loghead n x))))))
  :hints (("Goal" :in-theory (enable equal-logapp-x-y-z))))

(defthm logapp-logior
  (implies (and (integerp w)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp n)
                (<= 0 n))
           (equal (logapp n (logior w y) (logior x z))
                  (logior (logapp n w x) (logapp n y z))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logapp-logand
  (implies (and (integerp w)
                (integerp x)
                (integerp y)
                (integerp z)
                (integerp n)
                (<= 0 n))
           (equal (logapp n (logand w y) (logand x z))
                  (logand (logapp n w x) (logapp n y z))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logapp-lognot
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n))
           (equal (logapp n (lognot x) (lognot y))
                  (lognot (logapp n x y))))
  :hints (("goal" :in-theory (enable LRDT))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; loghead
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


(defthm loghead-subsumes-+-logext
  (implies (and (< n m)
                (integerp n)
                (integerp m)
                (integerp x)
                (integerp a)
                (< 0 m)
                (<= 0 n)
                )
           (equal (loghead n (+ a (logext m x)))
                  (loghead n (+ a x)))))

(defthm loghead-logior
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (<= 0 n))
           (equal (loghead n (logior x y))
                  (logior (loghead n x) (loghead n y))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm loghead-logand
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (<= 0 n))
           (equal (loghead n (logand x y))
                  (logand (loghead n x) (loghead n y))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm loghead-ash-pos-rewrite
  (implies (and (integerp n2)
                (<= 0 n2))
           (equal (loghead n1 (ash x n2))
                  (if (or (<= n1 n2)
                          (not (integerp n1)))
                      0
                    (ash (loghead (- n1 n2) x) n2))))
  :hints (("goal" :in-theory (e/d (loghead*-better ash* LRDT
                                                   zp
                                                   )
                                  ( ;LOGHEAD-OF-*-EXPT-ALT
                                   )))))



(defthm loghead-*4
  (implies (and (integerp n)
                (integerp x)
                (< 0 n))
           (equal (loghead n (* 4 x))
                  (logcons 0 (loghead (1- n) (logcdr (* 4 x))))))
  :hints (("goal" :in-theory (enable loghead*)
           :use (:instance loghead* (size n) (i (* 4 x))))))

(defthm loghead-+-logior
  (implies (and (equal (loghead n y) 0)
                (integerp y)
                (integerp x)
                (integerp n)
                (<= 0 n)
                (integerp a))
           (equal (loghead n (+ a (logior x y)))
                  (loghead n (+ a x)))))

(defthm equal-loghead-ash-pos
  (implies (and (integerp n)
                (integerp m)
                (integerp y)
                (integerp x)
                (integerp p)
                (<= 0 p)
                (<= p n))
           (equal (equal (loghead n x) (ash (loghead m y) p))
                  (and (equal (loghead p x) 0)
                       (equal (logtail p (loghead n x)) (loghead m y)))))
  :hints (("goal" :in-theory (e/d (LRDT) (ash* ;change for acl2 3.0
                                          )))))

;; ;move to loghead.lisp
;; ;trying disabled
;; (defthmd loghead-almost
;;   (implies (and (not (unsigned-byte-p n x))
;;                 (unsigned-byte-p (1+ n) x)
;;                 )
;;            (equal (loghead n x)
;;                   (if (integerp n)
;;                       (- x (ash 1 n)) ;use expt here?
;;                     0
;;                     )))
;;   :hints (("goal" :in-theory (e/d (LRDT open-logcons
;;                                         ) (evenp-of-logcons
;;                                         expt-2-cruncher)))))



(defthm loghead-+-logext
  (implies (and (integerp n)
                (integerp m)
                (integerp x)
                (integerp y)
                (< 0 n)
                (<= n m))
           (and (equal (loghead n (+ (logext m x) y))
                       (loghead n (+ x y)))
                (equal (loghead n (+ x (logext m y)))
                       (loghead n (+ x y)))
                (implies (integerp z)
                         (equal (loghead n (+ x (logext m z) y))
                                (loghead n (+ x y z))))
                (implies (integerp z)
                         (equal (loghead n (+ x y (logext m z)))
                                (loghead n (+ x y z))))))
  :hints (("goal" :use ((:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m x) y)))
                        (:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m y) z)))
                        (:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m x) y z)))
                        (:instance logextu-as-loghead (final-size n) (ext-size m) (i (+ (logext m z) y x)))))))

;move
(defthm equal-loghead-almost-0-helper
  (implies (and (unsigned-byte-p (+ 1 n) x)
                (integerp n)
                (< 0 n)
                )
           (equal (equal (loghead n x) 0)
                  (or (equal x (expt 2 n))
                      (equal x 0))))
  :rule-classes nil
  :hints (("goal"
           :induct (loghead n x)
           :expand (logcdr x)
           :in-theory (e/d (lrdt expt ;logcdr
                                 )
                           (unsigned-byte-p-of-logcdr ;why was this necessary?
                            LOGCAR-0-REWRITE
                            )))))

(defthm equal-loghead-almost-0
  (implies (and (unsigned-byte-p n x)
                (unsigned-byte-p n y)
;                (integerp n)
                (< 0 n)
                )
           (equal (equal (loghead n (+ x y)) 0)
                  (or (equal (+ x y) (expt 2 n))
                      (and (equal x 0) (equal y 0)))))
  :hints (("goal" :use (:instance equal-loghead-almost-0-helper (x (+ x y))))))

(local (in-theory (disable UNSIGNED-BYTE-P-OF-LOGCDR))) ;this doesn't play well with LRDT

(defthm equal-loghead-lognot-all-ones
  (implies (and (integerp n)
                (integerp x)
                (<= 0 n))
           (equal (equal (loghead n (lognot x)) (1- (expt 2 n)))
                  (equal (loghead n x) 0)))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm loghead-lognot-in-+
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p n x))
           (and (equal (+ (loghead n (lognot x)) y)
                       (+ (- (expt 2 n) (1+ x)) y))
                (equal (+ y (loghead n (lognot x)))
                       (+ y (- (expt 2 n) (1+ x))))
                (equal (+ y z (loghead n (lognot x)))
                       (+ y z (- (expt 2 n) (1+ x))))))
  :hints (("goal" :in-theory (enable lognot loghead unsigned-byte-p nfix))))

(defthm equal-loghead-0-sbp
  (implies (and (signed-byte-p n x)
;                (integerp n)
        ;        (<= 0 n)
                )
           (equal (equal (loghead n x) 0)
                  (equal x 0)))
  :hints (("goal" :in-theory (enable LRDT))))



(defthm equal-loghead-0-sbp-v2
  (implies (and (signed-byte-p (1+ n) x)
                (integerp n))
           (equal (equal (loghead n x) 0)
                  (or (equal x 0)
                      (equal x (- (expt 2 n))))))
  :hints (("goal" :in-theory (e/d (LRDT expt ash) (loghead-of-minus
                                                   LOGCAR-0-REWRITE)))))

(defthm loghead-neg-logext
  (implies (and (integerp n)
                (<= 0 n)
                (unsigned-byte-p n x))
           (equal (loghead n (- (logext n x)))
                  (loghead n (- x))))
  :hints (("goal" :in-theory (e/d (LRDT open-logcons) (LOGEXTU-AS-LOGHEAD ;forcing
                                                       LOGHEAD-OF-MINUS
                                                       )))))

(defthm loghead-logxor
  (implies (and (integerp n)
                (integerp x)
                (integerp y)
                (<= 0 n))
           (equal (loghead n (logxor x y))
                  (logxor (loghead n x) (loghead n y))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm loghead-lognot-loghead
  (implies (and (integerp n1)
                (integerp n2)
                (integerp x)
                (<= n1 n2)
                (<= 0 n1))
           (equal (loghead n1 (lognot (loghead n2 x)))
                  (loghead n1 (lognot x))))
  :hints (("goal"
           :in-theory (e/d (LRDT logendp) (LOGHEAD-OF-MINUS
                                           )))))
           ;:induct (sub1-sub1-logcdr-induction n2 n1 x))))

(defthm loghead-lognot-ash-pos
  (implies (and (integerp x)
                (integerp n)
                (integerp p)
                (<= 0 p)
                (<= p n))
           (equal (loghead p (lognot (ash x n)))
                  (loghead p -1)))
  :hints (("goal"
           :in-theory (enable LRDT))))
           ;; :induct (sub1-sub1-induction p n)

(local (in-theory (disable LOGCONS-OF-0))) ;for acl2 3.0

(defthm loghead-lognot-ash-pos-logext
  (implies (and (integerp x)
                (integerp n)
                (integerp p)
                (integerp m)
                (<= 0 m)
                (<= 0 p)
                (< 0 n)
                (<= p (+ m n)))
           (equal (loghead p (lognot (ash (logext n x) m)))
                  (loghead p (lognot (ash x m)))))
  :hints (("goal" :in-theory (enable LRDT))))
           ;; :induct (sub1-sub1-induction p m))))

;we already have ash-as-logtail
(defthm loghead-ash-neg
  (implies (and (<= n2 0)
                (integerp n2) ;drop?
                )
           (equal (loghead n1 (ash x n2))
                  (loghead n1 (logtail (- n2) x))))
  :hints (("goal" :use ((:instance ash-as-logtail
                                   (n n2))))))

(defthm loghead-logapp-better
  (implies (<= size1 size)
           (equal (loghead size1 (logapp size i j))
                  (if (integerp size)
                      (loghead size1 i) ;usual case
                    (loghead size1 j)
                    )))
  :hints (("Goal" :use (:instance loghead-logapp (size (ifix size)))
           :in-theory (disable loghead-logapp))))

(in-theory (disable loghead-logapp))

(defthmd logtail-loghead-better
  (equal (logtail size1 (loghead size i))
         (loghead (max 0 (- size (nfix size1)))
                  (logtail size1 i)))
  :hints (("Goal" :use (:instance logtail-loghead)
           :in-theory (disable logtail-loghead))))

(in-theory (disable logtail-loghead))

(defthm loghead-logtail
  (equal (loghead i (logtail j x))
         (logtail j (loghead (+ i (nfix j)) x)))
  :hints (("Goal" :in-theory (enable logtail-loghead-better))))

;It's not clear whether we want to bring the loghead or the logtail inside.
;I'm trying things out with the policy of bringing the loghead inside. -ews

(defthm logtail-logapp-better
  (implies (and (integerp size1)
                (<= 0 size1)
                (integerp size)
                (<= 0 size)
                )
           (equal (logtail size (logapp size1 i j))
                  (if (< size size1)
                      (logapp (- size1 size)
                              (logtail size i)
                              j)
                    (logtail (- size size1)
                             j))))
  :hints (("Goal" :use (:instance logtail-logapp)
           :in-theory (disable logtail-logapp))))

(in-theory (disable logtail-logapp))

;move to logapp.lisp?
(defthm associativity-of-logapp-better
  (implies (and (integerp size1)
                (<= 0 size1)
                (integerp size)
                (<= 0 size)
                )
           (equal (logapp size i (logapp size1 j k))
                  (logapp (+ size size1) (logapp size i j) k)))
  :hints (("Goal" :use (:instance associativity-of-logapp)
           :in-theory (disable associativity-of-logapp))))

(in-theory (disable associativity-of-logapp))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logtail
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;

(defthm logtail-logior
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n))
           (equal (logtail n (logior x y))
                  (logior (logtail n x) (logtail n y))))
  :hints (("goal"
           :in-theory (disable logapp-logior)
           :use ((:instance logapp-logior
                            (w (loghead n x))
                            (x (logtail n x))
                            (y (loghead n y))
                            (z (logtail n y)))))))

(defthm logtail-logand
  (implies (and (integerp x)
                (integerp y)
                (integerp n)
                (<= 0 n))
           (equal (logtail n (logand x y))
                  (logand (logtail n x) (logtail n y))))
  :hints (("goal"
           :in-theory (disable logapp-logand)
           :use ((:instance logapp-logand
                            (w (loghead n x))
                            (x (logtail n x))
                            (y (loghead n y))
                            (z (logtail n y)))))))

(defthm logtail-lognot
  (implies (and (integerp x)
                (integerp n)
                (<= 0 n))
           (equal (logtail n (lognot x))
                  (lognot (logtail n x))))
  :hints (("goal"
           :in-theory (disable logapp-lognot)
           :use ((:instance logapp-lognot
                            (x (loghead n x))
                            (y (logtail n x)))))))

(defthm logcar-lognot
  (equal (logcar (lognot a))
         (b-not (logcar a)))
  :hints (("Goal" :in-theory (enable  logops-recursive-definitions-theory))))

(defthm logcar-logand
  (equal (logcar (logand a b))
         (b-and (logcar a) (logcar b)))
  :hints (("goal" :in-theory (enable logops-recursive-definitions-theory)
           :use (:instance logand* (i a) (j b)))))

(defthm logcar-logior
  (equal (logcar (logior a b))
         (b-ior (logcar a) (logcar b)))
  :hints (("goal"
           :in-theory (enable logior logops-recursive-definitions-theory))))

;move 3rd hyp to conclusion?
(defthm logcar-logext
  (implies (and (integerp n)
                (integerp x)
                (< 0 n))
           (equal (logcar (logext n x))
                  (logcar x)))
  :hints (("goal" :in-theory (enable logext logbitp oddp; evenp
                                     ))))


(defthm logcar-ash-neg
  (implies (and (<= n 0)
                (integerp n)
        ;        (integerp x)
                )
           (equal (logcar (ash x n))
                  (logbit (- n) x)))
  :hints (("goal" :in-theory (e/d (LRDT logbit) (logtail* ;was forcing
                                                 )))))

(defthm logcar-ash-both
  (implies (integerp n)
           (equal (logcar (ash x n))
                  (if (< 0 n)
                      0
                    (logbit (- n) x))))
  :hints (("Goal" :in-theory (disable ASH-AS-LOGTAIL))))

(defthm logcar-logtail
  (implies (and ;(integerp x)
                (integerp n)
                (<= 0 n)
                )
           (equal (logcar (logtail n x))
                  (logbit n x)))
  :hints (("goal" :in-theory (e/d (LRDT
                                     logbit) (logtail*)))))


;; (defthm logcar-+-carry-bit
;;  (implies (and (integerp a)
;;                (integerp b)
;;                (unsigned-byte-p 1 c))
;;           (equal (logcar (+ a b c))
;;                  (b-xor (logcar a) (b-xor (logcar b) c)))))

;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;
;; logcdr
;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;-;


;move this stuff?


;do we need this?
(defthm unsigned-byte-p-logcdr-fc
  (implies (and (unsigned-byte-p n x)
                (integerp n)
                (< 0 n))
           (unsigned-byte-p (1- n) (logcdr x)))
  :rule-classes ((:forward-chaining :trigger-terms ((logcdr x)))))

(defthm signed-byte-p-of-logcdr
  (equal (signed-byte-p n (logcdr x))
         (and (< 0 n)
              (integerp n)
              (if (integerp x)
                  (signed-byte-p (1+ n) x)
                t)))
  :hints (("goal"
           :cases ((evenp x))
           :in-theory (e/d (logcdr
                            signed-byte-p
                            expt
                            )
                           (expt-2-cruncher
                            FLOOR-OF-SHIFT-RIGHT-2
                            )))))

;do we need this?
(defthm signed-byte-p-logcdr-fc
  (implies (and (signed-byte-p n x)
                (integerp n)
                (< 1 n))
           (signed-byte-p (1- n) (logcdr x)))
  :rule-classes ((:forward-chaining :trigger-terms ((logcdr x)))))

;see LOGCDR-EVENP-*
(defthmd *ark*-logcdr-*4
  (implies (integerp x)
           (equal (logcdr (* 4 x))
                  (* 2 x)))
  :hints (("goal" :in-theory (enable logcdr))))


(defthm logcdr-logcar
  (equal (logcdr (logcar x))
         0)
  :hints (("goal" :in-theory (enable logcdr logcar))))


;move some of this stuff to logcdr

;split into several rules
;mixes logcdr and logcar
(defthm logcdr-+1
  (implies (integerp x)
           (and (implies (equal (logcar x) 0)
                         (equal (logcdr (+ 1 x))
                                (logcdr x)))
                (implies (equal (logcar x) 1)
                         (equal (logcdr (+ 1 x))
                                (+ 1 (logcdr x))))
                (implies (and (integerp y)
                              (equal (logcar x) 1))
                         (equal (logcdr (+ 1 x y))
                                (+ 1 (logcdr x) (logcdr y))))
                (implies (and (integerp y)
                              (equal (logcar x) 1))
                         (equal (logcdr (+ 1 y x))
                                (+ 1 (logcdr x) (logcdr y))))))
  :hints (("Goal" :in-theory (enable logcons))))

(defthm logcdr-+3
  (and (implies (and (integerp x)
                     (equal (logcar x) 0))
                (equal (logcdr (+ 3 x))
                       (+ 1 (logcdr x))))
       (implies (and (integerp x)
                     (equal (logcar x) 1))
                (equal (logcdr (+ 3 x))
                       (+ 2 (logcdr x)))))
  :hints (("goal" :in-theory (enable logcar logcdr))))

(defthm logcdr-loghead
  (implies (< 0 n)
           (equal (logcdr (loghead n x))
                  (loghead (1- n) (logcdr x))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logcdr-logext
  (implies (and (integerp n)
                ;(integerp x)
                (< 1 n))
           (equal (logcdr (logext n x))
                  (logext (1- n) (logcdr x))))
  :hints (("goal" :in-theory (enable LRDT))))

(defthm logcdr-bitop
  (and (equal (logcdr (b-and x y)) 0)
       (equal (logcdr (b-ior x y)) 0)
       (equal (logcdr (b-xor x y)) 0)
       (equal (logcdr (b-not x)) 0))
  :hints (("goal" :in-theory (enable logcdr b-and b-ior b-xor b-not))))

(defthm equal-logcdr-constant-bridge
  (implies (and (syntaxp (quotep x))
                (not (equal (logcar y) 0))
                (integerp x)
                (integerp y)
                )
           (equal (equal (logcdr y) x)
                  (equal y (1+ (* 2 x))))))



;; ;doing more harm than good?
;; (defthm logcdr-+
;;   (implies (and (integerp a)
;;                 (integerp b))
;;            (equal (logcdr (+ a b))
;;                   (+ (logcdr a)
;;                      (logcdr b)
;;                      (b-maj (logcar a) (logcar b) 0)))))

;; (defthm logcdr-+-carry-bit
;;   (implies (and (integerp a)
;;                 (integerp b)
;;                 (unsigned-byte-p 1 c))
;;            (equal (logcdr (+ a b c))
;;                   (+ (logcdr a)
;;                      (logcdr b)
;;                      (b-maj (logcar a) (logcar b) c)))))

(in-theory (disable logtail))

(defthm logtail-when-i-is-zero
  (equal (logtail pos 0)
         0)
  :hints (("Goal" :in-theory (enable logtail))))

(in-theory (disable logtail-size-0))

(defthm logtail-when-i-is-not-an-integerp
  (implies (not (integerp i))
           (equal (logtail pos i)
                  0))
  :hints
  (("Goal" :in-theory (enable logtail))))

(defthm logtail-when-pos-is-not-positive
  (implies (<= pos 0)
           (equal (logtail pos i)
                  (ifix i)
                  ))
  :hints (("Goal" :in-theory (enable logtail))))

(defthmd logtail-when-pos-is-not-positive-no-split
  (implies (and (<= pos 0)
                (integerp i))
           (equal (logtail pos i)
                  i))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-when-pos-is-not-an-integerp
  (implies (not (integerp pos))
           (equal (logtail pos i)
                  (ifix i)
                  ))
  :hints (("Goal" :in-theory (enable logtail))))

(defthm logtail-1
  (equal (logtail 1 x)
         (logcdr x))
  :hints (("goal" :in-theory (enable logtail logcons))))


(defthm logtail--1
  (equal (logtail n -1)
         -1)
  :hints (("Goal" :in-theory (enable logtail))))

(defthm ash-as-logtail
  (implies (<= n 0)
           (equal (ash x n)
                  (logtail (- n) x)))
  :hints (("goal" :in-theory (enable logtail ash))))

(defthm logtail-of-logcdr
  (implies (and (integerp n)
                (<= 0 n))
           (equal (logtail n (logcdr i))
                  (logtail (+ 1 n) i)))
  :hints (("Goal" :in-theory (e/d (logtail logcdr ifloor ) (floor-of-shift-right-2)))))

(defthm logcdr-of-logtail
  (implies (and (<= 0 n)
                (integerp n))
           (equal (logcdr (logtail n i))
                  (logtail (+ 1 n) i)))
  :hints (("Goal" :in-theory (e/d (logtail logcdr ifloor ) (floor-of-shift-right-2)))))

(defthmd logtail*-better
  (equal (logtail pos i)
         (cond ((< (ifix pos) 0)  (ifix i))
               ((equal (ifix pos) 0) (ifix i))
               (t (logtail (1- pos) (logcdr i)))))
  :rule-classes
  ((:definition :clique (logtail)
                :controller-alist ((logtail t t))))
  :hints (("Goal" :use (:instance logtail*))))

(in-theory (disable logtail*))

;the ifix was causing case splits
(defthm logtail-0-i-better
  (equal (logtail 0 i)
         (ifix i)))

(defthmd logtail-0-i-better-no-split
  (implies (integerp i)
           (equal (logtail 0 i)
                  i)))

(in-theory (disable logtail-0-i))

;dup
(defun sub1-sub1-induction (m n)
  (if (zp m)
      n
    (sub1-sub1-induction (1- m) (1- n))))

(defthm logtail-*-expt-v2
  (implies (and (integerp n)
                (integerp n2)
                (integerp x)
                (integerp y)
                (<= 0 n)
                (<= 0 n2))
           (equal (logtail n (* x y (expt 2 n2)))
                  (if (< n n2)
                      (* x y (expt 2 (- n2 n)))
                    (logtail (- n n2) (* x y)))))
  :hints (("goal" :use (:instance logtail-*-expt (x (* x y))))))



(defthm logtail-logtail-better
  (implies (and (>= pos1 0)
                (integerp pos1)
                (integerp pos)
                (>= pos 0)
                )
           (equal (logtail pos1 (logtail pos i))
                  (logtail (+ pos pos1)
                           i)))
  :hints (("Goal" :use (:instance logtail-logtail)
           :in-theory (disable logtail-logtail))))

(in-theory (disable LOGTAIL-LOGTAIL))

(in-theory (disable lshu))

(defthm integerp-lshu
  (integerp (lshu size i x)))

(defthm lshu-bound
  (and (<= 0 (lshu 32 i x))
       (<= (lshu 32 i x) (1- (expt 2 32))))
  :hints (("goal" :in-theory (enable lshu)))
  :rule-classes :linear)

(defthmd lshu-bound-rewrite-1
  (implies (and (<= (expt 2 n) bound)
                (integerp n)
                (<= 0 n))
           (<= (lshu n x s) bound))
  :hints (("goal" :use (:instance unsigned-byte-p-lshu
                                  (size n) (size1 n)
                                  (i x) (cnt s))
           :in-theory (disable unsigned-byte-p-lshu)))
  :rule-classes (:linear :rewrite))


(defthmd <-expt-bridge-bridge
  (implies (and (< (* a x) c)
                (rationalp a)
                (rationalp x)
                (<= 0 x)
                (rationalp c)
                (<= 0 c)
                (rationalp d)
                (<= 0 d)
                (<= d a))
           (< (* x d) c))
  :hints (("goal" :cases ((<= (* x d) (* a x)))
           :in-theory (enable *-PRESERVES->=-FOR-NONNEGATIVES))))

(defthmd <-expt-bridge
  (implies (and (< (* V (EXPT 2 S)) (EXPT 2 N1))
                (<= 0 v)
                (<= 0 n1)
                (integerp v)
                (integerp s)
                (integerp n1)
                (integerp n2))
           (< (* (EXPT 2 S) (LOGHEAD N2 V))
              (EXPT 2 N1)))
  :hints (("goal" :use ((:instance loghead-<= (n n2) (x v) (y v)))
           :in-theory (e/d (<-expt-bridge-bridge) (loghead-<)))))

(defthmd lshu-bound-2
  (implies (and (unsigned-byte-p (- n1 s) v)
                (integerp n1)
                (integerp n2)
                (<= 0 n2)
                (integerp s)
                (<= 0 n1)
                )
           (unsigned-byte-p n1 (lshu n2 v s)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (lshu
                            <-expt-bridge
                            UNSIGNED-BYTE-P
                            ASH-BOUND4
                            ASH-BOUND3a)
                           ()))))

(defthm lshu-bound-template
  (implies (and (<= v (1- (expt 2 (- n1 s))))
                (integerp n1)
                (integerp n2)
                (<= 0 n2)
                (integerp s)
                (<= 0 n1)
                (< s n1)
                (integerp v)
                (<= 0 v)
                )
           (<= (lshu n2 v s) (1- (expt 2 n1))))
  :rule-classes nil
  :hints (("goal" :use (lshu-bound-2)
           :in-theory (e/d (UNSIGNED-BYTE-P)
                           (  lshu-bound-2 EXPT-MINUS)))))

(defthmd lshu-bound-instance1
  (implies (and (<= v (1- (expt 2 (- 31 s))))
                (integerp n2)
                (<= 0 n2)
                (integerp s)
                (< s 31)
                (integerp v)
                (<= 0 v)
                )
           (<= (lshu n2 v s) 2147483647))
  :hints (("goal" :use (:instance lshu-bound-template (n1 31) ; (bound 2147483647)
                                  ))))

(defthmd lshu-bound-instance2
  (implies (and (<= v (1- (expt 2 (- 16 s))))
                (< s 16)
                (integerp n2)
                (<= 0 n2)
                (integerp s)
                (integerp v)
                (<= 0 v)
                )
           (<= (lshu n2 v s) 65535))
  :hints (("goal" :use (:instance lshu-bound-template (n1 16) ; (bound 65535)
                                  ))))

(defthmd lshu-bound-instance3
  (implies (and (<= v (1- (expt 2 (- 31 s))))
                (< s 31)
                (integerp n2)
                (<= 0 n2)
                (integerp s)
                (integerp v)
                (<= 0 v)
                )
           (< (lshu n2 v s) 2147483648))
  :hints (("goal" :use lshu-bound-instance1
           :in-theory (disable lshu-bound-instance1))))

;;
;; meta rule to simplify loghead of a sum
;;

;Returns a term representing the conjunctionof TERM1 and TERM2.
(defund make-conjunction (term1 term2)
  (declare (type t term1 term2))
  (if (equal term1 ''t)
      term2 ;conjoining something with "true" has no effect
    (if (equal term2 ''t)
        term1 ;conjoining something with "true" has no effect
      `(if ,term1 ,term2 'nil))))


(defund call-to-loghead-with-n-or-greater-size (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))))
  (and (consp term)
       (equal 'loghead (car term))
       (let ((size-param (cadr term)))
         (or (equal n size-param)
             (and (quotep n)
                  (quotep size-param)
                  (integerp (cadr n))
                  (integerp (cadr size-param))
                  (<= (cadr n) (cadr size-param)))))))

;if term isn't a call to loghead of n, just return term
(defund strip-loghead-from-term (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))
                  :guard-hints (("Goal" :in-theory (enable call-to-loghead-with-n-or-greater-size)))))
  (if (call-to-loghead-with-n-or-greater-size n term)
      (caddr term)
    term))

;assumes the sum nest has already been somewhat normalized (right associated, etc.)
(defun strip-logheads-from-sum (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))))
  (if (not (consp term))
      term
    (case (car term)
          (binary-+ `(binary-+ ,(strip-logheads-from-sum n (cadr term)) ;(strip-loghead-from-term n (cadr term))
                               ,(strip-logheads-from-sum n (caddr term))))
          (unary-- `(unary-- ,(strip-loghead-from-term n (cadr term))))
          (otherwise (strip-loghead-from-term n term)))))

;;We could perhaps make this more efficient by first doing a check that there
;;is at least one loghead call to strip off, thus avoiding reconstructing the
;;whole term when there is no stripping of logheads to be done.
(defun strip-logheads-from-sum-aux (term)
  (declare (xargs :guard (and (pseudo-termp term))))

  (if (and (consp term)
           (equal (car term) 'loghead))
      `(loghead ,(cadr term) ,(strip-logheads-from-sum (cadr term) (caddr term)))
    term))

;(strip-logheads-from-sum-aux '(loghead '16 (binary-+ (loghead '16 x) (loghead '16 y))))

(defun hyp-for-addend (n term)
  (declare (xargs :guard (and (pseudo-termp n)
                              (pseudo-termp term))
                  :guard-hints (("Goal" :in-theory (enable call-to-loghead-with-n-or-greater-size)))))
  (if (call-to-loghead-with-n-or-greater-size n term)
      `(integerp ,(caddr term))
    `(integerp ,term)
    ))

;returns a list of things which the hyp must claim are integers - bzo right now, that's all the addends, with the logheads stipped off!  can we do better?
(defun hyp-for-addends (n term)
  (declare (xargs :guard (and (pseudo-termp term)
                              (pseudo-termp n))))
  (if (not (consp term))
      `(integerp ,term)
    (case (car term)
          (binary-+ (make-conjunction
                     (hyp-for-addends n (cadr term))
                     (hyp-for-addends n (caddr term))))
          (unary-- (hyp-for-addend n (cadr term)))
          (otherwise (hyp-for-addend n term)))))

(defun hyp-for-strip-logheads-from-sum-aux (term)
  (declare (xargs :guard (and (pseudo-termp term))))
  (if (and (consp term)
           (equal (car term) 'loghead))
      (hyp-for-addends (cadr term) (caddr term))
    nil ;what should this be?
    ))

(defthm eval-of-hyp-for-addends-helper
  (implies (loghead-sum-eval (hyp-for-addends n term) alist)
           (integerp (loghead-sum-eval term alist)))
  :hints (("Goal" :in-theory (enable MAKE-CONJUNCTION
                                     CALL-TO-LOGHEAD-WITH-N-OR-GREATER-SIZE)
           :do-not '(generalize eliminate-destructors))))

(defthm eval-of-hyp-for-addends-helper2
  (implies (loghead-sum-eval (hyp-for-addends n term) alist)
           (integerp (loghead-sum-eval (strip-logheads-from-sum n term) alist)))
  :hints (("Goal" :in-theory (enable make-conjunction
                                     STRIP-LOGHEAD-FROM-TERM)
           :do-not '(generalize eliminate-destructors))))

(defthm car-of-HYP-FOR-ADDENDS-isnt-quote
  (not (EQUAL 'COMMON-LISP::QUOTE
              (CAR (HYP-FOR-ADDENDS N term))))
  :hints (("Goal" :in-theory (enable MAKE-CONJUNCTION)
           :do-not '(generalize eliminate-destructors))))


(defthm fix-does-nothing
  (implies (acl2-numberp x)
           (equal (fix x)
                  x)))

(defthm meta-rule-helper
  (implies (and (loghead-sum-eval (hyp-for-addends n term) alist))
           (equal (loghead (loghead-sum-eval n alist)
                           (loghead-sum-eval term alist))
                  (loghead (loghead-sum-eval n alist)
                           (loghead-sum-eval (strip-logheads-from-sum n term) alist))))
  :hints (("Goal" :in-theory (e/d (make-conjunction
                                     strip-loghead-from-term
                                     CALL-TO-LOGHEAD-WITH-N-OR-GREATER-SIZE)
                                  (UNSIGNED-BYTE-P-LOGHEAD-FORWARD-CHAINING ;i think this prevents specious simplification
                                   ))
           :do-not '(generalize eliminate-destructors))))

(defthm meta-rule-eric
  (implies (loghead-sum-eval (hyp-for-strip-logheads-from-sum-aux term) alist)
           (equal (loghead-sum-eval term alist)
                  (loghead-sum-eval (strip-logheads-from-sum-aux term) alist)))
  :otf-flg t
  :rule-classes ((:meta :trigger-fns (loghead)))
  :hints (("Goal" :do-not-induct t
           :do-not '(generalize eliminate-destructors))))


;;thms about min and max
;bzo disable min and max later?

(defthm integerp-max
  (implies
   (and
    (integerp a)
    (integerp b))
   (integerp (max a b))))

(defthm integerp-min
  (implies
   (and
    (integerp a)
    (integerp b))
   (integerp (min a b))))


; Opening max and min causes too much casesplitting.  We add some
; rules that simplify max and min expressions, in case we later disable min and max.

(defthm equal-max-x-x
  (equal (max x x)
         x))

(defthm max-linear
  (and
   (<= a (max a b))
   (<= b (max a b)))
  :rule-classes :linear)

(defthm equal-a-max-a
  (implies
   (and
    (rationalp a)
    (rationalp b))
   (and
    (equal
     (equal (max a b) a)
     (<= b a))
   (equal
    (equal (max a b) b)
    (<= a b)))))

(defthm max-constants
  (implies
   (and
    (syntaxp (quotep x))
    (syntaxp (quotep y)))
   (equal
    (max x (max y z))
    (max (max x y) z))))

(defthm max-simplify
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (<= a b)
     (and
      (equal (<= a (max b c)) t)
      (equal (<= a (max c b)) t)))
    (implies
     (< a b)
     (and
      (equal (<= b (max a c)) (<= b c))
      (equal (<= b (max c a)) (<= b c))))
    (implies
     (< a b)
     (and
      (equal (< a (max b c)) t)
      (equal (< a (max c b)) t)))
    (implies
     (<= a b)
     (and
      (equal (< b (max a c)) (< b c))
      (equal (< b (max c a)) (< b c)))
     ))))

(defthm max-simplify2
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (< a b)
     (and
      (equal (<= (max b c) a) nil)
      (equal (<= (max c b) a) nil)))
    (implies
     (<= a b)
     (and
      (equal (<= (max a c) b) (<= c b))
      (equal (<= (max c a) b) (<= c b))))
    (implies
     (<= a b)
     (and
      (equal (< (max b c) a) nil)
      (equal (< (max c b) a) nil)))
    (implies
     (< a b)
     (and
      (equal (< (max a c) b) (< c b))
      (equal (< (max c a) b) (< c b)))))))

(defthm +-over-max
  (implies
   (syntaxp (quotep a))
  (equal
   (+ a (max b c))
   (max (+ a b) (+ a c)))))


(defthm commutativity-of-max
  (implies
   (and
    (acl2-numberp a)
    (acl2-numberp b))
   (equal (max a b) (max b a))))

(defthm equal-min-x-x
  (equal (min x x) x))

(defthm min-linear
  (and
   (<= (min a b) a)
   (<= (min a b) b))
  :rule-classes :linear)

(defthm equal-a-min-a
  (implies
   (and
    (rationalp a)
    (rationalp b))
   (and
    (equal
     (equal (min a b) a)
     (<= a b))
    (equal
     (equal (min a b) b)
     (<= b a)))))

(defthm min-simplify
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (<= a b)
     (and
      (equal (<= a (min b c)) (<= a c))
      (equal (<= a (min c b)) (<= a c))))
    (implies
     (< a b)
     (and
      (equal (<= b (min a c)) nil)
      (equal (<= b (min c a)) nil)))
    (implies
     (< a b)
     (and
      (equal (< a (min b c)) (< a c))
      (equal (< a (min c b)) (< a c))))
    (implies
     (<= a b)
     (and
      (equal (< b (min a c)) nil)
      (equal (< b (min c a)) nil))))))

(defthm min-simplify2
  (implies
   (and
    (rationalp a)
    (rationalp b)
    (rationalp c))
   (and
    (implies
     (< a b)
     (and
      (equal (<= (min b c) a) (<= c a))
      (equal (<= (min c b) a) (<= c a))))
    (implies
     (<= a b)
     (and
      (equal (<= (min a c) b) t)
      (equal (<= (min c a) b) t)))
    (implies
     (<= a b)
     (and
      (equal (< (min b c) a) (< c a))
      (equal (< (min c b) a) (< c a))))
    (implies
     (< a b)
     (and
      (equal (< (min a c) b) t)
      (equal (< (min c a) b) t))))))

(defthm min-constants
  (implies
   (and
    (syntaxp (quotep x))
    (syntaxp (quotep y)))
   (equal
    (min x (min y z))
    (min (min x y) z))))

(defthm +-over-min
  (equal
   (+ a (min b c))
   (min (+ a b) (+ a c))))

(defthm commutativity-of-min
  (implies
   (and
    (acl2-numberp a)
    (acl2-numberp b))
   (equal (min a b) (min b a))))

;(in-theory (disable len))

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
           (signed-byte-p 32 x)))

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
(defthm the-error-noop
  (equal (the-error y x)
         x)
  :hints (("goal" :in-theory (enable the-error))))

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
           :in-theory (enable LOGOPS-RECURSIVE-DEFINITIONS-THEORY b-and b-xor open-logcons))))

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
                              ) (MOVE-NEGATED-TERM-TO-OTHER-SIDE-OF-<-TERM-1-ON-RHS ?
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

(in-theory (disable unsigned-byte-p))

;see FALSIFY-UNSIGNED-BYTE-P
;consider disabling for the user of this library
(defthm unsigned-byte-p-when-n-is-not-an-integerp
  (implies (not (integerp n))
           (equal (unsigned-byte-p n x)
                  nil))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-when-n-is-non-positive
  (implies (<= n 0)
           (equal (unsigned-byte-p n x)
                  (and (equal 0 n)
                       (equal 0 x) )))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;try disabling this?
(defthm unsigned-byte-p-forward-to-expt-bound
  (implies (unsigned-byte-p bits i)
           (< i (expt 2 bits)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     integer-range-p)))
  :rule-classes :forward-chaining)

;If we are trying to show (unsigned-byte-p n x) and we know that x is <= some k, then if we can show that k is <=
;(2^n)-1, we rewrite the unsigned-byte-p claim to a conjunction of seemingly easier facts.  One might object that
;this rule takes us from the nice world of bit vectors to the dirty world of arithmetic, but if we can establish
;the upper bound on x, I think we are already in the dirty arithmetic world, and I'd hate to see a proof of
;unsigned-byte-p fail when we alread have the upper bound, which seems like the hard part to me.

;bzo maybe the signed-byte-p rules are too agressive?  because we often know that x is >= 0...

(defthm unsigned-byte-p-rewrites-to-lower-bound-when-we-know-upper-bound-one
  (implies (and (<= x k) ;k is a free variable
                (<= k (+ -1 (expt 2 n)))
                )
           (equal (unsigned-byte-p n x)
                  (and (integerp x)
                       (<= 0 x)
                       (integerp n)
                       )
                  ))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P UNSIGNED-BYTE-P))))

(defthm unsigned-byte-p-rewrites-to-lower-bound-when-we-know-upper-bound-two
  (implies (and (< x k) ;k is a free variable
                (<= k (expt 2 n)) ;(<= k (+ -1 (expt 2 n)))
                )
           (equal (unsigned-byte-p n x)
                  (and (<= 0 x)
                       (integerp x)
                       (<= 0 n)
                       (integerp n))))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P UNSIGNED-BYTE-P))))

(defthmd usb-free-backchain
  (implies (and (<= x k) ;k is a free variable
                (<= k (1- (expt 2 n)))
                (integerp n)
                (integerp x)
                (<= 0 x)
                )
           (unsigned-byte-p n x))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P
                                     UNSIGNED-BYTE-P))))

(defthmd usb-free-backchain1
  (implies (and (< x k)
                (<= k (1- (expt 2 n)))
                (integerp n)
                (integerp x)
                (<= 0 x)
                )
           (unsigned-byte-p n x))
  :hints (("goal" :in-theory (enable INTEGER-RANGE-P
                                     UNSIGNED-BYTE-P))))

(defthm unsigned-byte-p-of-1
  (equal (unsigned-byte-p n 1)
         (and (integerp n)
              (< 0 n)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p
                                     integer-range-p))))

;bzo add syntaxp hyps like the one for this rule to other rules?
(defthm unsigned-byte-p-of-x-minus-1
  (implies (and (syntaxp (not (quotep x))) ;prevents bad behavior when acl2 unifies (+ -1 x) with a constant
                (unsigned-byte-p n x)
                )
           (equal (unsigned-byte-p n (+ -1 x))
                  (not (equal 0 x)))))

(defthm unsigned-byte-p-of-expt
  (equal (unsigned-byte-p n (expt 2 m))
         (and (< (ifix m) n)
              (<= 0 (ifix m))
              (integerp n)))
  :otf-flg t
  :hints (("Goal" :cases ((integerp m))
           :in-theory (enable unsigned-byte-p))))

;generalize to non-powers-of-2
(defthm unsigned-byte-p-of-expt-const-version
  (implies (and (syntaxp (quotep k))
                (acl2::power2p k))
           (equal (unsigned-byte-p n k)
                  (and (< (expo k) n)
                       (<= 0 (expo k))
                       (integerp n))))
  :hints (("Goal" :in-theory (disable unsigned-byte-p-of-expt)
           :use (:instance unsigned-byte-p-of-expt (m (expo k))))))

(defthm unsigned-byte-p-when-adding-big-power-of-2
  (equal (unsigned-byte-p n (+ (expt 2 n) y))
         (and (integerp n)
              (<= 0 n)
              (if (acl2-numberp y)
                  (or (equal y (- (expt 2 n)))
                      (and (unsigned-byte-p n (- y))
                           (not (equal 0 y))))
                nil)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p-when-adding-big-power-of-2-constant-version
  (implies (and (syntaxp (quotep k))
                (equal k (expt 2 n)))
           (equal (unsigned-byte-p n (+ k y))
                  (and (integerp n)
                       (<= 0 n)
                       (if (acl2-numberp y)
                           (or (equal y (- (expt 2 n)))
                               (and (unsigned-byte-p n (- y))
                                    (not (equal 0 y))))
                         nil))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defthm unsigned-byte-p--of-minus
  (equal (unsigned-byte-p n (- y))
         (and (integerp n)
              (<= 0 n)
              (if (acl2-numberp y)
                  (and (<= y 0)
                       (and (signed-byte-p (+ 1 n) y)
                            (not (equal y (- (expt 2 n))))))
                t)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p signed-byte-p))))

;this might be expensive?
(defthm equal-bit-1
  (implies (unsigned-byte-p 1 x)
           (equal (equal x 1)
                  (not (equal x 0)))))

(defthm unsigned-byte-p-+-easy
  (implies (and; (integerp n)
        ;        (< 0 n)
                (unsigned-byte-p (1- n) x)
                (unsigned-byte-p (1- n) y))
           (unsigned-byte-p n (+ x y)))
  :hints (("goal" :in-theory (enable unsigned-byte-p EXPONENTS-ADD-UNRESTRICTED))))

;it's maybe a bit odd that this is about the size parameter (which will probably usually be a constant in code proofs)
(defthmd unsigned-byte-p-fc-to-size-is-natural
  (implies (unsigned-byte-p n x)
           (and (integerp n)
                (<= 0 n)))
  :rule-classes ((:forward-chaining :trigger-terms ((unsigned-byte-p n x))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

;could allow the sizes of x and y to differ and then use the larger
(defthm unsigned-byte-p-+-easy-fc
  (implies (and (unsigned-byte-p n x) ;n is a free variable
                ;(integerp n)
                ;(<= 0 n)
                (unsigned-byte-p n y))
           (unsigned-byte-p (+ 1 n) (+ x y)))
  :hints (("goal" :in-theory (enable  unsigned-byte-p-fc-to-size-is-natural)
           :use ((:instance unsigned-byte-p-+-easy (n (1+ n))))))
  :rule-classes ((:forward-chaining :trigger-terms ((+ x y)))))

;; (defun remove-list (list target)
;;   (declare (type (satisfies eqlable-listp) list target))
;;   (if (consp list)
;;       (remove-list (cdr list) (remove (car list) target))
;;     target))
