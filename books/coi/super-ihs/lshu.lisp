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

;clean this up!

(include-book "ihs/ihs-lemmas" :dir :system)
(include-book "arithmetic")
(include-book "hacks")

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