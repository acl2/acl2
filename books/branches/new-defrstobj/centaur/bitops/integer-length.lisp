; Centaur Bitops Library
; Copyright (C) 2010-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>
;
; Additional copyright notice:
;
; Portions of this file were adapted from the data-structures/memories library,
; which is also released under the GPL.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "ihs/logops-definitions" :dir :system)
(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable floor mod integer-length logcdr)))

(defthm |(integerp (* 1/2 (expt 2 n)))|
  (equal (integerp (* 1/2 (expt 2 n)))
         (posp n))
  :hints(("Goal" :in-theory (enable expt))))

(defthm |(* 1/2 (expt 2 n))|
  (implies (integerp n)
           (equal (* 1/2 (expt 2 n))
                  (expt 2 (- n 1)))))



(defsection bitops/integer-length
  :parents (bitops integer-length)
  :short "Basic theorems about @(see integer-length)."

  (defthm integer-length-type-prescription-strong
    ;; Even without any books loaded, ACL2 already knows that (integer-length a)
    ;; is unconditinoally a natp.
    (implies (and (integerp n)
                  (< 0 n))
             (and (integerp (integer-length n))
                  (< 0 (integer-length n))))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable integer-length))))

  (defthm integer-length-type-prescription-strong-negative
    (implies (and (integerp n)
                  (< n -1))
             (and (integerp (integer-length n))
                  (< 0 (integer-length n))))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable integer-length))))

  (defthm integer-length-expt-upper-bound-n
    (implies (integerp n)
             (< n (expt 2 (integer-length n))))
    :rule-classes :linear
    :hints(("Goal"
            :in-theory (enable integer-length*)
            :expand ((:free (b) (expt 2 (+ 1 b))))
            :induct (logcdr-induction-1 n))))

  (defthm integer-length-expt-upper-bound-n-1
    (implies (integerp n)
             (<= n (expt 2 (integer-length (1- n)))))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable integer-length))))

  (defthm integer-length-monotonic
    (implies (and (<= i j)
                  (natp i)
                  (natp j))
             (<= (integer-length i) (integer-length j)))
    :rule-classes :linear
    :hints(("Goal"
            :induct (logcdr-induction-2 i j)
            :in-theory (enable integer-length*))))

  (defthm integer-length-less
    (implies (natp n)
             (<= (integer-length n) n))
    :rule-classes :linear
    :hints(("Goal" :in-theory (enable integer-length*)
            :induct (logcdr-induction-1 n))))



  (encapsulate
    ()
    (local (defun my-induct (n)
             (if (zp n)
                 nil
               (my-induct (1- n)))))

    (defthm |(integer-length (expt 2 n))|
      (implies (natp n)
               (equal (integer-length (expt 2 n))
                      (+ 1 n)))
      :hints(("Goal"
              :induct (my-induct n)
              :do-not '(generalize fertilize)
              :in-theory (enable integer-length*))))

    (defthm |(integer-length (1- (expt 2 n)))|
      (implies (natp n)
               (equal (integer-length (+ -1 (expt 2 n)))
                      n))
      :hints(("Goal"
              :induct (my-induct n)
              :do-not '(generalize fertilize)
              :in-theory (enable integer-length* expt)))))



  (defthm |(integer-length (floor n 2))|
    (implies (natp n)
             (equal (integer-length (floor n 2))
                    (if (zp n)
                        0
                      (- (integer-length n) 1))))
    :hints(("Goal"
            :expand ((:with integer-length* (integer-length n)))
            :in-theory (enable logcdr))))

  (defthm |2^{(integer-length n) - 1} <= n|
    (implies (posp n)
             (<= (expt 2 (1- (integer-length n)))
                 n))
    :hints(("Goal"
            :induct (logcdr-induction-1 n)
            :expand ((:with integer-length* (integer-length n)))))
    :rule-classes ((:rewrite) (:linear)))




  (defthm integer-length-of-logcdr-strong
    (implies (posp (integer-length a))
             (< (integer-length (logcdr a))
                (integer-length a)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable integer-length*))))

  (defthm integer-length-of-logcdr-weak
    (<= (integer-length (logcdr a))
        (integer-length a))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :in-theory (enable logcdr integer-length))))

  (encapsulate
    ()
    (local (defun dec-floor2-induct (a x)
             (if (zp a)
                 x
               (dec-floor2-induct (- a 1)
                                  (floor x 2)))))

    (local (include-book "ihsext-basics"))
    ;; (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
    ;; (local (in-theory (disable functional-commutativity-of-minus-*-left)))

    (local (defthm floor-2
             (implies (integerp i)
                      (equal (floor i 2)
                             (logcdr i)))
             :hints (("goal" :use ((:instance floor-to-logtail (n 1)))
                      :in-theory (e/d (logtail**)
                                      (floor-to-logtail logtail))))))

    (local (defthm ash-<-logcdr-lemma
             (implies (and (< a (ash 1 n))
                           (posp n)
                           (integerp a))
                      (< (logcdr a) (ash 1 (+ -1 n))))
             :hints (("goal" :expand ((:with ash* (ash 1 n)))))))

    (defthm integer-length-bounded-by-expt
      (implies (and (< a (expt 2 n))
                    (natp a)
                    (natp n))
               (< (integer-length a) (+ 1 n)))
      :rule-classes ((:rewrite :corollary
                      (implies (and (syntaxp (or (not (quotep n))
                                                 ;; safety valve to keep this rule from
                                                 ;; exploding Lisp
                                                 (< (cadr n) 1000)))
                                    (< a (expt 2 n))
                                    (natp a)
                                    (natp n))
                               (< (integer-length a) (+ 1 n))))
                     (:linear))
      :hints(("Goal"
              :nonlinearp t
              :in-theory (enable expt-2-is-ash)
              :induct (dec-floor2-induct n a)
              :expand ((:with integer-length* (integer-length a))))))

    (defthm |(integer-length (mod a (expt 2 n)))|
      (implies (and (natp a)
                    (natp n))
               (< (integer-length (mod a (expt 2 n)))
                  (+ 1 n)))
      :hints(("Goal" :in-theory (enable* ihsext-arithmetic)))
      :rule-classes ((:rewrite) (:linear)))))

