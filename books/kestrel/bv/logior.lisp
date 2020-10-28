; BV Library: logior
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/mod-and-expt"))
(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/floor-mod-expt"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/integerp"))
(local (include-book "../../meta/meta-plus-equal"))
(local (include-book "../../meta/meta-plus-lessp"))
(local (include-book "logand")) ;;logior is defined in terms of logand
(local (include-book "lognot")) ;;logior is defined in terms of lognot

(in-theory (disable binary-logior))

(defthm logior-commutative
  (equal (logior i j)
         (logior j i))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-of--1
  (equal (logior -1 j)
         -1)
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-of-0
  (equal (logior 0 j)
         (ifix j))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-when-not-integerp-arg1
  (implies (not (integerp i))
           (equal (logior i j)
                  (ifix j)))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-when-not-integerp-arg2
  (implies (not (integerp j))
           (equal (logior i j)
                  (ifix i)))
  :hints (("Goal" :in-theory (enable logior))))

;; This theorem is here because logior is the most complex function it
;; mentions.
(defthmd lognot-of-logand
  (equal (lognot (logand i j))
         (logior (lognot i) (lognot j)))
  :hints (("Goal" :in-theory (enable logior))))

(theory-invariant (incompatible (:definition logior) (:rewrite lognot-of-logand)))

(defthm lognot-of-logior
  (equal (lognot (logior i j))
         (logand (lognot i) (lognot j)))
  :hints (("Goal" :in-theory (e/d (logior) (lognot-of-logand)))))

(defthmd lognot-of-logior-back
  (equal (logand (lognot i) (lognot j))
         (lognot (logior i j))))

(defthm logior-associative
  (equal (logior (logior i j) k)
         (logior i (logior j k)))
  :hints (("Goal" :in-theory (enable logior))))

(defthm <-of-logior-and-0
  (equal (< (logior i j) 0)
         (or (< (ifix i) 0)
             (< (ifix j) 0)))
  :hints (("Goal" :cases ((< J 0)
                          (and (not (< j 0))
                               (< I 0)))
           :in-theory (enable logior))))

(defthm <-of-logior-and-0-type
  (implies (and (or (< i 0)
                    (< j 0))
                (integerp i)
                (integerp j))
           (< (logior i j) 0))
  :rule-classes :type-prescription)

(defthm logior-non-negative-type
  (implies (and (<= 0 i)
                (<= 0 j))
           (<= 0 (logior i j)))
  :rule-classes :type-prescription
  :hints (("Goal" :cases ((and (integerp i) (integerp j))
                          (and (not (integerp i)) (integerp j))
                          (and (integerp i) (not (integerp j)))))))

(defthm logior-commutative-2
  (equal (logior j i k)
         (logior i j k))
  :hints (("Goal" :use ((:instance logior-associative)
                        (:instance logior-associative (i j) (j i)))
           :in-theory (disable logior-associative))))

(defthm logior-same
  (equal (logior i i)
         (ifix i))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-same-2
  (equal (logior i i j)
         (logior i j))
  :hints (("Goal"
           :use (:instance logior-associative (i i) (j i) (k j))
           :in-theory (disable logior-associative))))

(defthm floor-of-logior-and-2
  (implies (and (integerp i)
                (integerp j))
           (equal (floor (logior i j) 2)
                  (logior (floor i 2) (floor j 2))))
  :hints (("Goal" :in-theory (enable logior floor-of-lognot-and-2))))

(defthmd floor-of-logior-and-2-back
  (implies (and (integerp i)
                (integerp j))
           (equal (logior (floor i 2) (floor j 2))
                  (floor (logior i j) 2))))

(theory-invariant (incompatible (:rewrite floor-of-logior-and-2) (:rewrite floor-of-logior-and-2-back)))

(defthm floor-of-logior-and-expt
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (floor (logior i j) (expt 2 n))
                  (logior (floor i (expt 2 n))
                          (floor j (expt 2 n)))))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logior))))

(defthm mod-of-logior-and-2
  (implies (and (integerp i)
                (integerp j))
           (equal (mod (logior i j) 2)
                  (logior (mod i 2) (mod j 2))))
  :hints (("Goal" :in-theory (enable logior lognot mod-sum-cases))))

(defthm mod-of-logior-expt
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (mod (logior i j) (expt 2 n))
                  (logior (mod i (expt 2 n))
                          (mod j (expt 2 n)))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm equal-of-logior-and-0
  (equal (equal (logior i j) 0)
         (and (equal 0 (ifix i))
              (equal 0 (ifix j))))
  :hints (("Goal" :in-theory (e/d (logior) (lognot-of-logand)))))

(defthm logior-bound
  (implies (and (natp i)
                (natp j))
           (not (< (logior i j) i)))
  :hints (("Goal"
           :use (:instance <=-of-logand-same-when-negative (i (+ -1 (- i)))
                           (j (+ -1 (- j))))
           :in-theory (e/d (logior lognot)
                           (lognot-of-logand
                            <=-of-logand-same-when-negative)))))

(defthm logior-bound-linear
  (implies (and (natp i)
                (natp j))
           (<= i (logior i j)))
  :rule-classes :linear)

(defthm logior-bound-linear-2
  (implies (and (natp i)
                (natp j))
           (<= i (logior j i)))
  :rule-classes :linear)

;drop?
(defthmd equal-of-logior-of-floor-and-floor-and--1
  (implies (and (equal (logior j k) -1)
                (integerp j)
                (integerp k))
           (equal (logior (floor j 2) (floor k 2))
                  -1))
  :hints (("Goal" :in-theory (e/d (logior logand-of-floor-and-floor-when-0
                                          lognot-of-floor-of-2)
                                  (lognot-of-logand)))))

(defthm logior-of-*-2-and-*-2
  (implies (and (integerp i)
                (integerp j))
           (equal (logior (* 2 i) (* 2 j))
                  (* 2 (logior i j))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-of-+-1-and-*-2-and-+-1-of-*-2
  (implies (and (integerp i)
                (integerp j))
           (equal (logior (+ 1 (* 2 i)) (+ 1 (* 2 j)))
                  (+ 1 (* 2 (logior i j)))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-of-*-2-and-+-1-of-*-2
  (implies (and (integerp i)
                (integerp j))
           (equal (logior (* 2 i) (+ 1 (* 2 j)))
                  (+ 1 (* 2 (logior i j)))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm logior-of-*-2-and-+-1-of-*-2-alt
  (implies (and (integerp i)
                (integerp j))
           (equal (logior (+ 1 (* 2 i)) (* 2 j))
                  (+ 1 (* 2 (logior i j)))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm integerp-of-*-1/2-of-logior
  (implies (and (integerp i)
                (integerp j))
           (equal (integerp (* 1/2 (logior i j)))
                  (and (integerp (* 1/2 i))
                       (integerp (* 1/2 j)))))
  :hints (("Goal" :in-theory (enable logior))))

(defthm unsigned-byte-p-of-logior
  (implies (and (unsigned-byte-p n i)
                (unsigned-byte-p n j))
           (unsigned-byte-p n (logior i j)))
  :hints (("Goal"
           :use (:instance logand-lower-bound-negative-2-alt
                           (i (lognot i))
                           (j (lognot j)))
           :in-theory (e/d (logior unsigned-byte-p)
                           (logand-lower-bound-negative-2
                            logand-lower-bound-negative-2-alt)))))

(local
 (defthmd logior-opener-var
   (implies (and (syntaxp (variablep i))
                 (integerp i)
                 (integerp j))
            (equal (logior i j)
                   (+ (if (or (equal 1 (mod i 2))
                              (equal 1 (mod j 2)))
                          1
                        0)
                      (* 2 (logior (floor i 2)
                                   (floor j 2))))))
   :hints (("Goal" :in-theory (e/d (logior LOGNOT-OF-FLOOR-OF-2
                                           floor-of-logand-and-2-back)
                                   (FLOOR-OF-LOGAND-AND-2))))))

(defthm logior-of-logand-same-arg-1
  (implies (and (integerp i)
                (integerp j))
           (equal (logior i (logand i j))
                  i))
  :hints (("Goal" :in-theory (enable logand
                                     logior-opener-var))))

(defthm logior-of-logand-same-arg-1-extra
  (implies (and (integerp i)
                (integerp j))
           (equal (logior i (logand i j) k)
                  (logior i k)))
  :hints (("Goal" :use (:instance logior-of-logand-same-arg-1)
           :in-theory (disable logior-of-logand-same-arg-1))))

(defthm logand-of-logior
  (implies (and (integerp i)
                (integerp j)
                (integerp k))
           (equal (logand i (logior j k))
                  (logior (logand i j)
                          (logand i k))))
  :hints (("Goal" :induct t
           :in-theory (e/d (logand
                            zip
                            logior-opener-var)
                           (lognot-of-logand
                            mod-sum-cases)))))

(defthmd logior-of-logand
  (implies (and (integerp i)
                (integerp j)
                (integerp k))
           (equal (logior i (logand j k))
                  (logand (logior i j)
                          (logior i k))))
  :hints (("Goal" :induct t
           :in-theory (e/d (logand zip)
                           (lognot-of-logand
                            mod-sum-cases)))))
