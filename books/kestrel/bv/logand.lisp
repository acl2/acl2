; BV Library: logand
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2019 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(local (include-book "../arithmetic-light/floor"))
(local (include-book "../arithmetic-light/mod"))
(local (include-book "../arithmetic-light/plus"))
(local (include-book "../arithmetic-light/plus-and-minus"))
(local (include-book "../arithmetic-light/times"))
(local (include-book "../arithmetic-light/times-and-divides"))
(local (include-book "../arithmetic-light/mod-and-expt"))
(local (include-book "../arithmetic-light/floor-and-expt"))
(local (include-book "../arithmetic-light/floor-mod-expt"))
(local (include-book "../arithmetic-light/minus"))
(local (include-book "../arithmetic-light/expt2"))
(local (include-book "../arithmetic-light/numerator"))
(local (include-book "../arithmetic-light/integerp"))
(local (include-book "../../meta/meta-plus-lessp"))
(local (include-book "../../meta/meta-plus-equal"))

(in-theory (disable binary-logand))

(defthm commutativity-of-logand
  (equal (logand i j)
         (logand j i))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-of-0
  (equal (logand 0 j)
         0)
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-of--1
  (equal (logand -1 j)
         (ifix j))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-when-not-integerp-arg1-cheap
  (implies (not (integerp i))
           (equal (logand i j)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-when-not-integerp-arg2-cheap
  (implies (not (integerp j))
           (equal (logand i j)
                  0))
  :rule-classes ((:rewrite :backchain-limit-lst 0))
  :hints (("Goal" :in-theory (enable logand))))

(defthmd logand-when-not-integerp-arg1
  (implies (not (integerp i))
           (equal (logand i j)
                  0))
  :hints (("Goal" :in-theory (enable logand))))

(defthmd logand-when-not-integerp-arg2
  (implies (not (integerp j))
           (equal (logand i j)
                  0))
  :hints (("Goal" :in-theory (enable logand))))

(local
 (defthm <-of-logand-and-0-helper
   (implies (and (integerp i)
                 (integerp j))
            (iff (< (logand i j) 0)
                 (and (< i 0)
                      (< j 0))))
   :hints (("Goal" :induct (logand i j)
            :in-theory (enable logand floor)))))

(defthm <-of-logand-and-0
  (equal (< (logand i j) 0)
         (and (< i 0)
              (< j 0)
              (integerp i)
              (integerp j)))
  :hints (("Goal" :use (:instance <-of-logand-and-0-helper)
           :in-theory (disable <-of-logand-and-0-helper))))

(defthm logand-non-negative-type
  (implies (or (<= 0 i)
               (<= 0 j))
           (<= 0 (logand i j)))
  :rule-classes :type-prescription)

(defthm logand-negative-type
  (implies (and (< i 0)
                (< j 0)
                (integerp i)
                (integerp j))
           (< (logand i j) 0))
  :rule-classes :type-prescription)

(defthm logand-non-positive-type
  (implies (and (<= i 0)
                (<= j 0))
           (<= (logand i j) 0))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-same
  (equal (logand i i)
         (ifix i))
  :hints (("Goal" :in-theory (enable logand *-of-2-and-floor-of-2)
           :expand (logand i i))))

(defthm <=-of-logand-same-arg1
  (implies (<= 0 i)
           (<= (logand i j) i))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable logand))))

(defthm <=-of-logand-same-arg2
  (implies (<= 0 j)
           (<= (logand i j) j))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :use (:instance <=-of-logand-same-arg1 (i j) (j i))
           :in-theory (disable <=-of-logand-same-arg1))))

(defthm equal-of-logand-and--1
  (equal (equal -1 (logand i j))
         (and (equal -1 i)
              (equal -1 j)))
  :hints (("Goal" :in-theory (enable logand
                                     floor-of-2-cases))))

(local
 (defthmd logand-is-zero-helper
   (implies (equal 0 (logand i k))
            (equal (logand i j k) 0))
   :hints (("Goal" :in-theory (enable logand
                                      floor-of-2-cases)))))

(local
 (defthmd logand-is-zero-helper-2
   (implies (equal 0 (logand i j))
            (equal (logand i j k) 0))
   :hints (("Goal" :in-theory (enable logand
                                      floor-of-2-cases)))))

(defthm logand-associative
  (equal (logand (logand i j) k)
         (logand i (logand j k)))
  :hints (("Goal" :in-theory (enable logand
                                     floor-of-2-cases
                                     zip
                                     logand-is-zero-helper
                                     logand-is-zero-helper-2)
           :induct t
           :expand ((:free (j) (logand i j))
                    (:free (j) (logand k j))))))

(defthm logand-commutative-2
  (equal (logand i j k)
         (logand j i k))
  :hints (("Goal" :use ((:instance logand-associative)
                        (:instance logand-associative (i j) (j i)))
           :in-theory (disable logand-associative))))

(defthm logand-same-2
  (equal (logand i i j)
         (logand i j))
  :hints (("Goal" :cases ((integerp i))
           :use (:instance logand-associative (j i) (k j))
           :in-theory (disable logand-associative))))

(defthm logand-combine-constants
  (implies (syntaxp (and (quotep i)
                         (quotep j)))
           (equal (logand i (logand j k))
                  (logand (logand i j) k))))

;; logand is even iff either argument is
(defthm integerp-of-*-1/2-of-logand
  (implies (and (integerp i)
                (integerp j))
           (equal (integerp (* 1/2 (logand i j)))
                  (or (integerp (* 1/2 i))
                      (integerp (* 1/2 j)))))
  :hints (("Goal" :in-theory (enable logand))))

(defun floor-floor-sub1-induct (x y n)
  (if (zp n)
      (list x y n)
    (floor-floor-sub1-induct (floor x 2) (floor y 2) (+ -1 n))))

(defthm floor-of-logand-and-expt
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (floor (logand i j) (expt 2 n))
                  (logand (floor i (expt 2 n))
                          (floor j (expt 2 n)))))
  :hints (("Goal"
           :in-theory (e/d (expt-of-+
                            ;floor-of-logand-and-2-back
                            *-of-2-and-floor-of-2)
                           (;floor-of-logand-and-2
                            mod-sum-cases))
           :expand (binary-logand i j)
           :induct (floor-floor-sub1-induct i j n))))

(defthm floor-of-logand-and-2
  (implies (and (integerp i)
                (integerp j))
           (equal (floor (logand i j) 2)
                  (logand (floor i 2) (floor j 2))))
  :hints (("Goal" :use (:instance floor-of-logand-and-expt (n 1))
           :in-theory (disable floor-of-logand-and-expt))))

;rename
(defthmd floor-of-logand-and-2-back
  (implies (and (integerp i)
                (integerp j))
           (equal (logand (floor i 2) (floor j 2))
                  (floor (logand i j) 2))))

(theory-invariant (incompatible (:rewrite floor-of-logand-and-2) (:rewrite floor-of-logand-and-2-back)))

(defthmd logand-of-floor-arg2
  (implies (and (integerp i)
                (integerp j))
           (equal (logand i (floor j 2))
                  (floor (logand (* 2 i) j) 2)))
  :hints (("Goal" :in-theory (enable floor-of-logand-and-2
                                     floor-when-multiple))))

(defthm <=-of-logand-same-when-negative
  (implies (and (<= i 0) ;unusual
                (< j 0)  ;unusual
                (integerp i)
                (integerp j))
           (<= (logand i j) i))
  :hints (("Goal" :do-not '(generalize eliminate-destructors)
           :in-theory (enable logand zip)
           :induct (logand i j))))

(defthm logand-of-lognot-same
  (equal (logand i (lognot i))
         0)
  :hints (("Goal" :in-theory (enable logand lognot))))

;could wrap the mod around either or both args
(defthm mod-of-logand-and-expt-alt
  (implies (and (natp n)
                (integerp i)
                (integerp j))
           (equal (mod (logand i j) (expt 2 n))
                  (logand (mod i (expt 2 n)) j)))
  :hints (("subgoal *1/2"
           :use (:instance <=-of-logand-same-arg2
                           (j (floor (mod i (expt 2 n)) 2))
                           (i (floor j 2))))
          ("Goal" :induct (floor-floor-sub1-induct i j n)
           :expand ((:free (i) (logand j i)))
           :in-theory (e/d (logand
                            mod-expt-split2
                            ;mod-of-floor-and-expt-of-one-less
                            zip
                            expt-of-+
                            mod-of-floor-of-2-and-expt-of-one-less
                            )
                           (;logand-with-mask-better-alt
                            mod-floor-2-expt-2
                            <=-of-logand-same-arg2)))))

;; in this version we push the mod into both args of logand
(defthm mod-of-logand-and-expt
  (implies (and (natp n)
                (integerp i)
                (integerp j))
           (equal (mod (logand i j) (expt 2 n))
                  (logand (mod i (expt 2 n))
                          (mod j (expt 2 n)))))
  :hints (("subgoal *1/2"
           :use ((:instance mod-bound-linear-arg2-strong
                            (x (logand (floor i 2) (floor j 2)))
                            (y (* 1/2 (expt 2 n))))))
          ("Goal" :induct (floor-floor-sub1-induct i j n)
           :expand ((:free (i) (logand j i)))
           :in-theory (e/d (logand
                            mod-expt-split2
                            ;mod-of-floor-and-expt-of-one-less
                            zip
                            expt-of-+
                            mod-of-floor-of-2-and-expt-of-one-less)
                           (;logand-with-mask-better-alt
                            mod-floor-2-expt-2
                            <=-of-logand-same-arg2)))))

(defthm mod-of-logand-and-2
  (implies (and (integerp i)
                (integerp j))
           (equal (mod (logand i j) 2)
                  (logand (mod i 2)
                          (mod j 2))))
  :hints (("Goal" :use (:instance mod-of-logand-and-expt (n 1))
           :in-theory (disable mod-of-logand-and-expt))))

;rename
(defthm logand-of-negative-and-positive
  (implies (and (integerp i)
                (<= 0 i)
                (< i (expt 2 n))
                (integerp j)
                (<= j (- (expt 2 n)))
                (< j 0))
           (< (logand i j) (expt 2 n))))

;rename
(defthm logand-of-negative-and-negative
  (implies (and (integerp j)
                (<= j (- (expt 2 n)))
                (< j 0)
                (integerp i)
                (<= i (- (expt 2 n)))
                (< i 0)
                )
           (< (logand i j) (expt 2 n))))

;gen?
(defthm <-of-logand
  (implies (and (or (< i k)
                    (< j k))
                (natp i)
                (natp j)
                (natp k))
           (< (logand i j) k))
  :hints (("Goal" :in-theory (enable logand))))

;;rename
;drop?
(defthmd logand-of-x-and-not-x-lemma
  (implies (integerp i)
           (equal (logand i (+ -1 (- i)))
                  0))
  :hints (("Goal" :use (:instance logand-of-lognot-same)
           :in-theory (e/d (lognot)
                           (logand-of-lognot-same)))))

;drop?
(defthmd logand-of-floor-and-floor-when-0
  (implies (and (equal (logand j k) 0)
                (integerp j)
                (integerp k))
           (equal (logand (floor j 2) (floor k 2))
                  0))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-of-+-1-of-*-2-and-+-1-of-*-2
  (implies (and (integerp i)
                (integerp j))
           (equal (logand (+ 1 (* 2 i))
                          (+ 1 (* 2 j)))
                  (+ 1 (* 2 (logand i j)))))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-of-*-2-and-*-2
  (implies (and (integerp i)
                (integerp j))
           (equal (logand (* 2 i)
                          (* 2 j))
                  (* 2 (logand i j))))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-of-+-1-of-*-2-and-*-2
  (implies (and (integerp i)
                (integerp j))
           (equal (logand (+ 1 (* 2 i))
                          (* 2 j))
                  (* 2 (logand i j))))
  :hints (("Goal" :in-theory (enable logand))))

(defthm logand-of-*-2-and-+-1-of-*-2
  (implies (and (integerp i)
                (integerp j))
           (equal (logand (* 2 i)
                          (+ 1 (* 2 j)))
                  (* 2 (logand i j))))
  :hints (("Goal" :in-theory (enable logand))))

;; (defthmd logand-of-+-1-and-*2-arg2
;;   (implies (and (integerp i)
;;                 (integerp j))
;;            (equal (logand i (+ 1 (* 2 j)))
;;                   (+ (mod i 2) (* 2 (logand (floor i 2) j)))))
;;   :hints (("Goal" :in-theory (enable ; logand
;;                               ))))

(defthm logand-lower-bound-negative
  (implies (and (<= (- (expt 2 n)) i)
                (<= (- (expt 2 n)) j)
                (<= i 0)
                (<= j 0)
                (integerp i)
                (integerp j)
                (natp n))
           (<= (- (expt 2 n))
               (logand i j)))
  :hints (("Goal" :in-theory (e/d (logand expt
                                          <-of-floor-arg1)
                                  (expt-hack))
           :induct (floor-floor-sub1-induct i j n)
           :expand ((logand i j)))))

(defthm logand-lower-bound-negative-2
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (<= (- (expt 2 n)) (logand i j))
                  (or (<= 0 i)
                      (<= 0 j)
                      (and (<= (- (expt 2 n)) i)
                           (<= (- (expt 2 n)) j)))))
  :hints (("Goal" :in-theory (e/d (logand expt
                                          <-of-floor-arg1)
                                  (expt-hack))
           :induct (floor-floor-sub1-induct i j n)
           :expand ((logand i j)))))

(defthm logand-lower-bound-negative-2-alt
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (< (logand i j) (- (expt 2 n)))
                  (and (< i 0)
                       (< j 0)
                       (or (< i (- (expt 2 n)))
                           (< j (- (expt 2 n)))))))
  :hints (("Goal" :use (:instance logand-lower-bound-negative-2)
           :in-theory (disable logand-lower-bound-negative-2))))

(defthm unsigned-byte-p-of-logand
  (implies (or (unsigned-byte-p n i)
               (unsigned-byte-p n j))
           (unsigned-byte-p n (logand i j)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p))))

(defun floor-by-2-and-sub-1-induct (i n)
  (if (zp n)
      (list i n)
    (floor-by-2-and-sub-1-induct (floor i 2) (+ -1 n))))

(defthm logand-of-plus--1-of-expt
  (implies (and (natp size)
                (integerp i))
           (equal (logand i (+ -1 (expt 2 size)))
                  (mod i (expt 2 size))))
  :hints (("Goal" :induct (floor-by-2-and-sub-1-induct i size)
           :expand (LOGAND I (+ -1 (EXPT 2 SIZE)))
           :in-theory (e/d (logand
                            mod-of-floor-of-2-and-expt-of-one-less-alt)
                           (expt-hack
                            mod-floor-2-expt-2)))))

(add-invisible-fns logand lognot)

(local
 (defthm helper
   (implies (and (equal (+ i (expt 2 n)) 0)
                 (posp n))
            (equal (floor i 2)
                   (- (expt 2 (+ -1 n)))))
   :hints (("Goal" :cases ((equal i (- (EXPT 2 N))))
            :in-theory (enable FLOOR-WHEN-MULTIPLE expt-of-+)
            ))))

(local
 (defthm helper2
   (implies (and (equal (+ i (expt 2 n)) 0)
                 (posp n))
            (integerp (* 1/2 i)))
   :hints (("Goal" :cases ((equal i (- (EXPT 2 N))))))))

(defthm logand-of-+-of-expt-and-+-of-expt
  (implies (and (natp n)
                (integerp i)
                (integerp j)
                (< i 0)
                (< j 0)
                (<= (- (expt 2 n)) i)
                (<= (- (expt 2 n)) j))
           (equal (logand (+ (expt 2 n) i)
                          (+ (expt 2 n) j))
                  (+ (expt 2 n)
                     (logand i j))))
  :hints (("Goal" :induct (floor-floor-sub1-induct i j n)
           :expand (logand i j)
           :do-not '(generalize eliminate-destructors)
           :in-theory (e/d (logand expt-of-+
                                   <-of-floor-arg1)
                           (expt-hack)))))

(defthmd logand-of-mod-and-mod
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (logand (mod i (expt 2 n))
                          (mod j (expt 2 n)))
                  (logand (mod i (expt 2 n))
                          j)))
  :hints (("Goal" :use (mod-of-logand-and-expt-alt
                        mod-of-logand-and-expt)
           :in-theory (disable mod-of-logand-and-expt))))

;; adding expt has no effect because we are chopping the other argument
(defthm logand-of-mod-and-+-of-expt
  (implies (and (integerp i)
                (integerp j)
                (natp n))
           (equal (logand (mod i (expt 2 n)) (+ (expt 2 n) j))
                  (logand (mod i (expt 2 n)) j)))
  :hints (("Goal" :use ((:instance logand-of-mod-and-mod
                                   (j (+ (EXPT 2 N) j)))
                        (:instance logand-of-mod-and-mod
                                   (j j)))
           :in-theory (disable mod-sum-cases))))
