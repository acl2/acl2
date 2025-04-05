; Bit-vector rotations
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "leftrotate")
(include-book "leftrotate32")
(include-book "rightrotate")
(include-book "rightrotate32")
(include-book "bvif")
(include-book "bvminus") ;todo
(include-book "kestrel/arithmetic-light/lg-def" :dir :system)
(local (include-book "kestrel/arithmetic-light/lg" :dir :system))
(local (include-book "unsigned-byte-p"))
(local (include-book "bvcat"))
(local (include-book "kestrel/arithmetic-light/mod" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod-and-expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))
(local (include-book "kestrel/arithmetic-light/integer-length" :dir :system))

;ffixme eventually get rid of the 32 one...

(defun leftrotate32alt (amt val)
  (let* ((amt (bvchop 5 amt) ;(mod amt 32)
              ))
    (bvcat (- 32 amt)
           (slice (- 31 amt) 0 val)
           amt
           (slice 31 (+ 32 (- amt)) val))))

;todo: consider replacing this with the leftrotate-unroller machinery below
;we split into cases, each of which calls leftrotate32alt and then open that function
(defthmd leftrotate32-cases
  (implies (natp amt) ;new
  (equal (leftrotate32 amt val)
         (BVIF 32
          (EQUAL (BVCHOP 5 AMT) '0)
          (leftrotate32alt '0 val)
          (BVIF 32
           (EQUAL (BVCHOP 5 AMT) '1)
           (leftrotate32alt '1 val)
           (BVIF 32
            (EQUAL (BVCHOP 5 AMT) '2)
            (leftrotate32alt '2 val)
            (BVIF 32
             (EQUAL (BVCHOP 5 AMT) '3)
             (leftrotate32alt '3 val)
             (BVIF 32
              (EQUAL (BVCHOP 5 AMT) '4)
              (leftrotate32alt '4 val)
              (BVIF 32
               (EQUAL (BVCHOP 5 AMT) '5)
               (leftrotate32alt '5 val)
               (BVIF 32
                (EQUAL (BVCHOP 5 AMT) '6)
                (leftrotate32alt '6 val)
                (BVIF 32
                 (EQUAL (BVCHOP 5 AMT) '7)
                 (leftrotate32alt '7 val)
                 (BVIF 32
                  (EQUAL (BVCHOP 5 AMT) '8)
                  (leftrotate32alt '8 val)
                  (BVIF 32
                   (EQUAL (BVCHOP 5 AMT) '9)
                   (leftrotate32alt '9 val)
                   (BVIF 32
                    (EQUAL (BVCHOP 5 AMT) '10)
                    (leftrotate32alt '10 val)
                    (BVIF 32
                     (EQUAL (BVCHOP 5 AMT) '11)
                     (leftrotate32alt '11 val)
                     (BVIF 32
                      (EQUAL (BVCHOP 5 AMT) '12)
                      (leftrotate32alt '12 val)
                      (BVIF 32
                       (EQUAL (BVCHOP 5 AMT) '13)
                       (leftrotate32alt '13 val)
                       (BVIF 32
                        (EQUAL (BVCHOP 5 AMT) '14)
                        (leftrotate32alt '14 val)
                        (BVIF 32
                         (EQUAL (BVCHOP 5 AMT) '15)
                         (leftrotate32alt '15 val)
                         (BVIF 32
                          (EQUAL (BVCHOP 5 AMT) '16)
                          (leftrotate32alt '16 val)
                          (BVIF 32
                           (EQUAL (BVCHOP 5 AMT) '17)
                           (leftrotate32alt '17 val)
                           (BVIF 32
                            (EQUAL (BVCHOP 5 AMT) '18)
                            (leftrotate32alt '18 val)
                            (BVIF 32
                             (EQUAL (BVCHOP 5 AMT) '19)
                             (leftrotate32alt '19 val)
                             (BVIF 32
                              (EQUAL (BVCHOP 5 AMT) '20)
                              (leftrotate32alt '20 val)
                              (BVIF 32
                               (EQUAL (BVCHOP 5 AMT) '21)
                               (leftrotate32alt '21 val)
                               (BVIF 32
                                (EQUAL (BVCHOP 5 AMT) '22)
                                (leftrotate32alt '22 val)
                                (BVIF 32
                                 (EQUAL (BVCHOP 5 AMT) '23)
                                 (leftrotate32alt '23 val)
                                 (BVIF 32
                                  (EQUAL (BVCHOP 5 AMT) '24)
                                  (leftrotate32alt '24 val)
                                  (BVIF 32
                                   (EQUAL (BVCHOP 5 AMT) '25)
                                   (leftrotate32alt '25 val)
                                   (BVIF 32
                                    (EQUAL (BVCHOP 5 AMT) '26)
                                    (leftrotate32alt '26 val)
                                    (BVIF 32
                                     (EQUAL (BVCHOP 5 AMT) '27)
                                     (leftrotate32alt '27 val)
                                     (BVIF 32
                                      (EQUAL (BVCHOP 5 AMT) '28)
                                      (leftrotate32alt '28 val)
                                      (BVIF 32 (EQUAL (BVCHOP 5 AMT) '29)
                                          (leftrotate32alt '29 val)
                                          (BVIF 32 (EQUAL (BVCHOP 5 AMT) '30)
                                              (leftrotate32alt '30 val)
                                              (leftrotate32alt '31 val))))))))))))))))))))))))))))))))))
  :hints (("Goal" :expand (:with bvchop (BVCHOP 5 AMT))
           :in-theory (enable leftrotate32alt leftrotate32 leftrotate bvif))))

;this one will be opened up
(defun rightrotate32alt (amt val)
  (let* ((amt (bvchop 5 amt)))
        (bvcat amt (slice (+ -1 amt) 0 val)
               (- 32 amt)
               (slice 32 amt val))))

;yuck!?
(defthmd rightrotate32-cases
  (implies (natp amt) ;new
  (equal (rightrotate32 amt val)
         (BVIF 32
          (EQUAL (BVCHOP 5 AMT) '0)
          (rightrotate32alt '0 val)
          (BVIF 32
           (EQUAL (BVCHOP 5 AMT) '1)
           (rightrotate32alt '1 val)
           (BVIF 32
            (EQUAL (BVCHOP 5 AMT) '2)
            (rightrotate32alt '2 val)
            (BVIF 32
             (EQUAL (BVCHOP 5 AMT) '3)
             (rightrotate32alt '3 val)
             (BVIF 32
              (EQUAL (BVCHOP 5 AMT) '4)
              (rightrotate32alt '4 val)
              (BVIF 32
               (EQUAL (BVCHOP 5 AMT) '5)
               (rightrotate32alt '5 val)
               (BVIF 32
                (EQUAL (BVCHOP 5 AMT) '6)
                (rightrotate32alt '6 val)
                (BVIF 32
                 (EQUAL (BVCHOP 5 AMT) '7)
                 (rightrotate32alt '7 val)
                 (BVIF 32
                  (EQUAL (BVCHOP 5 AMT) '8)
                  (rightrotate32alt '8 val)
                  (BVIF 32
                   (EQUAL (BVCHOP 5 AMT) '9)
                   (rightrotate32alt '9 val)
                   (BVIF 32
                    (EQUAL (BVCHOP 5 AMT) '10)
                    (rightrotate32alt '10 val)
                    (BVIF 32
                     (EQUAL (BVCHOP 5 AMT) '11)
                     (rightrotate32alt '11 val)
                     (BVIF 32
                      (EQUAL (BVCHOP 5 AMT) '12)
                      (rightrotate32alt '12 val)
                      (BVIF 32
                       (EQUAL (BVCHOP 5 AMT) '13)
                       (rightrotate32alt '13 val)
                       (BVIF 32
                        (EQUAL (BVCHOP 5 AMT) '14)
                        (rightrotate32alt '14 val)
                        (BVIF 32
                         (EQUAL (BVCHOP 5 AMT) '15)
                         (rightrotate32alt '15 val)
                         (BVIF 32
                          (EQUAL (BVCHOP 5 AMT) '16)
                          (rightrotate32alt '16 val)
                          (BVIF 32
                           (EQUAL (BVCHOP 5 AMT) '17)
                           (rightrotate32alt '17 val)
                           (BVIF 32
                            (EQUAL (BVCHOP 5 AMT) '18)
                            (rightrotate32alt '18 val)
                            (BVIF 32
                             (EQUAL (BVCHOP 5 AMT) '19)
                             (rightrotate32alt '19 val)
                             (BVIF 32
                              (EQUAL (BVCHOP 5 AMT) '20)
                              (rightrotate32alt '20 val)
                              (BVIF 32
                               (EQUAL (BVCHOP 5 AMT) '21)
                               (rightrotate32alt '21 val)
                               (BVIF 32
                                (EQUAL (BVCHOP 5 AMT) '22)
                                (rightrotate32alt '22 val)
                                (BVIF 32
                                 (EQUAL (BVCHOP 5 AMT) '23)
                                 (rightrotate32alt '23 val)
                                 (BVIF 32
                                  (EQUAL (BVCHOP 5 AMT) '24)
                                  (rightrotate32alt '24 val)
                                  (BVIF 32
                                   (EQUAL (BVCHOP 5 AMT) '25)
                                   (rightrotate32alt '25 val)
                                   (BVIF 32
                                    (EQUAL (BVCHOP 5 AMT) '26)
                                    (rightrotate32alt '26 val)
                                    (BVIF 32
                                     (EQUAL (BVCHOP 5 AMT) '27)
                                     (rightrotate32alt '27 val)
                                     (BVIF 32
                                      (EQUAL (BVCHOP 5 AMT) '28)
                                      (rightrotate32alt '28 val)
                                      (BVIF 32 (EQUAL (BVCHOP 5 AMT) '29)
                                          (rightrotate32alt '29 val)
                                          (BVIF 32 (EQUAL (BVCHOP 5 AMT) '30)
                                              (rightrotate32alt '30 val)
                                              (rightrotate32alt '31 val))))))))))))))))))))))))))))))))))
  :hints (("Goal"  :expand (:with bvchop (BVCHOP 5 AMT))
           :in-theory (enable rightrotate32alt rightrotate32 rightrotate bvif))))

;move these:

(defthm unsigned-byte-of-lg
  (implies (and (< amt width)
                (power-of-2p width)
                (natp width))
           (equal (unsigned-byte-p (lg width) amt)
                  (natp amt)))
  :hints (("Goal" :in-theory (enable unsigned-byte-p lg power-of-2p))))

(defthm bvchop-of-lg-when-power-of-2p
  (implies (power-of-2p width)
           (equal (bvchop (lg width) width)
                  0))
  :hints (("Goal" :in-theory (enable power-of-2p lg))))

(defthm rightrotate-becomes-leftrotate
  (implies (and (power-of-2p width)
                (< amt width)
                (natp amt)
                (natp width))
           (equal (rightrotate width amt val)
                  (leftrotate width (- width amt) val)))
  :hints (("Goal" :cases ((equal 0 amt))
           :in-theory (enable rightrotate leftrotate))))

(defthm rightrotate32-becomes-leftrotate32
  (implies (and (natp amt)
                (< amt 32) ;drop?
                )
           (equal (rightrotate32 amt val)
                  (leftrotate32 (bvminus 5 0 amt) ;do we really want bvminus here?
                                val)))
  :hints (("Goal" :in-theory (enable bvminus leftrotate32 rightrotate32))))

;; (defthm unsigned-byte-p-of-leftrotate
;;   (implies (and (<= size size2)
;;                 (integerp size2))
;;           (unsigned-byte-p size2 (leftrotate size x y))
;;                   ))
;;   :hints (("Goal" :in-theory (enable leftrotate))))

(defthm equal-of-constant-and-leftrotate
  (implies (and (syntaxp (quotep k))
                (natp amt)
                (< amt 32) ;gen (maybe gen RIGHTROTATE-BECOMES-LEFTROTATE too)
                )
           (equal (equal k (leftrotate 32 amt val))
                  (and (unsigned-byte-p 32 k)
                       (equal (rightrotate32 amt k) (bvchop 32 val)))))
  :hints (("Goal"
           :in-theory (enable leftrotate rightrotate32))))

(defthm equal-of-constant-and-leftrotate32
  (implies (and (syntaxp (quotep k))
                (natp amt)
                (< amt 32))
           (equal (equal k (leftrotate32 amt val))
                  (and (unsigned-byte-p 32 k)
                       (equal (rightrotate32 amt k)
                              (bvchop 32 val)))))
  :hints (("Goal" :use equal-of-constant-and-leftrotate
           :in-theory (e/d (leftrotate32 rightrotate32 natp) (equal-of-constant-and-leftrotate)))))

;; maybe there is not a nice blast rule.  just use the definition?
;; (defthm leftrotate-blast
;;   (implies (and (posp width)
;;                 (< amt width)
;;                 (natp amt))
;;            (equal (leftrotate width amt val)
;;                   (bvcat 1
;;                          (getbit (+ -1 (- amt) width) val)
;;                          (+ -1 width)
;;                          y)))
;;   :hints (("Goal" :in-theory (enable leftrotate))))

;gen the non-32 one too..
(defthm rightrotate32-becomes-leftrotate32-gen
  (implies (natp amt)
           (equal (rightrotate32 amt val)
                  (leftrotate32 (bvminus 5 0 amt) val)))
  :hints (("Goal" :in-theory (enable bvminus rightrotate32
                                     leftrotate32
                                     leftrotate
                                     rightrotate
                                     mod-becomes-bvchop-when-power-of-2p))))

(defthm leftrotate32-of-leftrotate32
  (implies (and (natp k1)
                (natp k2))
           (equal (leftrotate32 k1 (leftrotate32 k2 x))
                  (leftrotate32 (bvplus 5 k1 k2) x)))
  :hints (("Goal" :in-theory (enable leftrotate32
                                     ;leftrotate
                                     ;;natp bvchop-of-sum-cases
                                     bvplus
                                     ))))

;see leftrotate32-of-leftrotate32
;; (defthm leftrotate32-of-bvuminus-and-leftrotate32
;;   (implies (natp amt)
;;            (equal (leftrotate32 (bvuminus '5 amt) (leftrotate32 amt val))
;;                   (bvchop 32 val)))
;;   :hints (("Goal" :in-theory (e/d (leftrotate32 leftrotate bvuminus bvminus) (bvminus-becomes-bvplus-of-bvuminus)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only intended for rewriting when we want to split a rotate into cases.
(defund leftrotate-unroller (n width amt val)
  (if (zp n)
      (leftrotate width 0 val) ; just bvchop?
    (if (equal n amt)
        (leftrotate width n val)
      (leftrotate-unroller (+ -1 n) width amt val))))

(defthm leftrotate-unroller-opener
  (implies (and (syntaxp (quotep n))
                (natp n))
           (equal (leftrotate-unroller n width amt val)
                  (if (equal 0 n) ; avoids zp here in case the evaluator doesn't support it
                      (leftrotate width 0 val)
                    (if (equal n amt)
                        (leftrotate width n val)
                      (leftrotate-unroller (+ -1 n) width amt val)))))
  :hints (("Goal" :in-theory (enable leftrotate-unroller))))

(local
 (defthm leftrotate-unroller-of-0-arg2
   (equal (leftrotate-unroller n 0 amt val)
          0)
   :hints (("Goal" :in-theory (enable leftrotate-unroller)))))

;; (thm
;;  (implies (and (natp amt)
;;                (natp n))
;;           (equal (leftrotate-unroller n width (mod amt width) val)
;;                  (leftrotate-unroller n width amt val)))
;;  :hints (("Goal" :in-theory (enable leftrotate-unroller))))

(local
 (defthmd leftrotate-unroller-intro-helper
   (implies (and (<= amt n)
                 (natp amt)
                 (natp n))
            (equal (leftrotate width amt val)
                   (leftrotate-unroller n width amt val)))
   :hints (("Goal" :in-theory (enable leftrotate-unroller)))))

;; When the shift amount is not a constant, split into possible cases.  We
;; expect leftrotate-unroller-opener to fire next.
;; This one puts a MOD around the amt.
;todo: compare to the rule just below
(defthmd leftrotate-becomes-leftrotate-unroller
  (implies (and (syntaxp (and (not (quotep amt)) ; avoids loops, goal is to make all amounts be quoteps
                              (quotep width)))
                (<= amt width)
                (natp amt)
                (natp width))
           (equal (leftrotate width amt val)
                  (leftrotate-unroller width ;(+ -1 width)
                                       width amt val)))
  :hints (("Goal" :in-theory (enable leftrotate-unroller-intro-helper))))

;; This one requires showing that (<= amt width).
;; When the shift amount is not a constant, split into possible cases.  We
;; expect leftrotate-unroller-opener to fire next.  TODO: Do we need cases for
;; both the shift amount itself and 0?
(defthmd leftrotate-becomes-leftrotate-unroller-strong
  (implies (and (syntaxp (and (not (quotep amt)) ; avoids loops, goal is to make all amounts be quoteps
                              (quotep width)))
                (natp amt)
                (natp width))
           (equal (leftrotate width amt val)
                  (leftrotate-unroller (+ -1 width) width (mod amt width) val))) ; or use bvmod? or bvchop (if power of 2)
  :hints (("Goal" :cases ((equal 0 width))
           :use (:instance leftrotate-unroller-intro-helper
                           (amt (mod amt width))
                           (n (+ -1 width))))))

;; Special case when width is a power of 2
(defthmd leftrotate-becomes-leftrotate-unroller-strong2
  (implies (and (syntaxp (and (not (quotep amt)) ; avoids loops, goal is to make all amounts be quoteps
                              (quotep width)))
                (power-of-2p width)
                (natp amt)
                (natp width))
           (equal (leftrotate width amt val)
                  (leftrotate-unroller (+ -1 width) width (bvchop (lg width) amt) val)))
  :hints (("Goal" :cases ((equal 0 width))
           :in-theory (enable bvchop)
           :use (:instance leftrotate-unroller-intro-helper
                           (amt (mod amt width))
                           (n (+ -1 width))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Only intended for rewriting when we want to split a rotate into cases.
(defund rightrotate-unroller (n width amt val)
  (if (zp n)
      (rightrotate width 0 val) ; just bvchop?
    (if (equal n amt)
        (rightrotate width n val)
      (rightrotate-unroller (+ -1 n) width amt val))))

(defthm rightrotate-unroller-opener
  (implies (and (syntaxp (quotep n))
                (natp n))
           (equal (rightrotate-unroller n width amt val)
                  (if (equal 0 n) ; avoids zp here in case the evaluator doesn't support it
                      (rightrotate width 0 val)
                    (if (equal n amt)
                        (rightrotate width n val)
                      (rightrotate-unroller (+ -1 n) width amt val)))))
  :hints (("Goal" :in-theory (enable rightrotate-unroller))))

(local
 (defthm rightrotate-unroller-of-0-arg2
   (equal (rightrotate-unroller n 0 amt val)
          0)
   :hints (("Goal" :in-theory (enable rightrotate-unroller)))))

;; (thm
;;  (implies (and (natp amt)
;;                (natp n))
;;           (equal (rightrotate-unroller n width (mod amt width) val)
;;                  (rightrotate-unroller n width amt val)))
;;  :hints (("Goal" :in-theory (enable rightrotate-unroller))))

(local
 (defthmd rightrotate-unroller-intro-helper
   (implies (and (<= amt n)
                 (natp amt)
                 (natp n))
            (equal (rightrotate width amt val)
                   (rightrotate-unroller n width amt val)))
   :hints (("Goal" :in-theory (enable rightrotate-unroller)))))

;; This one requires showing that (<= amt width).
;; When the shift amount is not a constant, split into possible cases.  We
;; expect rightrotate-unroller-opener to fire next.  TODO: Do we need cases for
;; both the shift amount itself and 0?
(defthmd rightrotate-becomes-rightrotate-unroller
  (implies (and (syntaxp (and (not (quotep amt)) ; avoids loops, goal is to make all amounts be quoteps
                              (quotep width)))
                (<= amt width)
                (natp amt)
                (natp width))
           (equal (rightrotate width amt val)
                  (rightrotate-unroller width ;(+ -1 width)
                                       width amt val)))
  :hints (("Goal" :in-theory (enable rightrotate-unroller-intro-helper))))

;; When the shift amount is not a constant, split into possible cases.  We
;; expect rightrotate-unroller-opener to fire next.
;; This one puts a MOD around the amt.
;todo: compare to the rule just below
(defthmd rightrotate-becomes-rightrotate-unroller-strong
  (implies (and (syntaxp (and (not (quotep amt)) ; avoids loops, goal is to make all amounts be quoteps
                              (quotep width)))
                (natp amt)
                (natp width))
           (equal (rightrotate width amt val)
                  (rightrotate-unroller (+ -1 width) width (mod amt width) val))) ; or use bvmod? or bvchop (if power of 2)
  :hints (("Goal" :cases ((equal 0 width))
           :use (:instance rightrotate-unroller-intro-helper
                           (amt (mod amt width))
                           (n (+ -1 width))))))

;; Special case when WIDTH is a power of 2, so we can use bvchop instead of mod around AMT.
(defthmd rightrotate-becomes-rightrotate-unroller-strong2
  (implies (and (syntaxp (and (not (quotep amt)) ; avoids loops, goal is to make all amounts be quoteps
                              (quotep width)))
                (power-of-2p width)
                (natp amt)
                (natp width))
           (equal (rightrotate width amt val)
                  (rightrotate-unroller (+ -1 width) width (bvchop (lg width) amt) val)))
  :hints (("Goal" :cases ((equal 0 width))
           :in-theory (e/d (bvchop) (rightrotate-becomes-leftrotate))
           :use (:instance rightrotate-unroller-intro-helper
                           (amt (mod amt width))
                           (n (+ -1 width))))))
