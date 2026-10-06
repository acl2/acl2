; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "DATA")

(include-book "std/util/define" :dir :system)
(include-book "std/util/defrule" :dir :system)

(include-book "../fixed-size-words/fixnum")
(include-book "total-order-defs")

(local (include-book "std/basic/controlled-configuration" :dir :system))
(local (acl2::controlled-configuration :hooks nil))

(local (include-book "total-order"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Library extensions

;; A non-nil string< index is less than the length of the second string.
(defrulel string<-l-upper-bound
  (implies (and (string<-l l1 l2 i)
                (natp i))
           (< (string<-l l1 l2 i)
              (+ i (len l2))))
  :rule-classes :linear
  :induct (string<-l l1 l2 i)
  :enable string<-l
  :expand ((len l2)))

(defrulel string<-upper-bound
  (implies (and (string< x y)
                (stringp y))
           (< (string< x y)
              (length y)))
  :rule-classes :linear
  :enable (string<
           length))

;; Characters are equal exactly when their codes are.
(defrulel equal-of-char-code-and-char-code
  (implies (and (characterp x)
                (characterp y))
           (equal (equal (char-code x) (char-code y))
                  (equal x y)))
  :use (:instance equal-char-code
                  (acl2::x x)
                  (acl2::y y)))

;; Asymmetry and trichotomy of string<. On strings, << is string<, so
;; trichotomy follows from that of <<.
(defrulel string<-asymmetric
  (implies (string< x y)
           (not (string< y x)))
  :enable string<)

(defrulel string<-trichotomy
  (implies (and (not (string< x y))
                (not (equal x y))
                (stringp x)
                (stringp y))
           (string< y x))
  :use (:instance acl2::<<-trichotomy
                  (acl2::x x)
                  (acl2::y y))
  :enable (<<
           lexorder
           alphorder
           string<=))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The position of an atom's type in the order alphorder puts on atoms of
;; different types.
(define atom-type-rank (x)
  :returns (rank natp :rule-classes :type-prescription)
  (cond ((real/rationalp x) 0)
        ((complex/complex-rationalp x) 1)
        ((characterp x) 2)
        ((stringp x) 3)
        ((symbolp x) 4)
        (t 5))
  :inline t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define fast-acl2-number-compare-<<
  ((x acl2-numberp)
   (y acl2-numberp))
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (mbe :logic (mv (equal x y) (<< x y))
       :exec (cond ((real/rationalp x)
                    (if (real/rationalp y)
                        (mv (= x y) (< x y))
                      (mv nil t)))
                   ((real/rationalp y)
                    (mv nil nil))
                   (t (let ((x-real (realpart x))
                            (y-real (realpart y)))
                        (cond ((< x-real y-real) (mv nil t))
                              ((< y-real x-real) (mv nil nil))
                              (t (let ((x-imag (imagpart x))
                                       (y-imag (imagpart y)))
                                   (mv (= x-imag y-imag)
                                       (< x-imag y-imag)))))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable <<
                                           lexorder
                                           alphorder))))

;;;;;;;;;;;;;;;;;;;;

(define fast-symbol-compare-<<
  ((x symbolp)
   (y symbolp))
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (mbe :logic (mv (equal x y) (<< x y))
       :exec (let* ((x-name (symbol-name x))
                    (y-name (symbol-name y))
                    (index (string<= x-name y-name)))
               (cond ((not index) (mv nil nil))
                     ((eql index (length y-name))
                      (let* ((x-pkg (symbol-package-name x))
                             (y-pkg (symbol-package-name y))
                             (index (string<= x-pkg y-pkg)))
                        (cond ((not index) (mv nil nil))
                              ((eql index (length y-pkg)) (mv t nil))
                              (t (mv nil t)))))
                     (t (mv nil t)))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable <<
                                           lexorder
                                           alphorder
                                           symbol<
                                           string<=)
                        :use (:instance acl2::symbol-equality
                                        (acl2::s1 x)
                                        (acl2::s2 y)))))

;;;;;;;;;;;;;;;;;;;;

(define fast-eqlable-compare-<<
  ((x eqlablep)
   (y eqlablep))
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (mbe :logic (mv (equal x y) (<< x y))
       :exec (cond ((symbolp x)
                    (cond ((not (symbolp y)) (mv nil nil))
                          ((eq x y) (mv t nil))
                          (t (fast-symbol-compare-<< x y))))
                   ((acl2-numberp x)
                    (if (acl2-numberp y)
                        (fast-acl2-number-compare-<< x y)
                      (mv nil t)))
                   ;; Otherwise, x is a character.
                   ((characterp y)
                    (mv (eql x y) (char< x y)))
                   (t (mv nil (< 2 (atom-type-rank y))))))
  :enabled t
  :guard-hints (("Goal" :in-theory (enable <<
                                           lexorder
                                           alphorder
                                           atom-type-rank
                                           char<))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; On strings, we use a single string<= rather than first checking equal.
;; Although equal is faster on pointer-equal strings, testing it first was
;; slower on the string pairs compared while validating nginx, most of which
;; differ.
(define fast-compare-<< (x y)
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (cond ((consp x)
         (if (consp y)
             (mv-let (equalp ltp)
                     (fast-compare-<< (car x) (car y))
               (if equalp
                   (fast-compare-<< (cdr x) (cdr y))
                 (mv nil ltp)))
           (mv nil nil)))
        ((consp y)
         (mv nil t))
        ((and (fixnump x)
              (fixnump y))
         (mv (= (acl2::the-fixnum x) (acl2::the-fixnum y))
             (< (acl2::the-fixnum x) (acl2::the-fixnum y))))
        ((stringp x)
         (if (stringp y)
             (let ((index (string<= x y)))
               (cond ((not index) (mv nil nil))
                     ((eql index (length y)) (mv t nil))
                     (t (mv nil t))))
           (mv nil (< 3 (atom-type-rank y)))))
        ((symbolp x)
         (cond ((not (symbolp y)) (mv nil (< 4 (atom-type-rank y))))
               ((eq x y) (mv t nil))
               (t (fast-symbol-compare-<< x y))))
        ((acl2-numberp x)
         (if (acl2-numberp y)
             (fast-acl2-number-compare-<< x y)
           (mv nil t)))
        ((characterp x)
         (if (characterp y)
             (mv (eql x y) (char< x y))
           (mv nil (< 2 (atom-type-rank y)))))
        ((eql (atom-type-rank y) 5)
         (mv (equal x y)
             (and (acl2::bad-atom<= x y)
                  (not (equal x y)))))
        (t (mv nil nil)))
  :guard-hints (("Goal" :in-theory (enable atom-type-rank))))

;;;;;;;;;;;;;;;;;;;;

(defrule fast-compare-<<-becomes-mv
  (equal (fast-compare-<< x y)
         (mv (equal x y)
             (<< x y)))
  :induct t
  :enable (fast-compare-<<
           atom-type-rank
           <<
           lexorder
           alphorder
           string<=
           char<))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define compare-<< (x y)
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (mbe :logic (mv (equal x y) (<< x y))
       :exec (fast-compare-<< x y))
  :enabled t
  :inline t)

;;;;;;;;;;;;;;;;;;;;

(define acl2-number-compare-<<
  ((x acl2-numberp)
   (y acl2-numberp))
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (mbe :logic (mv (equal x y) (<< x y))
       :exec (if (and (fixnump x)
                      (fixnump y))
                 (mv (= (acl2::the-fixnum x) (acl2::the-fixnum y))
                     (< (acl2::the-fixnum x) (acl2::the-fixnum y)))
               (fast-acl2-number-compare-<< x y)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable <<
                                           lexorder
                                           alphorder))))

;;;;;;;;;;;;;;;;;;;;

(define symbol-compare-<<
  ((x symbolp)
   (y symbolp))
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (mbe :logic (mv (equal x y) (<< x y))
       :exec (if (eq x y)
                 (mv t nil)
               (fast-symbol-compare-<< x y)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable acl2::<<-irreflexive))))

;;;;;;;;;;;;;;;;;;;;

(define eqlable-compare-<<
  ((x eqlablep)
   (y eqlablep))
  :returns (mv (equalp booleanp)
               (ltp booleanp))
  (mbe :logic (mv (equal x y) (<< x y))
       :exec (if (and (fixnump x)
                      (fixnump y))
                 (mv (= (acl2::the-fixnum x) (acl2::the-fixnum y))
                     (< (acl2::the-fixnum x) (acl2::the-fixnum y)))
               (fast-eqlable-compare-<< x y)))
  :enabled t
  :inline t
  :guard-hints (("Goal" :in-theory (enable <<
                                           lexorder
                                           alphorder))))
