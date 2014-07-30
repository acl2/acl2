; Copyright (C) 2013, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This total order book, put together by Matt Kaufmann, is culled from events
; contributed by Pete Manolios and also benefits from contributions by Rob
; Sumners.

; Modified 2013-01-15 by Jared Davis to add FAST- functions and correctness
; proofs, for compatibility with the GPL'd total-order book.

; History: Originally this book was derived from a version of total-order.lisp,
; but avoiding dependence on xdoc/top since that book was GPL'ed.  Now that
; xdoc/top has a BSD-style license that concern is gone, but it seems simplest
; to leave this book in place and add that license to total-order.lisp.

(in-package "ACL2")

(encapsulate
  ()
  (local (in-theory (enable alphorder)))

  (defun fast-alphorder (x y)
    (declare (xargs :guard (and (atom x) (atom y))))
    (mbe :logic (alphorder x y)
         :exec
         (cond ((integerp x)
                (cond ((integerp y)
                       (<= x y))
                      ((real/rationalp y)
                       (<= x y))
                      (t
                       t)))

               ((symbolp x)
                (if (symbolp y)
                    ;; Doing an EQ check here costs relatively very
                    ;; little.  After all, we're about to do a function
                    ;; call and two string compares.  And if it hits,
                    ;; it's a big win.
                    (or (eq x y)
                        (not (symbol-< y x)))
                  ;; Ugh.  We should just know this is true, but we have
                  ;; to consider these cases because of bad atoms:
                  (not (or (integerp y)
                           (stringp y)
                           (characterp y)
                           (real/rationalp y)
                           (complex/complex-rationalp y)))))

               ((stringp x)
                (cond ((stringp y)
                       (and (string<= x y) t))
                      ((integerp y)
                       nil)
                      ((symbolp y)
                       t)
                      (t
                       (not (or (characterp y)
                                (real/rationalp y)
                                (complex/complex-rationalp y))))))

               ((characterp x)
                (cond ((characterp y)
                       (<= (char-code x) (char-code y)))
                      (t
                       (not (or (integerp y)
                                (real/rationalp y)
                                (complex/complex-rationalp y))))))

               ((real/rationalp x)
                (cond ((integerp y)
                       (<= x y))
                      ((real/rationalp y)
                       (<= x y))
                      (t t)))

               ((real/rationalp y)
                nil)

               ((complex/complex-rationalp x)
                (cond ((complex/complex-rationalp y)
                       (or (< (realpart x)
                              (realpart y))
                           (and (= (realpart x)
                                   (realpart y))
                                (<= (imagpart x)
                                    (imagpart y)))))
                      (t t)))

               ;; Ugly, just need this in case of bad-atoms.
               ((or (symbolp y)
                    (stringp y)
                    (characterp y)
                    (complex/complex-rationalp y))
                nil)

               (t
                (acl2::bad-atom<= x y))))))


(encapsulate
  ()
  (defund fast-lexorder (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if (atom y)

               ;; Inlined, rearranged alphorder.
               (cond ((integerp x)
                      (cond ((integerp y)
                             (<= x y))
                            ((real/rationalp y)
                             (<= x y))
                            (t
                             t)))

                     ((symbolp x)
                      (if (symbolp y)
                          ;; Doing an EQ check here costs relatively very
                          ;; little.  After all, we're about to do a function
                          ;; call and two string compares.  And if it hits,
                          ;; it's a big win.
                          (or (eq x y)
                              (not (symbol-< y x)))
                        ;; Ugh.  We should just know this is true, but we have
                        ;; to consider these cases because of bad atoms:
                        (not (or (integerp y)
                                 (stringp y)
                                 (characterp y)
                                 (real/rationalp y)
                                 (complex/complex-rationalp y)))))

                     ((stringp x)
                      (cond ((stringp y)
                             (and (string<= x y) t))
                            ((integerp y)
                             nil)
                            ((symbolp y)
                             t)
                            (t
                             (not (or (characterp y)
                                      (real/rationalp y)
                                      (complex/complex-rationalp y))))))

                     ((characterp x)
                      (cond ((characterp y)
                             (<= (char-code x) (char-code y)))
                            (t
                             (not (or (integerp y)
                                      (real/rationalp y)
                                      (complex/complex-rationalp y))))))

                     ((real/rationalp x)
                      (cond ((integerp y)
                             (<= x y))
                            ((real/rationalp y)
                             (<= x y))
                            (t t)))

                     ((real/rationalp y)
                      nil)

                     ((complex/complex-rationalp x)
                      (cond ((complex/complex-rationalp y)
                             (or (< (realpart x)
                                    (realpart y))
                                 (and (= (realpart x)
                                         (realpart y))
                                      (<= (imagpart x)
                                          (imagpart y)))))
                            (t t)))

                     ;; Ugly, just need this in case of bad-atoms.
                     ((or (symbolp y)
                          (stringp y)
                          (characterp y)
                          (complex/complex-rationalp y))
                      nil)

                     (t
                      (acl2::bad-atom<= x y)))

             ;; (atom x) and not (atom y)
             t))
          ((atom y)
           nil)
          ((equal (car x) (car y))
           (fast-lexorder (cdr x) (cdr y)))
          (t
           (fast-lexorder (car x) (car y)))))

  (local (in-theory (enable fast-lexorder lexorder alphorder)))

  (defthm fast-lexorder-is-lexorder
    (equal (fast-lexorder x y)
           (lexorder x y))))


(encapsulate
  ()
  (defund fast-<< (x y)
    (declare (xargs :guard t))
    (cond ((atom x)
           (if (atom y)
               (cond ((integerp x)
                      (cond ((integerp y)
                             (< x y))
                            ((real/rationalp y)
                             (< x y))
                            (t
                             t)))
                     ((symbolp x)
                      (if (symbolp y)
                          (and (not (eq x y))
                               (symbol-< x y)
                               t)
                        (not (or (integerp y)
                                 (stringp y)
                                 (characterp y)
                                 (real/rationalp y)
                                 (complex/complex-rationalp y)))))
                     ((stringp x)
                      (cond ((stringp y)
                             (and (string< x y) t))
                            ((integerp y)
                             nil)
                            ((symbolp y)
                             t)
                            (t
                             (not (or (characterp y)
                                      (real/rationalp y)
                                      (complex/complex-rationalp y))))))
                     ((characterp x)
                      (cond ((characterp y)
                             (< (char-code x) (char-code y)))
                            (t
                             (not (or (integerp y)
                                      (real/rationalp y)
                                      (complex/complex-rationalp y))))))
                     ((real/rationalp x)
                      (cond ((integerp y)
                             (< x y))
                            ((real/rationalp y)
                             (< x y))
                            (t t)))
                     ((real/rationalp y)
                      nil)
                     ((complex/complex-rationalp x)
                      (cond ((complex/complex-rationalp y)
                             (or (< (realpart x)
                                    (realpart y))
                                 (and (= (realpart x)
                                         (realpart y))
                                      (< (imagpart x)
                                         (imagpart y)))))
                            (t t)))
                     ((or (symbolp y)
                          (stringp y)
                          (characterp y)
                          (complex/complex-rationalp y))
                      nil)
                     (t
                      (and (acl2::bad-atom<= x y)
                           (not (equal x y)))))
             t))
          ((atom y)
           nil)
          ((equal (car x) (car y))
           (fast-<< (cdr x) (cdr y)))
          (t
           (fast-<< (car x) (car y))))))


(encapsulate
  ()
  (defund << (x y)
    (declare (xargs :guard t
                    :verify-guards nil))
    (mbe :logic
         (and (lexorder x y)
              (not (equal x y)))
         :exec
         (fast-<< x y)))

  (local (in-theory (enable <<)))

  (defthm <<-irreflexive
    (not (<< x x)))

  (defthm <<-transitive
    (implies (and (<< x y)
                  (<< y z))
             (<< x z)))

  (defthm <<-asymmetric
    (implies (<< x y)
             (not (<< y x))))

  (defthm <<-trichotomy
    (implies (and (not (<< y x))
                  (not (equal x y)))
             (<< x y)))

  (defthm <<-implies-lexorder
    (implies (<< x y)
             (lexorder x y))))


(encapsulate
  ()
  (local (in-theory (enable fast-<< << lexorder alphorder)))

  (local (defthm l0
           (implies (and (characterp x)
                         (characterp y))
                    (equal (equal (char-code x) (char-code y))
                           (equal x y)))
           :hints(("Goal" :use ((:instance equal-char-code))))))

  (defthm fast-<<-is-<<
    (equal (fast-<< x y)
           (<< x y))))

(verify-guards <<
  :hints(("Goal" :in-theory (enable <<))))


