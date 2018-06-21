; Processing Unicode Files with ACL2
; Copyright (C) 2005-2006 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "uchar")
(include-book "utf8-table36")
(include-book "utf8-table37")
(include-book "utf8-encode")
(include-book "partition")
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/typed-lists/signed-byte-listp" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "tools/mv-nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/revappend" :dir :system))
(set-verify-guards-eagerness 2)
(set-state-ok t)

(local (defthm signed-byte-p-resolver
         (implies (and (integerp n)
                       (<= 1 n)
                       (integerp x)
                       (<= (- (expt 2 (1- n))) x)
                       (< x (expt 2 (1- n))))
                  (signed-byte-p n x))
         :hints(("Goal" :in-theory (enable signed-byte-p)))))


;; BOZO library stuff

(local
 (encapsulate
   ()
   (local (include-book "arithmetic/top" :dir :system))

   (defthm car-of-append
     (equal (car (append x y))
            (if (consp x)
                (car x)
              (car y))))

   (defthm nthcdr-of-increment-and-cons
     (implies (natp n)
              (equal (nthcdr (+ 1 n) (cons a x))
                     (nthcdr n x)))
     :hints(("Goal"
             :do-not-induct t
             :expand (nthcdr (+ 1 n) (cons a x)))))

   (defthm nthcdr-of-len-append
     (equal (nthcdr (len x) (append x y))
            y))))


;; The conversion into UTF-8 was pretty straightforward.  Unfortunately, the
;; conversion from UTF-8 is much more complicated, because we have to deal with
;; lists of bytes rather than atomic code points.
;;
;; Assume for now that we are given a single UTF-8 encoded character.  This
;; might be a list of 1-4 bytes.  We will write functions to coerce these bytes
;; back into their atomic codepoint format.
;;
;; If there is only one byte, the transformation is simply the identity
;; function.  We consider the other cases below.

(defund utf8-combine2-guard (x1 x2)
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2))
  (and (mbt (unsigned-byte-p 8 x1))
       (mbt (unsigned-byte-p 8 x2))
       (utf8-table36-byte-1/2? x1)
       (utf8-table36-trailing-byte? x2)
       (utf8-table37-bytes-2? (list x1 x2))))

(defund utf8-combine2 (x1 x2)
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2)
           (xargs :guard (utf8-combine2-guard x1 x2)))
  (let ((000yyyyy (logand (the-fixnum x1) #x1F))
        (00xxxxxx (logand (the-fixnum x2) #x3F)))
    (the-fixnum (logior (the-fixnum (ash (the-fixnum 000yyyyy) 6))
                        (the-fixnum 00xxxxxx)))))

(encapsulate
 ()

 (local (defun utf8-combine2-test1 (x1 x2)
          (declare (type (unsigned-byte 8) x1)
                   (type (unsigned-byte 8) x2))
          (let ((test (if (utf8-combine2-guard x1 x2)
                          (let ((result (utf8-combine2 x1 x2)))
                            (and (uchar? result)
                                 (utf8-table36-ok? result (list x1 x2))
                                 (utf8-table37-ok? result (list x1 x2))
                                 (equal (uchar=>utf8 result)
                                        (list x1 x2))))
                        t)))
            (and test
                 (or (zp x2)
                     (utf8-combine2-test1 x1 (1- x2)))))))

 (local (defun utf8-combine2-test (x1)
          (declare (type (unsigned-byte 8) x1))
          (let ((test (utf8-combine2-test1 x1 255)))
            (and test
                 (or (zp x1)
                     (utf8-combine2-test (1- x1)))))))

 (local (defthm lemma1
          (implies (and (utf8-combine2-test1 x1 x2)
                        (integerp x2)
                        (integerp j) (<= 0 j) (<= j x2)
                        (utf8-combine2-guard x1 j))
                   (and (uchar? (utf8-combine2 x1 j))
                        (utf8-table36-ok? (utf8-combine2 x1 j) (list x1 j))
                        (utf8-table37-ok? (utf8-combine2 x1 j) (list x1 j))
                        (equal (uchar=>utf8 (utf8-combine2 x1 j))
                               (list x1 j))))))

 (local (defthm lemma2
          (implies (and (utf8-combine2-test x1)
                        (integerp x1)
                        (integerp i) (<= 0 i) (<= i x1)
                        (integerp j) (<= 0 j) (< j 256)
                        (utf8-combine2-guard i j))
                   (and (uchar? (utf8-combine2 i j))
                        (utf8-table36-ok? (utf8-combine2 i j) (list i j))
                        (utf8-table37-ok? (utf8-combine2 i j) (list i j))
                        (equal (uchar=>utf8 (utf8-combine2 i j))
                               (list i j))))
          :hints(("Goal" :in-theory (enable utf8-combine2-guard)))))

 (comp t)

 (local (defthm lemma3
          (implies (utf8-combine2-guard x1 x2)
                   (and (uchar? (utf8-combine2 x1 x2))
                        (utf8-table36-ok? (utf8-combine2 x1 x2) (list x1 x2))
                        (utf8-table37-ok? (utf8-combine2 x1 x2) (list x1 x2))
                        (equal (uchar=>utf8 (utf8-combine2 x1 x2))
                               (list x1 x2))))
          :hints(("Goal"
                  :in-theory (enable utf8-combine2-guard
                                     unsigned-byte-p)
                  :use (:instance lemma2 (x1 255) (i x1) (j x2))))))

 (defthm uchar?-of-utf8-combine2
   (implies (utf8-combine2-guard x1 x2)
            (uchar? (utf8-combine2 x1 x2))))

 (defthm utf8-table36-ok?-of-utf8-combine2
   (implies (utf8-combine2-guard x1 x2)
            (utf8-table36-ok? (utf8-combine2 x1 x2) (list x1 x2))))

 (defthm utf8-table37-ok?-of-utf8-combine2
   (implies (utf8-combine2-guard x1 x2)
            (utf8-table37-ok? (utf8-combine2 x1 x2) (list x1 x2))))

 (defthm uchar=>utf8-of-utf8-combine2
   (implies (utf8-combine2-guard x1 x2)
            (equal (uchar=>utf8 (utf8-combine2 x1 x2))
                   (list x1 x2))))
 )



(defund utf8-combine3-guard (x1 x2 x3)
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2)
           (type (unsigned-byte 8) x3))
  (and (mbt (unsigned-byte-p 8 x1))
       (mbt (unsigned-byte-p 8 x2))
       (mbt (unsigned-byte-p 8 x3))
       (utf8-table36-byte-1/3? x1)
       (utf8-table36-trailing-byte? x2)
       (utf8-table36-trailing-byte? x3)
       (let ((bytes (list x1 x2 x3)))
         (or (utf8-table37-bytes-3? bytes)
             (utf8-table37-bytes-4? bytes)
             (utf8-table37-bytes-5? bytes)
             (utf8-table37-bytes-6? bytes)))))

(defund utf8-combine3 (x1 x2 x3)
  (declare (type (unsigned-byte 8) x1)
           (type (unsigned-byte 8) x2)
           (type (unsigned-byte 8) x3)
           (xargs :guard (utf8-combine3-guard x1 x2 x3)))
  (let ((0000zzzz (logand (the-fixnum x1) #b00001111))
        (00yyyyyy (logand (the-fixnum x2) #b00111111))
        (00xxxxxx (logand (the-fixnum x3) #b00111111)))
    (the-fixnum (logior (the-fixnum (ash (the-fixnum 0000zzzz) 12))
                        (the-fixnum (ash (the-fixnum 00yyyyyy) 6))
                        (the-fixnum 00xxxxxx)))))


(encapsulate
 ()

 (local (defun test2-utf8-combine3 (x1 x2 x3)
          (declare (type (unsigned-byte 8) x1)
                   (type (unsigned-byte 8) x2)
                   (type (unsigned-byte 8) x3))
          (let ((test (if (utf8-combine3-guard x1 x2 x3)
                          (let ((result (utf8-combine3 x1 x2 x3)))
                            (and (uchar? result)
                                 (utf8-table36-ok? result (list x1 x2 x3))
                                 (utf8-table37-ok? result (list x1 x2 x3))
                                 (equal (uchar=>utf8 (utf8-combine3 x1 x2 x3))
                                        (list x1 x2 x3))))
                        t)))
            (and test
                 (or (zp x3)
                     (test2-utf8-combine3 x1 x2 (1- x3)))))))

 (local (defun test1-utf8-combine3 (x1 x2)
          (declare (type (unsigned-byte 8) x1)
                   (type (unsigned-byte 8) x2))
          (let ((test (test2-utf8-combine3 x1 x2 255)))
            (and test
                 (or (zp x2)
                     (test1-utf8-combine3 x1 (1- x2)))))))

 (local (defun test-utf8-combine3 (x1)
          (declare (type (unsigned-byte 8) x1))
          (let ((test (test1-utf8-combine3 x1 255)))
            (and test
                 (or (zp x1)
                     (test-utf8-combine3 (1- x1)))))))

 (local (defthm lemma
          (implies (and (test2-utf8-combine3 x1 x2 x3)
                        (integerp x3)
                        (integerp k) (<= 0 k) (<= k x3)
                        (utf8-combine3-guard x1 x2 k))
                   (and (uchar? (utf8-combine3 x1 x2 k))
                        (utf8-table36-ok? (utf8-combine3 x1 x2 k)
                                          (list x1 x2 k))
                        (utf8-table37-ok? (utf8-combine3 x1 x2 k)
                                          (list x1 x2 k))
                        (equal (uchar=>utf8 (utf8-combine3 x1 x2 k))
                               (list x1 x2 k))))))

 (local (defthm lemma2
          (implies (and (test1-utf8-combine3 x1 x2)
                        (integerp x2)
                        (integerp j) (<= 0 j) (<= j x2)
                        (integerp k) (<= 0 k) (< k 256)
                        (utf8-combine3-guard x1 j k))
                   (and (uchar? (utf8-combine3 x1 j k))
                        (utf8-table36-ok? (utf8-combine3 x1 j k)
                                          (list x1 j k))
                        (utf8-table37-ok? (utf8-combine3 x1 j k)
                                          (list x1 j k))
                        (equal (uchar=>utf8 (utf8-combine3 x1 j k))
                               (list x1 j k))))
          :hints(("Goal" :in-theory (enable utf8-combine3-guard)))))

 (local (defthm lemma3
          (implies (and (test-utf8-combine3 x1)
                        (integerp x1)
                        (integerp i) (<= 0 i) (<= i x1)
                        (integerp j) (<= 0 j) (< j 256)
                        (integerp k) (<= 0 k) (< k 256)
                        (utf8-combine3-guard i j k))
                   (and (uchar? (utf8-combine3 i j k))
                        (utf8-table36-ok? (utf8-combine3 i j k)
                                          (list i j k))
                        (utf8-table37-ok? (utf8-combine3 i j k)
                                          (list i j k))
                        (equal (uchar=>utf8 (utf8-combine3 i j k))
                               (list i j k))))
          :hints(("Goal" :in-theory (enable utf8-combine3-guard)))))

 (comp t)

 (local (defthm lemma4
          (implies (utf8-combine3-guard x1 x2 x3)
                   (and (uchar? (utf8-combine3 x1 x2 x3))
                        (utf8-table36-ok? (utf8-combine3 x1 x2 x3)
                                          (list x1 x2 x3))
                        (utf8-table37-ok? (utf8-combine3 x1 x2 x3)
                                          (list x1 x2 x3))
                        (equal (uchar=>utf8 (utf8-combine3 x1 x2 x3))
                               (list x1 x2 x3))))
          :hints(("Goal"
                  :in-theory (enable utf8-combine3-guard unsigned-byte-p)
                  :use (:instance lemma3 (x1 255) (i x1) (j x2) (k x3))))))

 (defthm uchar?-of-utf8-combine3
   (implies (utf8-combine3-guard x1 x2 x3)
            (uchar? (utf8-combine3 x1 x2 x3))))

 (defthm utf8-table36-ok?-of-utf8-combine3
   (implies (utf8-combine3-guard x1 x2 x3)
            (utf8-table36-ok? (utf8-combine3 x1 x2 x3) (list x1 x2 x3))))

 (defthm utf8-table37-ok?-of-utf8-combine3
   (implies (utf8-combine3-guard x1 x2 x3)
            (utf8-table37-ok? (utf8-combine3 x1 x2 x3) (list x1 x2 x3))))

 (defthm uchar=>utf8-of-utf8-combine3
   (implies (utf8-combine3-guard x1 x2 x3)
            (equal (uchar=>utf8 (utf8-combine3 x1 x2 x3))
                   (list x1 x2 x3))))

 )



(encapsulate
 ()

 (defund utf8-combine4-guard (x1 x2 x3 x4)
   (declare (type (unsigned-byte 8) x1)
            (type (unsigned-byte 8) x2)
            (type (unsigned-byte 8) x3)
            (type (unsigned-byte 8) x4))
   (and (mbt (unsigned-byte-p 8 x1))
        (mbt (unsigned-byte-p 8 x2))
        (mbt (unsigned-byte-p 8 x3))
        (mbt (unsigned-byte-p 8 x4))
        (utf8-table36-byte-1/4? x1)
        (utf8-table36-trailing-byte? x2)
        (utf8-table36-trailing-byte? x3)
        (utf8-table36-trailing-byte? x4)
        (let ((bytes (list x1 x2 x3 x4)))
          (or (utf8-table37-bytes-7? bytes)
              (utf8-table37-bytes-8? bytes)
              (utf8-table37-bytes-9? bytes)))))

 (defund utf8-combine4 (x1 x2 x3 x4)
   (declare (type (unsigned-byte 8) x1)
            (type (unsigned-byte 8) x2)
            (type (unsigned-byte 8) x3)
            (type (unsigned-byte 8) x4)
            (xargs :guard (utf8-combine4-guard x1 x2 x3 x4)))
   (let ((00000uuu (logand (the-fixnum x1) #b00000111))
         (00uuzzzz (logand (the-fixnum x2) #b00111111))
         (00yyyyyy (logand (the-fixnum x3) #b00111111))
         (00xxxxxx (logand (the-fixnum x4) #b00111111)))
     (the-fixnum (logior (the-fixnum (ash (the-fixnum 00000uuu) 18))
                         (the-fixnum (ash (the-fixnum 00uuzzzz) 12))
                         (the-fixnum (ash (the-fixnum 00yyyyyy) 6))
                         (the-fixnum 00xxxxxx)))))

 (local (defun test3-utf8-combine4 (x1 x2 x3 x4)
          (declare (type (unsigned-byte 8) x1)
                   (type (unsigned-byte 8) x2)
                   (type (unsigned-byte 8) x3)
                   (type (unsigned-byte 8) x4))
          (let ((test (if (utf8-combine4-guard x1 x2 x3 x4)
                          (let ((result (utf8-combine4 x1 x2 x3 x4)))
                            (and (uchar? result)
                                 (utf8-table36-ok? result (list x1 x2 x3 x4))
                                 (utf8-table37-ok? result (list x1 x2 x3 x4))
                                 (equal (uchar=>utf8
                                         (utf8-combine4 x1 x2 x3 x4))
                                        (list x1 x2 x3 x4))))
                        t)))
            (and (or test
                     (cw "Error: (test3-utf8-combine4 ~x0 ~x1 ~x2 ~x3)~%"
                         x1 x2 x3 x4))
                 (or (zp x4)
                     (test3-utf8-combine4 x1 x2 x3 (1- x4)))))))

 (local (defun test2-utf8-combine4 (x1 x2 x3)
          (declare (type (unsigned-byte 8) x1)
                   (type (unsigned-byte 8) x2)
                   (type (unsigned-byte 8) x3))
          (let ((test (test3-utf8-combine4 x1 x2 x3 255)))
            (and test
                 (or (zp x3)
                     (test2-utf8-combine4 x1 x2 (1- x3)))))))

 (local (defun test1-utf8-combine4 (x1 x2)
          (declare (type (unsigned-byte 8) x1)
                   (type (unsigned-byte 8) x2))
          (let ((test (test2-utf8-combine4 x1 x2 255)))
            (and test
                 (or (zp x2)
                     (test1-utf8-combine4 x1 (1- x2)))))))

 (local (defun test-utf8-combine4 (x1)
          (declare (type (unsigned-byte 8) x1))
          (let ((test (test1-utf8-combine4 x1 255)))
            (and test
                 (or (zp x1)
                     (test-utf8-combine4 (1- x1)))))))

 (local (defthm lemma
          (implies (and (test3-utf8-combine4 x1 x2 x3 x4)
                        (integerp x4)
                        (integerp m) (<= 0 m) (<= m x4)
                        (utf8-combine4-guard x1 x2 x3 m))
                   (and (uchar? (utf8-combine4 x1 x2 x3 m))
                        (utf8-table36-ok? (utf8-combine4 x1 x2 x3 m)
                                          (list x1 x2 x3 m))
                        (utf8-table37-ok? (utf8-combine4 x1 x2 x3 m)
                                          (list x1 x2 x3 m))
                        (equal (uchar=>utf8 (utf8-combine4 x1 x2 x3 m))
                               (list x1 x2 x3 m))))))

 (local (defthm lemma2
          (implies (and (test2-utf8-combine4 x1 x2 x3)
                        (integerp x3)
                        (integerp k) (<= 0 k) (<= k x3)
                        (integerp m) (<= 0 m) (< m 256)
                        (utf8-combine4-guard x1 x2 k m))
                   (and (uchar? (utf8-combine4 x1 x2 k m))
                        (utf8-table36-ok? (utf8-combine4 x1 x2 k m)
                                          (list x1 x2 k m))
                        (utf8-table37-ok? (utf8-combine4 x1 x2 k m)
                                          (list x1 x2 k m))
                        (equal (uchar=>utf8 (utf8-combine4 x1 x2 k m))
                               (list x1 x2 k m))))
          :hints(("Goal" :in-theory (enable utf8-combine4-guard)))))

 (local (defthm lemma3
          (implies (and (test1-utf8-combine4 x1 x2)
                        (integerp x2)
                        (integerp j) (<= 0 j) (<= j x2)
                        (integerp k) (<= 0 k) (< k 256)
                        (integerp m) (<= 0 m) (< m 256)
                        (utf8-combine4-guard x1 j k m))
                   (and (uchar? (utf8-combine4 x1 j k m))
                        (utf8-table36-ok? (utf8-combine4 x1 j k m)
                                          (list x1 j k m))
                        (utf8-table37-ok? (utf8-combine4 x1 j k m)
                                          (list x1 j k m))
                        (equal (uchar=>utf8 (utf8-combine4 x1 j k m))
                               (list x1 j k m))))
          :hints(("Goal" :in-theory (enable utf8-combine4-guard)))))

 (local (defthm lemma4
          (implies (and (test-utf8-combine4 x1)
                        (integerp x1)
                        (integerp i) (<= 0 i) (<= i x1)
                        (integerp j) (<= 0 j) (< j 256)
                        (integerp k) (<= 0 k) (< k 256)
                        (integerp m) (<= 0 m) (< m 256)
                        (utf8-combine4-guard i j k m))
                   (and (uchar? (utf8-combine4 i j k m))
                        (utf8-table36-ok? (utf8-combine4 i j k m)
                                          (list i j k m))
                        (utf8-table37-ok? (utf8-combine4 i j k m)
                                          (list i j k m))
                        (equal (uchar=>utf8 (utf8-combine4 i j k m))
                               (list i j k m))))
          :hints (("Goal"
                   :in-theory
                   (e/d (utf8-combine4-guard)

; Note from J Moore about this change after v5-0: There is an extensive note in
; tau.lisp about lemma4 of utf8-decode.lisp!  There are several ways to deal
; with a slowdown caused by tau in the following proof.  We chose ``Mechanism
; D'' of the extensive note mentioned above: disable test-utf8-combine4 for
; this proof.

                        ((:executable-counterpart test-utf8-combine4)))))))

 (comp t)

 ;; This takes just over two minutes on a P4-2800.  That's pretty amazing,
 ;; considering that it's exhaustively checking 2^32 cases!

 (local (defthm lemma5-for-utf8-combine4-guard
          (implies (utf8-combine4-guard x1 x2 x3 x4)
                   (and (uchar? (utf8-combine4 x1 x2 x3 x4))
                        (utf8-table36-ok? (utf8-combine4 x1 x2 x3 x4)
                                          (list x1 x2 x3 x4))
                        (utf8-table37-ok? (utf8-combine4 x1 x2 x3 x4)
                                          (list x1 x2 x3 x4))
                        (equal (uchar=>utf8 (utf8-combine4 x1 x2 x3 x4))
                               (list x1 x2 x3 x4))))
          :hints(("Goal"
                  :in-theory (enable utf8-combine4-guard
                                     unsigned-byte-p)
                  :use (:instance lemma4
                                  (x1 255) (i x1) (j x2) (k x3) (m x4))))))

 (defthm uchar?-of-utf8-combine4
   (implies (utf8-combine4-guard x1 x2 x3 x4)
            (uchar? (utf8-combine4 x1 x2 x3 x4))))

 (defthm utf8-table36-ok?-of-utf8-combine4
   (implies (utf8-combine4-guard x1 x2 x3 x4)
            (utf8-table36-ok? (utf8-combine4 x1 x2 x3 x4)
                              (list x1 x2 x3 x4))))

 (defthm utf8-table37-ok?-of-utf8-combine4
   (implies (utf8-combine4-guard x1 x2 x3 x4)
            (utf8-table37-ok? (utf8-combine4 x1 x2 x3 x4)
                              (list x1 x2 x3 x4))))

 (defthm uchar=>utf8-of-utf8-combine4
   (implies (utf8-combine4-guard x1 x2 x3 x4)
            (equal (uchar=>utf8 (utf8-combine4 x1 x2 x3 x4))
                   (list x1 x2 x3 x4))))

 )



;; We now join our four cases into a single routine which attempts to decode
;; an encoded UTF-8 character.  On success, this routine produces a Unicode
;; scalar value corresponding to this UTF-8 byte sequence, and otherwise it
;; returns nil.

(defund utf8-char=>uchar (x)
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (<= 1 (len x))
                              (<= (len x) 4))))
  (and (mbt (unsigned-byte-listp 8 x))
       (case (len x)
         (1 (if (utf8-table36-byte-1/1? (first x))
                (first x)
              nil))
         (2 (let ((x1 (first x))
                  (x2 (second x)))
              (if (utf8-combine2-guard x1 x2)
                  (utf8-combine2 x1 x2)
                nil)))
         (3 (let ((x1 (first x))
                  (x2 (second x))
                  (x3 (third x)))
              (if (utf8-combine3-guard x1 x2 x3)
                  (utf8-combine3 x1 x2 x3)
                nil)))
         (4 (let ((x1 (first x))
                  (x2 (second x))
                  (x3 (third x))
                  (x4 (fourth x)))
              (if (utf8-combine4-guard x1 x2 x3 x4)
                  (utf8-combine4 x1 x2 x3 x4)
                nil)))
         (otherwise nil))))


(encapsulate
 ()
 (local (defun tester (x)
          (declare (type (unsigned-byte 29) x))
          (let ((test (or (if (uchar? x)
                              (equal (utf8-char=>uchar (uchar=>utf8 x))
                                     x)
                            t)
                          (cw "failure on ~x0~%" x))))
            (and test
                 (or (zp x)
                     (tester (1- x)))))))

 (local (defthm lemma
          (implies (and (tester n)
                        (integerp n)
                        (integerp i) (<= 0 i) (<= i n)
                        (uchar? i))
                   (equal (utf8-char=>uchar (uchar=>utf8 i))
                          i))))

 (comp t)

 (defthm utf8=>uchar-of-uchar=>utf8
   (implies (uchar? x)
            (equal (utf8-char=>uchar (uchar=>utf8 x))
                   x))
   :hints(("Goal" :use ((:instance lemma (n #x10FFFF) (i x))))))

 )


(encapsulate
  ()
  (local (include-book "arithmetic/top" :dir :system))
  (local (include-book "std/lists/len" :dir :system))

  (local (defthm lemma1
           (implies (utf8-table36-byte-1/1? x)
                    (utf8-table36-ok? x (list x)))
           :hints(("Goal" :in-theory (enable unsigned-byte-p
                                             uchar?
                                             utf8-table36-ok?
                                             utf8-table36-row-1?
                                             utf8-table36-codepoint-1?
                                             utf8-table36-byte-1/1?)))))

  (local (defthm lemma2
           (implies (and (equal (len x) 1)
                         (true-listp x)
                         (utf8-table36-byte-1/1? (first x)))
                    (utf8-table36-ok? (first x) x))))

  (local (defthm lemma3
           (implies (utf8-table36-byte-1/1? x)
                    (utf8-table37-ok? x (list x)))
           :hints(("Goal" :in-theory (enable unsigned-byte-p
                                             uchar?
                                             utf8-table37-ok?
                                             utf8-table37-row-1?
                                             utf8-table37-codepoint-1?
                                             utf8-table37-bytes-1?
                                             utf8-table36-byte-1/1?)))))

  (local (defthm lemma4
           (implies (and (equal (len x) 1)
                         (true-listp x)
                         (utf8-table36-byte-1/1? (first x)))
                    (utf8-table37-ok? (first x) x))))

  (local (defthm lemma5-for-utf8-table36-byte-1/1?
           (implies (utf8-table36-byte-1/1? x)
                    (uchar? x))
           :hints(("Goal" :in-theory (enable utf8-table36-byte-1/1?
                                             uchar?)))))

  (local (defthm lemma6
           (implies (utf8-table36-byte-1/1? x)
                    (equal (uchar=>utf8 x)
                           (list x)))
           :hints(("Goal" :in-theory (enable uchar=>utf8
                                             utf8-table36-byte-1/1?)))))

  (defthm uchar?-of-utf8-char=>uchar
    (implies (utf8-char=>uchar x)
             (uchar? (utf8-char=>uchar x)))
    :hints(("Goal" :in-theory (enable utf8-char=>uchar))))

  (defthm utf8-table36-okp-of-utf8-char=>uchar
    (implies (utf8-char=>uchar x)
             (utf8-table36-ok? (utf8-char=>uchar x) x))
    :hints(("Goal" :in-theory (enable utf8-char=>uchar))))

  (defthm utf8-table37-okp-of-utf8-char=>uchar
    (implies (utf8-char=>uchar x)
             (utf8-table37-ok? (utf8-char=>uchar x) x))
    :hints(("Goal" :in-theory (enable utf8-char=>uchar))))

  (defthm uchar=>utf8-of-utf8-char=>uchar
    (implies (utf8-char=>uchar x)
             (equal (uchar=>utf8 (utf8-char=>uchar x))
                    x))
    :hints(("Goal" :in-theory (enable utf8-char=>uchar))))

  )




;; We say that a valid utf8-char is a sequence of one to four bytes which can
;; be processed by utf8-char=>uchar to yield a non-nil result.  In other words,
;; it is a sequence of bytes that can be validly converted into a unicode
;; scalar value.

(defun utf8-char? (x)
  (declare (xargs :guard t))
  (and (unsigned-byte-listp 8 x)
       (<= 1 (len x))
       (<= (len x) 4)
       (utf8-char=>uchar x)))

(defthm utf8-char?-of-uchar=>utf8
  (implies (uchar? x)
           (utf8-char? (uchar=>utf8 x))))


;; Furthermore, we say that a valid utf8-string is a sequence of valid
;; utf8-chars.  In other words, this is a structure like ((x1 x2) (y1 y2 y3)
;; (z1) (a1 a2 a3 a4) ...), where each of x1, x2, y1, y2, ... are bytes, and
;; where each of the lists (x1 x2), (y1 y2 y3), ... are valid utf8-chars.
;;
;; We don't usually encounter utf8-strings, since in a file all of the bytes
;; are laid out flatly and there is no structure to take advantage of.  But
;; this is a particularly useful concept for the statement of our correctness
;; properties.

(defund utf8-string? (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (utf8-char? (car x))
           (utf8-string? (cdr x)))
    (equal x nil)))

(defthm utf8-string?-when-not-consp
  (implies (not (consp x))
           (equal (utf8-string? x)
                  (equal x nil)))
  :hints(("Goal" :in-theory (enable utf8-string?))))

(defthm utf8-string?-of-cons
  (equal (utf8-string? (cons a x))
         (and (utf8-char? a)
              (utf8-string? x)))
  :hints(("Goal" :in-theory (enable utf8-string?))))

(defthm nat-listp-when-partition-creates-utf8-string
  (implies (utf8-string? (partition sizes x))
           (nat-listp (list-fix sizes)))
  :hints(("Goal" :in-theory (enable partition))))

(defthm utf8-char?-of-take-when-partition-creates-utf8-string
  (implies (and (consp x)
                (consp sizes)
                (utf8-string? (partition sizes x)))
           (utf8-char? (take (car sizes) x))))




;; Partitioning UTF-8 Files ===================================================
;;
;; Now we turn our attention to parsing actual UTF-8 files.  By a "file" we
;; mean a list of bytes.  We say that a file is well-formed UTF-8 data if there
;; exists some partitioning of the bytes in the file which results in a UTF-8
;; string.  Below, we provide an algorithm to identify such partitions.
;;
;; First, we show that the 1st Byte entries in Table 3-6 are distinct.  That
;; is, given any x as input, x either matches none of the acceptable 1st Byte
;; patterns, or it matches exactly one of them.  Because of this, we can use
;; the 1st Byte to determine how many bytes we need to read total.

(defun utf8-table36-expected-length (x)
  "Given that x is allegedly the first byte of a UTF-8 sequence, use Table 3-6
   to determine how long this sequence is expected to be."
  (declare (type (unsigned-byte 8) x))
  (cond ((utf8-table36-byte-1/1? x) 1)
        ((utf8-table36-byte-1/2? x) 2)
        ((utf8-table36-byte-1/3? x) 3)
        ((utf8-table36-byte-1/4? x) 4)
        (t nil)))

(defthm utf8-table36-ok?-when-not-expected-length
  (implies (not (equal (utf8-table36-expected-length (first x))
                       (len x)))
           (not (utf8-table36-ok? cp x)))
  :hints(("Goal" :in-theory (enable utf8-table36-ok?
                                    utf8-table36-rows
                                    utf8-table36-bytes
                                    utf8-table36-expected-length))))

(defthm utf8-table36-expected-length-when-utf8-table36-ok?
  (implies (utf8-table36-ok? cp x)
           (equal (utf8-table36-expected-length (first x))
                  (len x))))

(defthm utf8-table36-expected-length-when-utf8-char=>uchar
  (implies (utf8-char=>uchar x)
           (equal (utf8-table36-expected-length (car x))
                  (len x)))
  :hints(("Goal"
          :in-theory (enable utf8-char=>uchar
                             utf8-table36-expected-length
                             utf8-combine2-guard
                             utf8-combine3-guard
                             utf8-combine4-guard
                             utf8-table36-bytes)
          :expand ((utf8-table36-expected-length (car x))))))




;; Partitioning Algorithm.
;;
;; Suppose that we have some list of bytes, x, and we believe that it is valid
;; UTF-8 data.  The function utf8-partition will attempt to create a
;; partitioning, i.e., a list of sizes, that will allow us to interpret the
;; bytes as a utf8-string.

(defund utf8-partition (x)
  "We attempt to create a partitioning of a list of bytes which results in a
   UTF-8 string."
  (declare (xargs :guard (unsigned-byte-listp 8 x)))
  (if (consp x)
      (let ((len1 (utf8-table36-expected-length (car x))))
        (if (or (not len1)
                (not (utf8-char? (take len1 x))))
            ;; Failed; the first byte doesn't match anything.
            (mv nil nil)
          (mv-let (successp rest)
                  (utf8-partition (nthcdr len1 x))
                  (if successp
                      (mv t (cons len1 rest))
                    (mv nil nil)))))
    (mv (equal x nil) nil)))

(defthm unsigned-byte-listp-when-utf8-partition
  (implies (mv-nth 0 (utf8-partition x))
           (unsigned-byte-listp 8 x))
  :hints(("Goal"
          :in-theory (e/d (utf8-partition)
                          (utf8-table36-expected-length)))))

(defthm nat-listp-when-utf8-partition
  (implies (mv-nth 0 (utf8-partition x))
           (nat-listp x))
  :hints(("Goal"
          :in-theory (disable unsigned-byte-listp-when-utf8-partition)
          :use ((:instance unsigned-byte-listp-when-utf8-partition)))))

(defthm true-listp-when-utf8-partition
  (implies (mv-nth 0 (utf8-partition x))
           (true-listp x))
  :hints(("Goal"
          :in-theory (disable unsigned-byte-listp-when-utf8-partition)
          :use ((:instance unsigned-byte-listp-when-utf8-partition)))))

(defthm utf8-partition-of-append-utf8-char
  (implies (and (utf8-char? a)
                (mv-nth 0 (utf8-partition x)))
           (mv-nth 0 (utf8-partition (append a x))))
  :hints(("Goal"
          :in-theory (disable utf8-table36-expected-length)
          :expand (utf8-partition (append a x)))))

(defthm sum-list-of-sizes-of-utf8-partition
  (implies (mv-nth 0 (utf8-partition x))
           (equal (sum-list (mv-nth 1 (utf8-partition x)))
                  (len x)))
  :hints(("Goal"
          :in-theory (e/d (utf8-partition)
                          (utf8-table36-expected-length)))))

(defthm nat-listp-of-mv-nth-1-of-utf8-partition
  (implies (mv-nth 0 (utf8-partition x))
           (nat-listp (mv-nth 1 (utf8-partition x))))
  :hints(("Goal" :in-theory (e/d (utf8-partition)
                                 (utf8-table36-expected-length)))))




;; Correctness of UTF8-Partition.  (Part 1: Soundness)
;;
;; Suppose that UTF8-partition is successful.  If we partition the data using
;; the resulting list of sizes, then we obtain a valid UTF8 string.

(defthm ustring?-of-utf8-partition
  (implies (mv-nth 0 (utf8-partition x))
           (utf8-string? (partition (mv-nth 1 (utf8-partition x)) x)))
  :hints(("Goal"
          :in-theory (enable utf8-partition partition)
          :induct (utf8-partition x))))


;; Correctness of UTF8-Partition.  (Part 2: Completeness)
;;
;; Given a list of bytes, suppose there is any partitioning which results in a
;; valid UTF8 string.  Then, UTF8-Partition is successful.

(local (defthm len-when-true-listp
         (implies (true-listp x)
                  (equal (equal (len x) 0)
                         (equal x nil)))))

(local (defthm utf8-table36-expected-length-when-partition-creates-utf8-string
         (implies (and (consp x)
                       (consp sizes)
                       (utf8-string? (partition sizes x)))
                  (equal (utf8-table36-expected-length (car x))
                         (car sizes)))
         :hints(("Goal"
                 :in-theory (disable utf8-table36-expected-length
                                     utf8-table36-expected-length-when-utf8-char=>uchar
                                     utf8-char?-of-take-when-partition-creates-utf8-string)
                 :use ((:instance utf8-char?-of-take-when-partition-creates-utf8-string)
                       (:instance utf8-table36-expected-length-when-utf8-char=>uchar
                                  (x (take (car sizes) x))))))))

(defthm utf8-partition-successful-when-any-valid-partitioning-exists
  (implies (and (unsigned-byte-listp 8 x)
                (true-listp sizes)
                (equal (sum-list sizes) (len x))
                (utf8-string? (partition sizes x)))
           (mv-nth 0 (utf8-partition x)))
  :hints(("Goal" :in-theory (enable partition utf8-partition))))


;; Correctness of UTF8-Partition.  (Part 3: Uniqueness)
;;
;; Given a list of bytes, suppose there is any partitioning which results in a
;; valid UTF8 string.  Then, UTF8-Partition returns exactly this partitioning.

(defthm utf8-partitioning-is-unique-when-any-valid-partitioning-exists
  (implies (and (unsigned-byte-listp 8 x)
                (true-listp sizes)
                (equal (sum-list sizes) (len x))
                (utf8-string? (partition sizes x)))
           (equal (mv-nth 1 (utf8-partition x))
                  sizes))
  :hints(("Goal" :in-theory (enable partition utf8-partition))))





;; We can now extend our utf8-char=>uchar routine to be able to convert
;; utf8-strings into ustrings.

(defund utf8-string=>ustring (x)
  (declare (xargs :guard (utf8-string? x)))
  (if (consp x)
      (cons (utf8-char=>uchar (car x))
            (utf8-string=>ustring (cdr x)))
    nil))

(defthm utf8-string=>ustring-when-not-consp
  (implies (not (consp x))
           (equal (utf8-string=>ustring x)
                  nil))
  :hints(("Goal" :in-theory (enable utf8-string=>ustring))))

(defthm utf8-string=>ustring-of-cons
  (equal (utf8-string=>ustring (cons a x))
         (cons (utf8-char=>uchar a)
               (utf8-string=>ustring x)))
  :hints(("Goal" :in-theory (enable utf8-string=>ustring))))

(defthmd ustring?-of-utf8-string=>ustring
  (implies (utf8-string? x)
           (ustring? (utf8-string=>ustring x)))
  :hints(("Goal" :induct (len x))))





;; We are now going to write our main decoding routine.  This function takes,
;; as input, a list of bytes which hopefully are valid UTF-8 data, and creates
;; the decoded, Unicode string corresponding to this list of bytes.
;;
;; We want this operation to be fast.  We have gone to some lengths to use mbe
;; in order to tune the function.  Below, we provide a heavily optimized, tail
;; recursive version of this function, which we will ultimately use as our
;; algorithm's core.  You should probably just skim through this definition and
;; not pay it much attention.

(defund utf8=>ustring-fast (x acc)
  (declare (xargs :guard (and (unsigned-byte-listp 8 x)
                              (ustring? acc))
                  :verify-guards nil))
  (mbe
   :logic
   (if (not (consp x))
       (if (equal x nil)
           (reverse acc)
         'fail)
     (let ((len1 (utf8-table36-expected-length (car x))))
       (if (not len1)
           'fail
         (let ((first (utf8-char=>uchar (take len1 x))))
           (if (not first)
               'fail
             (utf8=>ustring-fast (nthcdr len1 x)
                                 (cons first acc)))))))
   :exec
   (if (not (consp x))
       (if (eq x nil)
           (reverse acc)
         'fail)
     (let ((x1 (car x)))
       (cond

        ((in-range? (the-fixnum x1) 0 127)
         ;; Expected length 1.  We don't need to do any further checking; we can
         ;; just recur very quickly.  Note that this will give us very good
         ;; performance for English text, where characters are typically only a
         ;; single byte.
         (utf8=>ustring-fast (cdr x) (cons (car x) acc)))

        ((in-range? (the-fixnum x1) 194 223)
         ;; Expected length 2.  (We excluded 192,193 because they are not
         ;; permitted under Table 3-7.)
         (let ((x1-rest (rest x)))
           (if (not (consp x1-rest))
               'fail
            (let ((x2      (first x1-rest))
                  (x2-rest (rest  x1-rest)))
              (if (in-range? (the-fixnum x2) 128 191)
                  ;; Manually-inlined utf8-combine2 operation.
                  (utf8=>ustring-fast
                   x2-rest
                   (cons
                    (the-fixnum
                     (logior
                      (the-fixnum (ash (the-fixnum (logand (the-fixnum x1) 31)) 6))
                      (the-fixnum (logand (the-fixnum x2) 63))))
                    acc))
                'fail)))))

        ((in-range? (the-fixnum x1) 224 239)
         ;; Expected length 3.
         (let ((x1-rest (rest x)))
           (if (not (consp x1-rest))
               'fail
            (let ((x2      (first x1-rest))
                  (x2-rest (rest  x1-rest)))
              (if (not (consp x2-rest))
                  'fail
               (let ((x3      (first x2-rest))
                     (x3-rest (rest  x2-rest)))
                 (if (and (cond ((= (the-fixnum x1) 224)
                                 (in-range? (the-fixnum x2) 160 191))
                                ((= (the-fixnum x1) 237)
                                 (in-range? (the-fixnum x2) 128 159))
                                (t
                                 (in-range? (the-fixnum x2) 128 191)))
                          (in-range? (the-fixnum x3) 128 191))
                     (utf8=>ustring-fast
                      x3-rest
                      (cons
                       (the-fixnum
                        (logior
                         (the-fixnum
                          (ash (the-fixnum (logand (the-fixnum x1) 15)) 12))
                         (logior
                          (the-fixnum
                           (ash (the-fixnum (logand (the-fixnum x2) 63)) 6))
                          (the-fixnum (logand (the-fixnum x3) 63)))))
                       acc))
                   'fail)))))))

        ((in-range? (the-fixnum x1) 240 244)
         ;; Expected length 4.  We only accept 240-244 because of Table 3-7.
         (let ((x1-rest (rest x)))
           (if (not (consp x1-rest))
               'fail
            (let ((x2      (first x1-rest))
                  (x2-rest (rest  x1-rest)))
              (if (not (consp x2-rest))
                  'fail
               (let ((x3      (first x2-rest))
                     (x3-rest (rest  x2-rest)))
                 (if (not (consp x3-rest))
                     'fail
                  (let ((x4      (first x3-rest))
                        (x4-rest (rest  x3-rest)))
                    (if (and (cond ((= (the-fixnum x1) 240)
                                    (in-range? (the-fixnum x2) 144 191))
                                   ((= (the-fixnum x1) 244)
                                    (in-range? (the-fixnum x2) 128 143))
                                   (t
                                    (in-range? (the-fixnum x2) 128 191)))
                             (in-range? (the-fixnum x3) 128 191)
                             (in-range? (the-fixnum x4) 128 191))
                        (utf8=>ustring-fast
                         x4-rest
                         (cons
                          (the-fixnum
                           (logior
                            (the-fixnum
                             (ash (the-fixnum (logand (the-fixnum x1) 7)) 18))
                            (the-fixnum
                             (logior
                              (the-fixnum
                               (ash (the-fixnum (logand (the-fixnum x2) 63)) 12))
                              (the-fixnum
                               (logior
                                (the-fixnum
                                 (ash (the-fixnum (logand (the-fixnum x3) 63)) 6))
                                (the-fixnum
                                 (logand (the-fixnum x4) 63))))))))
                          acc))
                      'fail)))))))))

        (t 'fail))))))


;; It takes some work to show that the above MBE substitution is legitimate.

(local (defthm terrible-lemma-1
         (implies (and (integerp x)
                       (<= 0 x)
                       (<= x 127))
                  (uchar? x))
         :hints(("Goal" :in-theory (enable uchar?)))))

(local (defthm terrible-lemma-2
         (IMPLIES (AND (integerp x1)
                       (integerp x2)
                       (< 127 X1)
                       (<= 194 X1)
                       (<= X1 223)
                       (<= 128 X2)
                       (<= X2 191))
                  (UCHAR? (LOGIOR (ASH (LOGAND X1 31) 6)
                                  (LOGAND X2 63))))
         :hints(("Goal"
                 :in-theory (enable utf8-combine2-guard
                                    utf8-combine2
                                    utf8-table36-bytes
                                    utf8-table37-bytes)
                 :use ((:instance uchar?-of-utf8-combine2))))))

(local (defthm terrible-lemma-3
         (IMPLIES (AND (integerp x2)
                       (integerp x3)
                       (<= 160 X2)
                       (<= X2 191)
                       (<= 128 X3)
                       (<= X3 191))
                  (UCHAR? (LOGIOR 0 (ASH (LOGAND X2 63) 6)
                                  (LOGAND X3 63))))
         :hints(("Goal"
                 :in-theory (enable utf8-combine3-guard
                                    utf8-combine3
                                    utf8-table36-bytes
                                    utf8-table37-bytes)
                 :use ((:instance uchar?-of-utf8-combine3
                                  (x1 224)))))))

(local (defthm terrible-lemma-4
         (IMPLIES (AND (integerp X1)
                       (integerp X2)
                       (integerp X3)
                       (<= 224 X1)
                       (<= X1 239)
                       (NOT (EQUAL X1 224))
                       (NOT (EQUAL X1 237))
                       (<= 128 X2)
                       (<= X2 191)
                       (<= 128 X3)
                       (<= X3 191))
                  (UCHAR? (LOGIOR (ASH (LOGAND X1 15) 12)
                                  (ASH (LOGAND X2 63) 6)
                                  (LOGAND X3 63))))
         :hints(("Goal"
                 :in-theory (enable utf8-combine3-guard
                                    utf8-combine3
                                    utf8-table36-bytes
                                    utf8-table37-bytes)
                 :use ((:instance uchar?-of-utf8-combine3))))))

(local (defthm terrible-lemma-5
         (IMPLIES (AND (integerp x2)
                       (integerp x3)
                       (<= 128 X2)
                       (<= X2 159)
                       (<= 128 X3)
                       (<= X3 191))
                  (UCHAR? (LOGIOR 53248 (ASH (LOGAND X2 63) 6)
                                  (LOGAND X3 63))))
         :hints(("Goal"
                 :in-theory (enable utf8-combine3-guard
                                    utf8-combine3
                                    utf8-table36-bytes
                                    utf8-table37-bytes)
                 :use ((:instance uchar?-of-utf8-combine3
                                  (x1 237)))))))

(local (defthm terrible-lemma-6
         (IMPLIES (AND (integerp x2)
                       (integerp x3)
                       (integerp x4)
                       (<= 144 X2)
                       (<= X2 191)
                       (<= 128 X3)
                       (<= X3 191)
                       (<= 128 X4)
                       (<= X4 191))
                  (UCHAR? (LOGIOR 0 (ASH (LOGAND X2 63) 12)
                                  (ASH (LOGAND X3 63) 6)
                                  (LOGAND X4 63))))
         :hints(("Goal"
                 :in-theory (enable utf8-combine4-guard
                                    utf8-combine4
                                    utf8-table36-bytes
                                    utf8-table37-bytes)
                 :use ((:instance uchar?-of-utf8-combine4
                                  (x1 240)))))))

(local (defthm terrible-lemma-7
         (IMPLIES (AND (integerp x1)
                       (integerp x2)
                       (integerp x3)
                       (integerp x4)
                       (<= 240 X1)
                       (<= X1 244)
                       (NOT (EQUAL X1 240))
                       (NOT (EQUAL X1 244))
                       (<= 128 X2)
                       (<= X2 191)
                       (<= 128 X3)
                       (<= X3 191)
                       (<= 128 X4)
                       (<= X4 191))
                  (UCHAR? (LOGIOR (ASH (LOGAND X1 7) 18)
                                  (ASH (LOGAND X2 63) 12)
                                  (ASH (LOGAND X3 63) 6)
                                  (LOGAND X4 63))))
         :hints(("Goal"
                 :in-theory (enable utf8-combine4-guard
                                    utf8-combine4
                                    utf8-table36-bytes
                                    utf8-table37-bytes)
                 :use ((:instance uchar?-of-utf8-combine4))))))

(local (defthm terrible-lemma-8
         (IMPLIES (AND (integerp x2)
                       (integerp x3)
                       (integerp x4)
                       (<= 128 x2)
                       (<= x2 143)
                       (<= 128 x3)
                       (<= x3 191)
                       (<= 128 x4)
                       (<= x4 191))
                  (UCHAR? (LOGIOR 1048576 (ASH (LOGAND x2 63) 12)
                                  (ASH (LOGAND x3 63) 6)
                                  (LOGAND x4 63))))
         :hints(("Goal"
                 :in-theory (enable utf8-combine4-guard
                                    utf8-combine4
                                    utf8-table36-bytes
                                    utf8-table37-bytes)
                 :use ((:instance uchar?-of-utf8-combine4
                                  (x1 244)))))))


(verify-guards utf8=>ustring-fast
  :hints(("Goal"
          :do-not '(generalize fertilize)
          :do-not-induct t
          :in-theory (e/d (unsigned-byte-listp
                           utf8-char=>uchar
                           utf8-table36-bytes
                           utf8-table37-bytes
                           utf8-combine2
                           utf8-combine3
                           utf8-combine4
                           utf8-combine2-guard
                           utf8-combine3-guard
                           utf8-combine4-guard)
                          ;; BOZO the above "terrible lemmas" were developed
                          ;; before including bitops, so they're targeting the
                          ;; wrong normal forms...
                          (bitops::LOGAND-WITH-BITMASK
                           simplify-logior
                           commutativity-of-logior
                           commutativity-of-logand)))))


;; Finally we are ready to present our "simpler" view of the algorithm.  The
;; most naive and straightforward way to do the decoding seems to be the
;; following.
;;
;;  (1) Partition the file into a valid set of bytes, if one exists.
;;      (this is easy to do, we already have UTF8-Partition which
;;       finds this partitioning.)
;;
;;  (2) Go through "UTF8 Character by UTF8 character" and coerce each
;;      into its atomic uchar representation.
;;
;; Indeed, our function logically operates this way.  But, under the hood we
;; will substitute in our heavily inlined, fixnum optimized, and tail recursive
;; version instead, with MBE.

(defund utf8=>ustring (x)
  (declare (xargs :guard (unsigned-byte-listp 8 x)
                  :verify-guards nil))
  (mbe :logic (mv-let (successp sizes)
                      (utf8-partition x)
                      (if successp
                          (utf8-string=>ustring (partition sizes x))
                        'fail))
       :exec (utf8=>ustring-fast x nil)))

(encapsulate
 ()

 (local (defthm lemma1
          (implies (utf8-string? x)
                   (equal (ustring=>utf8 (utf8-string=>ustring x))
                          (flatten x)))
          :hints(("Goal" :induct (len x)))))

 (local (defthm lemma2
          (implies (ustring? x)
                   (mv-nth 0 (utf8-partition (ustring=>utf8 x))))
          :hints(("Goal" :in-theory (enable utf8-partition ustring=>utf8)))))

 (local (defthm lemma3
          (implies (ustring? x)
                   (equal
                    (utf8-string=>ustring
                     (partition (mv-nth 1 (utf8-partition (ustring=>utf8 x)))
                                (ustring=>utf8 x)))
                    x))
          :hints(("Goal"
                  :induct (len x)
                  :in-theory (enable utf8-partition)))))

 ;; Invertibility of Unicode <-> UTF8 Conversion
 ;;
 ;; Given any Unicode String, we can decode its UTF-8 encoding to recover the
 ;; original string.

 (defthm utf8=>ustring-of-ustring=>utf8
   (implies (ustring? x)
            (equal (utf8=>ustring (ustring=>utf8 x))
                   x))
   :hints(("Goal" :in-theory (enable utf8=>ustring))))

 ;; Given any sequence of bytes that can be validly partitioned into UTF8 byte
 ;; sequences, we can encode its decoding to recover the original sequence of
 ;; bytes.

 (defthm ustring=>utf8-of-utf8=>ustring
   (implies (mv-nth 0 (utf8-partition x))
            (equal (ustring=>utf8 (utf8=>ustring x))
                   x))
   :hints(("Goal"
           :in-theory (enable utf8=>ustring)
           :use ((:instance flatten-of-partition
                            (sizes (mv-nth 1 (utf8-partition x)))
                            (x x)))))))


;; We now address the validity of the MBE substitution.

(encapsulate
 ()
 (local (defthm lemma
          (implies (and (true-listp acc)
                        (mv-nth 0 (utf8-partition x)))
                   (equal (utf8=>ustring-fast x acc)
                          (revappend acc (utf8=>ustring x))))
          :hints(("Goal"
                  :in-theory (enable utf8=>ustring-fast
                                     utf8-partition
                                     utf8=>ustring)
                  :induct (utf8=>ustring-fast x acc)))))

 (local (defthm lemma2
          (implies (and (unsigned-byte-listp 8 x)
                        (not (mv-nth 0 (utf8-partition x))))
                   (equal (utf8=>ustring-fast x acc)
                          'fail))
          :hints(("Goal"
                  :in-theory (e/d (utf8=>ustring-fast
                                   utf8-partition
                                   utf8-char=>uchar)
                                  (utf8-table36-expected-length))
                  :induct (utf8=>ustring-fast x acc)))))

 (defthm utf8=>ustring-fast-of-nil
   (implies (unsigned-byte-listp 8 x)
            (equal (utf8=>ustring-fast x nil)
                   (utf8=>ustring x)))
   :hints(("Goal" :in-theory (enable utf8=>ustring)))))

(verify-guards utf8=>ustring
               :hints(("Goal" :in-theory (enable utf8=>ustring))))

