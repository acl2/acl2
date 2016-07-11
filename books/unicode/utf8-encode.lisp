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
(include-book "utf8-table36")
(include-book "utf8-table37")
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/typed-lists/signed-byte-listp" :dir :system))  ;; for the-fixnum
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))


(local (defthm signed-byte-p-resolver
         (implies (and (integerp n)
                       (<= 1 n)
                       (integerp x)
                       (<= (- (expt 2 (1- n))) x)
                       (< x (expt 2 (1- n))))
                  (signed-byte-p n x))
         :hints(("Goal" :in-theory (enable signed-byte-p)))))


;; Conversion From Unicode to UTF-8 ===========================================
;;
;; Recall that as uchar?s and within ustring?s, we store code points atomically
;; as single integers.  It is relatively straightforward to convert these
;; codepoints into UTF8 byte sequences.
;;
;; We now introduce the function uchar=>utf8, which, as its name suggests will
;; take any uchar and return to us the corresponding byte sequence in UTF-8.
;; This function is based on Table 3-6, and is in essence a straightforward
;; translation of this table, based on shifting the bits of the codepoints into
;; the correct locations for our output bytes.

(defund uchar=>utf8 (x)
  "Encode a Unicode character as a UTF8 byte sequence."
  (declare (xargs :guard (uchar? x)))
  (cond ((<= (the-fixnum x) #x007F)
         (list x))

        ((in-range? (the-fixnum x) #x0080 #x07FF)
         (let ((110yyyyy (logior #xC0 (the-fixnum (ash (the-fixnum x) -6))))
               (10xxxxxx (logior #X80 (the-fixnum
                                       (logand (the-fixnum x) #x3F)))))
           (list 110yyyyy 10xxxxxx)))

        ((in-range? (the-fixnum x) #x0800 #xFFFF)
         (let ((1110zzzz (logior #xE0 (the-fixnum (ash (the-fixnum x) -12))))
               (10yyyyyy (logior #x80 (the-fixnum
                                       (logand (the-fixnum
                                                (ash (the-fixnum x) -6))
                                               #x3F))))
               (10xxxxxx (logior #x80 (the-fixnum
                                       (logand (the-fixnum x) #x3F)))))
           (list 1110zzzz 10yyyyyy 10xxxxxx)))

        (t (let ((11110uuu (logior #xF0 (the-fixnum (ash (the-fixnum x) -18))))
                 (10uuzzzz (logior #x80 (the-fixnum
                                         (logand (the-fixnum
                                                  (ash (the-fixnum x) -12))
                                                 #x3F))))
                 (10yyyyyy (logior #x80 (the-fixnum
                                         (logand (the-fixnum
                                                  (ash (the-fixnum x) -6))
                                                 #x3F))))
                 (10xxxxxx (logior #x80 (the-fixnum
                                         (logand (the-fixnum x) #x3F)))))
             (list 11110uuu 10uuzzzz 10yyyyyy 10xxxxxx)))))

(defthm unsigned-byte-list-of-uchar=>utf8-when-uchar?
  (implies (uchar? x)
           (unsigned-byte-listp 8 (uchar=>utf8 x)))
  :hints(("Goal" :in-theory (enable uchar=>utf8))))

(defthm len-of-uchar=>utf8
  (implies (uchar? x)
           (and (<= 1 (len (uchar=>utf8 x)))
                (<= (len (uchar=>utf8 x)) 4)))
  :rule-classes :linear
  :hints(("Goal" :in-theory (enable uchar=>utf8))))


;; Now we would like to show that our encoding function actually respects the
;; constraints of Tables 3-6 and 3-7 which we formalized above.
;;
;; How can we prove something like this?  I have no deep insight about why the
;; table is written as it is, it all seems rather random/arbitrary.  Rather
;; than try to actually understand any sort of deeper meaning here, I will just
;; have ACL2 run an exhaustive test to prove that every uchar has a
;; satisfactory encoding under our function.
;;
;; This is so easy it feels like cheating.  It is a really easy way to get this
;; complicated theorem through, and it is useful later in the file as well.
;; Our method is to first write a testing function, to test all the integers
;; between 0 and i.

(encapsulate
 ()
 (local (defun test-uchar=>utf8 (i)
          (declare (xargs :guard (natp i)))
          (and (if (uchar? i)
                   (and (utf8-table37-ok? i (uchar=>utf8 i))
                        (utf8-table36-ok? i (uchar=>utf8 i)))
                 t)
               (or (zp i)
                   (test-uchar=>utf8 (1- i))))))

 ;; We now show that if we have successfully tested all the integers between 0
 ;; and i, then each of these integers satisfies our desired property.

 (local (defthm l0
          (implies (and (integerp i)
                        (integerp j)
                        (<= j i))
                   (equal (< (+ -1 i) j)
                          (equal i j)))))

 (local (defthmd lemma
          (implies (and (test-uchar=>utf8 i)
                        (natp i)
                        (natp j)
                        (<= j i)
                        (uchar? j))
                   (and (utf8-table36-ok? j (uchar=>utf8 j))
                        (utf8-table37-ok? j (uchar=>utf8 j))))))

 ;; Finally, by instantiation of the above theorem, we can show that all of the
 ;; integers in the range [0, #x10ffff] satisfy our property, and then trivially
 ;; all uchar's satisfy our property, since all uchar's are in this range.  This
 ;; means we run our testing function for about 1.1 million iterations, so we
 ;; need to compile things first.  The entire process takes only about 2 seconds
 ;; on a P4-2800.

 (comp t)

 (local (defthm lemma2
          (implies (uchar? x)
                   (and (utf8-table36-ok? x (uchar=>utf8 x))
                        (utf8-table37-ok? x (uchar=>utf8 x))))
          :hints(("Goal"
                  :use (:instance lemma
                                  (i #x10FFFF)
                                  (j x))))))

 (defthm utf8-table36-ok?-of-uchar=>utf8-when-uchar?
   (implies (uchar? x)
            (utf8-table36-ok? x (uchar=>utf8 x))))

 (defthm utf8-table37-ok?-of-uchar=>utf8-when-uchar?
   (implies (uchar? x)
            (utf8-table37-ok? x (uchar=>utf8 x)))))



;; We also introduce ustring=>utf8, which simply repeatedly applies uchar=>utf8
;; in order to create a UTF-8 encoding of a string.

(defund ustring=>utf8 (x)
  "Encode a Unicode string as a UTF-8 byte sequence."
  (declare (xargs :guard (ustring? x)))
  (if (atom x)
      nil
    (append (uchar=>utf8 (car x))
            (ustring=>utf8 (cdr x)))))

(defthm ustring=>utf8-when-not-consp
  (implies (not (consp x))
           (equal (ustring=>utf8 x)
                  nil))
  :hints(("Goal" :in-theory (enable ustring=>utf8))))

(defthm ustring=>utf8-of-cons
  (equal (ustring=>utf8 (cons a x))
         (append (uchar=>utf8 a)
                 (ustring=>utf8 x)))
  :hints(("Goal" :in-theory (enable ustring=>utf8))))

(defthm true-listp-of-ustring=>utf8
  (true-listp (ustring=>utf8 x))
  :rule-classes (:rewrite :type-prescription)
  :hints(("Goal" :induct (len x))))
