; ACL2 String Library
; Copyright (C) 2009-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "ieqv")
(include-book "std/basic/defs" :dir :system)
(include-book "std/util/deflist-base" :dir :system)
(include-book "std/lists/rev" :dir :system)
(include-book "std/lists/append" :dir :system)
(local (include-book "arithmetic"))
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (in-theory (disable floor mod truncate)))

(defsection decimal
  :parents (numbers)
  :short "Functions for working with decimal (base 10) numbers in strings.")

(local (xdoc::set-default-parents decimal))

(define digitp (x)
  :short "Recognizer for numeric characters (0-9)."
  :returns bool
  :long "<p>ACL2 provides @(see digit-char-p) which is more flexible and can
recognize numeric characters in other bases.  @(call digitp) only recognizes
base-10 digits, but is much faster, at least on CCL.  Here is an experiment you
can run in raw lisp, with times reported in CCL on an AMD FX-8350.</p>

@({
  (defconstant *chars*
    (loop for i from 0 to 256 collect (code-char i)))

  ;; 17.130 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (digit-char-p c))))

  ;; 3.772 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (str::digitp c))))
})"
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (and (<= (char-code #\0) code)
                     (<= code (char-code #\9))))
       :exec (and (characterp x)
                  (let ((code (the (unsigned-byte 8)
                                   (char-code (the character x)))))
                    (declare (type (unsigned-byte 8) code))
                    (and (<= (the (unsigned-byte 8) code)
                             (the (unsigned-byte 8) 57))
                         (<= (the (unsigned-byte 8) 48)
                             (the (unsigned-byte 8) code))))))
  ///
  (defcong ichareqv equal (digitp x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))
  (defthm characterp-when-digitp
    (implies (digitp char)
             (characterp char))
    :rule-classes :compound-recognizer))

(define nonzero-digitp (x)
  :short "Recognizer for non-zero numeric characters (1-9)."
  :returns bool
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (and (<= (char-code #\1) code)
                     (<= code (char-code #\9))))
       :exec (and (characterp x)
                  (let ((code (the (unsigned-byte 8)
                                   (char-code (the character x)))))
                    (declare (type (unsigned-byte 8) code))
                    (and (<= (the (unsigned-byte 8) code)
                             (the (unsigned-byte 8) 57))
                         (<= (the (unsigned-byte 8) 49)
                             (the (unsigned-byte 8) code))))))
  ///
  (defcong ichareqv equal (nonzero-digitp x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))
  (defthm digitp-when-nonzero-digitp
    (implies (nonzero-digitp x)
             (digitp x))
    :hints(("Goal" :in-theory (enable digitp)))))

(define digit-val
  :short "Coerces a @(see digitp) character into a number."
  ((x digitp :type character))
  :split-types t
  :returns (val natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(digit-val #\\3)') is 3.  For any non-digitp, 0 is
         returned.</p>"
  :inline t
  (mbe :logic
       (if (digitp x)
           (- (char-code (char-fix x))
              (char-code #\0))
         0)
       :exec
       (the (unsigned-byte 8)
         (- (the (unsigned-byte 8) (char-code (the character x)))
            (the (unsigned-byte 8) 48))))
  :prepwork
  ((local (in-theory (enable digitp char-fix))))
  ///
  (defcong ichareqv equal (digit-val x) 1
    :hints(("Goal" :in-theory (enable ichareqv downcase-char))))
  (defthm digit-val-upper-bound
    (< (digit-val x) 10)
    :rule-classes ((:rewrite) (:linear)))
  (defthm equal-of-digit-val-and-digit-val
    (implies (and (digitp x)
                  (digitp y))
             (equal (equal (digit-val x) (digit-val y))
                    (equal x y))))
  (defthm digit-val-of-digit-to-char
    (implies (and (natp n)
                  (< n 10))
             (equal (digit-val (digit-to-char n))
                    n))))

(std::deflist digit-listp (x)
  :short "Recognizes lists of @(see digitp) characters."
  (digitp x)
  ///
  (defcong icharlisteqv equal (digit-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm character-listp-when-digit-listp
    (implies (digit-listp x)
             (equal (character-listp x)
                    (true-listp x)))
    :rule-classes ((:rewrite :backchain-limit-lst 1))))

(define digit-list-value1
  :parents (digit-list-value)
  ((x digit-listp)
   (val :type unsigned-byte))
  (mbe :logic (if (consp x)
                  (digit-list-value1 (cdr x)
                                     (+ (digit-val (car x))
                                        (* 10 (nfix val))))
                (nfix val))
       :exec (if (consp x)
                 (digit-list-value1
                  (cdr x)
                  (the unsigned-byte
                    (+ (the (unsigned-byte 8)
                         (- (the (unsigned-byte 8)
                              (char-code (the character (car x))))
                            (the (unsigned-byte 8) 48)))
                       (* (the unsigned-byte 10)
                          (the unsigned-byte val)))))
               (the unsigned-byte val)))
  :guard-hints (("Goal" :in-theory (enable digit-val digitp))))

(define digit-list-value
  :short "Coerces a @(see digit-listp) into a natural number."
  ((x digit-listp))
  :returns (value natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(digit-list-value '(#\1 #\0 #\3))') is 103.  See
         also @(see parse-nat-from-charlist) for a more flexible function that
         can tolerate non-numeric characters after the number.</p>"
  :inline t
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (+ (* (expt 10 (1- (len x)))
                        (digit-val (car x)))
                     (digit-list-value (cdr x)))
                0)
       :exec (digit-list-value1 x 0))
  ///
  (defcong icharlisteqv equal (digit-list-value x) 1
    :hints(("Goal" :in-theory (e/d (icharlisteqv)))))
  (defthm digit-list-value-upper-bound
    (< (digit-list-value x)
       (expt 10 (len x)))
    :hints(("Goal" :nonlinearp t)))
  (defthm digit-list-value-upper-bound-free
    (implies (equal n (len x))
             (< (digit-list-value x) (expt 10 n))))
  (defthm digit-list-value1-removal
    (equal (digit-list-value1 x val)
           (+ (digit-list-value x)
              (* (nfix val) (expt 10 (len x)))))
    :hints(("Goal"
            :in-theory (enable digit-list-value1)
            :induct (digit-list-value1 x val))))
  (verify-guards digit-list-value$inline)
  (defthm digit-list-value-of-append
    (equal (digit-list-value (append x (list a)))
           (+ (* 10 (digit-list-value x))
              (digit-val a)))))

(define skip-leading-digits
  :short "Skip over any leading digits at the start of a character list."
  (x)
  :returns (tail character-listp :hyp (character-listp x))
  (cond ((atom x)         nil)
        ((digitp (car x)) (skip-leading-digits (cdr x)))
        (t                x))
  ///
  (local (defun ind (x y)
           (if (or (atom x) (atom y))
               (list x y)
             (ind (cdr x) (cdr y)))))
  (defcong charlisteqv charlisteqv (skip-leading-digits x) 1
    :hints(("Goal" :induct (ind x x-equiv))))
  (defcong icharlisteqv icharlisteqv (skip-leading-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm len-of-skip-leading-digits
    (equal (< (len (skip-leading-digits x))
              (len x))
           (digitp (car x)))
    :rule-classes ((:rewrite)
                   (:linear :corollary (implies (digitp (car x))
                                                (< (len (skip-leading-digits x))
                                                   (len x)))))))

(define take-leading-digits
  :short "Collect any leading digits from the start of a character list."
  (x)
  :returns (head character-listp :hyp (character-listp x))
  (cond ((atom x)         nil)
        ((digitp (car x)) (cons (car x) (take-leading-digits (cdr x))))
        (t                nil))
  ///
  (local (defthm l0 ;; Gross, but gets us an equal congruence
           (implies (digitp x)
                    (equal (ichareqv x y)
                           (equal x y)))
           :hints(("Goal" :in-theory (enable ichareqv
                                             downcase-char
                                             digitp
                                             char-fix)))))
  (defcong icharlisteqv equal (take-leading-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm digit-listp-of-take-leading-digits
    (digit-listp (take-leading-digits x)))
  (defthm bound-of-len-of-take-leading-digits
    (<= (len (take-leading-digits x)) (len x))
    :rule-classes :linear)
  (defthm equal-of-take-leading-digits-and-length
    (equal (equal (len (take-leading-digits x)) (len x))
           (digit-listp x)))
  (defthm take-leading-digits-when-digit-listp
    (implies (digit-listp x)
             (equal (take-leading-digits x)
                    (list-fix x))))
  (defthm consp-of-take-leading-digits
    (equal (consp (take-leading-digits x))
           (digitp (car x)))))

(define digit-string-p-aux
  :parents (digit-string-p)
  ((x  stringp             :type string)
   (n  natp                :type unsigned-byte)
   (xl (eql xl (length x)) :type unsigned-byte))
  :guard (<= n xl)
; Removed after v7-2 by Matt K. since logically, the definition is
; non-recursive:
; :measure (nfix (- (nfix xl) (nfix n)))
  :split-types t
  :verify-guards nil
  :enabled t
  (mbe :logic
       (digit-listp (nthcdr n (explode x)))
       :exec
       (if (eql n xl)
           t
         (and (digitp (char x n))
              (digit-string-p-aux x
                                  (the unsigned-byte (+ 1 n))
                                  xl))))
  ///
  (verify-guards digit-string-p-aux
    :hints(("Goal" :in-theory (enable digit-listp)))))

(define digit-string-p
  :short "Recognizer for strings whose characters are all decimal digits."
  ((x :type string))
  :returns bool
  :long "<p>Corner case: this accepts the empty string since all of its
characters are decimal digits.</p>

<p>Logically this is defined in terms of @(see digit-listp).  But in the
execution, we use a @(see char)-based function that avoids exploding the
string.  This provides much better performance, e.g., on an AMD FX-8350
with CCL:</p>

@({
    ;; 0.48 seconds, no garbage
    (let ((x \"1234\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::digit-string-p x))))

    ;; 0.82 seconds, 640 MB allocated
    (let ((x \"1234\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::digit-listp (coerce x 'list)))))
})"
  :inline t
  :enabled t
  (mbe :logic (digit-listp (explode x))
       :exec (digit-string-p-aux x 0 (length x)))
  ///
  (defcong istreqv equal (digit-string-p x) 1))


(define basic-natchars
  :parents (natchars)
  :short "Logically simple definition that is similar to @(see natchars)."
  ((n natp))
  :returns (chars digit-listp)
  :long "<p>This <i>almost</i> computes @('(natchars n)'), but when @('n') is
zero it returns @('nil') instead of @('(#\\0)').  You would normally never call
this function directly, but it is convenient for reasoning about @(see
natchars).</p>"
  (if (zp n)
      nil
    (cons (digit-to-char (mod n 10))
          (basic-natchars (floor n 10))))
  :prepwork
  ((local (defthm l0
            (implies (and (< a 10)
                          (< b 10)
                          (natp a)
                          (natp b))
                     (equal (equal (digit-to-char a) (digit-to-char b))
                            (equal a b)))))
   (local (defthm l1
            (implies (and (< a 10)
                          (natp a))
                     (digitp (digit-to-char a)))))
   (local (in-theory (disable digit-to-char))))
  ///
  (defthm basic-natchars-when-zp
    (implies (zp n)
             (equal (basic-natchars n)
                    nil)))
  (defthm true-listp-of-basic-natchars
    (true-listp (basic-natchars n))
    :rule-classes :type-prescription)
  (defthm character-listp-of-basic-natchars
    (character-listp (basic-natchars n)))
  (defthm basic-natchars-under-iff
    (iff (basic-natchars n)
         (not (zp n))))
  (defthm consp-of-basic-natchars
    (equal (consp (basic-natchars n))
           (if (basic-natchars n) t nil)))
  (local (defun my-induction (n m)
           (if (or (zp n)
                   (zp m))
               nil
             (my-induction (floor n 10) (floor m 10)))))
  (defthm basic-natchars-one-to-one
    (equal (equal (basic-natchars n)
                  (basic-natchars m))
           (equal (nfix n)
                  (nfix m)))
    :hints(("Goal" :induct (my-induction n m)))))

(define natchars-aux ((n natp) acc)
  :parents (natchars)
  :verify-guards nil
  :enabled t
  (mbe :logic
       (revappend (basic-natchars n) acc)
       :exec
       (if (zp n)
           acc
         (natchars-aux
          (the unsigned-byte (truncate (the unsigned-byte n) 10))
          (cons (the character (code-char
                                (the (unsigned-byte 8)
                                     (+ (the (unsigned-byte 8) 48)
                                        (the (unsigned-byte 8)
                                             (rem (the unsigned-byte n) 10))))))
                acc))))
  ///
  (verify-guards natchars-aux
    :hints(("Goal" :in-theory (enable basic-natchars)))))

(define natchars
  :short "Convert a natural number into a list of characters."
  ((n natp))
  :returns (chars digit-listp)
  :long "<p>For instance, @('(natchars 123)') is @('(#\\1 #\\2 #\\3)').</p>

<p>This is like ACL2's built-in function @(see explode-nonnegative-integer),
except that it doesn't deal with accumulators and is limited to base 10
numbers.  These simplifications lead to particularly nice rules, e.g., about
@(see digit-list-value), and somewhat better performance:</p>

@({
  ;; Times reported by an AMD FX-8350, Linux, 64-bit CCL:

  ;; 2.80 seconds, 1.1 GB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 10000000 do
            (str::natchars i))))

  ;; 4.28 seconds, 1.1 GB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 10000000 do
            (explode-nonnegative-integer i 10 nil))))
})"
  :inline t
  (or (natchars-aux n nil) '(#\0))
  ///
  (defthm true-listp-of-natchars
    (and (true-listp (natchars n))
         (consp (natchars n)))
    :rule-classes :type-prescription)
  (defthm character-listp-of-natchars
    (character-listp (natchars n)))
  (local (defthm lemma1
           (equal (equal (rev x) (list y))
                  (and (consp x)
                       (not (consp (cdr x)))
                       (equal (car x) y)))
           :hints(("Goal" :in-theory (enable rev)))))
  (local (defthmd lemma2
           (not (equal (basic-natchars n) '(#\0)))
           :hints(("Goal" :in-theory (enable basic-natchars)))))
  (defthm natchars-one-to-one
    (equal (equal (natchars n) (natchars m))
           (equal (nfix n) (nfix m)))
    :hints(("Goal"
            :in-theory (disable basic-natchars-one-to-one)
            :use ((:instance basic-natchars-one-to-one)
                  (:instance lemma2)
                  (:instance lemma2 (n m))))))
  (local (defthm digit-list-value-of-rev-of-basic-natchars
           (equal (digit-list-value (rev (basic-natchars n)))
                  (nfix n))
           :hints(("Goal"
                   :induct (basic-natchars n)
                   :in-theory (e/d (basic-natchars)
                                   (digit-to-char))))))
  (defthm digit-list-value-of-natchars
    (equal (digit-list-value (natchars n))
           (nfix n))))

(define revappend-natchars-aux ((n natp) (acc))
  :parents (revappend-natchars)
  :enabled t
  :verify-guards nil
  (mbe :logic
       (append (basic-natchars n) acc)
       :exec
       (if (zp n)
           acc
         (cons (the character (code-char
                               (the (unsigned-byte 8)
                                    (+ (the (unsigned-byte 8) 48)
                                       (the (unsigned-byte 8)
                                            (rem (the unsigned-byte n) 10))))))
               (revappend-natchars-aux
                (the unsigned-byte (truncate (the unsigned-byte n) 10))
                acc))))
  ///
  (verify-guards revappend-natchars-aux
    :hints(("Goal" :in-theory (enable basic-natchars)))))

(define revappend-natchars
  :short "More efficient version of @('(revappend (natchars n) acc).')"
  ((n natp)
   (acc))
  :returns (new-acc)
  :long "<p>This strange operation can be useful when building strings by
consing together characters in reverse order.</p>"
  :enabled t
  :inline t
  :prepwork ((local (in-theory (enable natchars))))
  (mbe :logic (revappend (natchars n) acc)
       :exec (if (zp n)
                 (cons #\0 acc)
               (revappend-natchars-aux n acc))))

(define natstr
  :short "Convert a natural number into a string with its digits."
  ((n natp))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>For instance, @('(natstr 123)') is @('\"123\"').</p>"
  :inline t
  (implode (natchars n))
  ///
  (defthm digit-listp-of-natstr
    (digit-listp (explode (natstr n))))
  (defthm natstr-one-to-one
    (equal (equal (natstr n) (natstr m))
           (equal (nfix n) (nfix m))))
  (defthm digit-list-value-of-natstr
    (equal (digit-list-value (explode (natstr n)))
           (nfix n)))
  (defthm natstr-nonempty
    (not (equal (natstr n) ""))))

(define natstr-width
  :short "Convert a natural number into a string with the given width."
  ((n natp)
   (width posp))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>Similar to @(see natstr) but produces a fixed number of decimal
digits.  If the input number is smaller it is padded with 0s, and if larger its
more-significant bits are truncated.</p>"
  (b* ((width (mbe :logic (if (posp width) width 1) :exec width))
       (chars (natchars n))
       (width-chars (cond ((<= width (len chars)) (nthcdr (- (len chars) width) chars))
                          (t (append (make-list (- width (len chars)) :initial-element #\0)
                                     chars)))))
    (implode width-chars))
  :prepwork
  ((local (defthm character-listp-of-nthcdr
            (implies (character-listp x)
                     (character-listp (nthcdr n x))))))
  ///
  (defthm digit-listp-of-natstr-width
    (digit-listp (explode (natstr-width n width))))
  (defthm natstr-width-nonempty
    (not (equal (natstr-width n width) ""))))

(define intstr
  :short "Convert an integer into a string with its digits."
  ((i integerp))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>For instance, @('(intstr -123)') is @('\"-123\"').</p>"
  :inline t
  (let ((i (mbe :logic (ifix i) :exec i)))
    (if (< i 0)
        (implode (cons #\- (natchars (- i))))
      (implode (natchars i))))
  ///
  (defthm intstr-nonempty
    (not (equal (intstr i) "")))

  (local (defthm l0
           (implies (digit-listp x)
                    (not (equal x (cons #\- y))))))

  (local (defthm l2
           (implies (equal (char x 0) #\-)
                    (not (equal x "0")))))

  (defthm intstr-one-to-one-positive
    (equal (equal (intstr n) (intstr m))
           (equal (ifix n) (ifix m)))
    :hints(("Goal"
            :in-theory (enable natstr)
            :use ((:instance natstr-one-to-one (n 0) (m m))
                  (:instance natstr-one-to-one (n n) (m 0)))))))

(define intstr-width
  :short "Convert an integer into a string with a fixed number of digits."
  ((i integerp)
   (width posp))
  :returns (str stringp :rule-classes :type-prescription)
  (b* ((i (mbe :logic (ifix i) :exec i))
       (width (mbe :logic (if (posp width) width 1) :exec width))
       (chars (if (< i 0)
                  (b* ((chars (natchars (- i))))
                    (cons #\-
                          (cond ((<= width (len chars)) (nthcdr (- (len chars) width) chars))
                                (t (append (make-list (- width (len chars)) :initial-element #\0)
                                           chars)))))
                (b* ((chars (natchars i)))
                  (cond ((<= width (len chars)) (nthcdr (- (len chars) width) chars))
                        (t (append (make-list (- width (len chars)) :initial-element #\0)
                                   chars)))))))
    (implode chars))
  :prepwork
  ((local (defthm character-listp-of-nthcdr
            (implies (character-listp x)
                     (character-listp (nthcdr n x))))))
  ///
  (defthm intstr-width-nonempty
    (not (equal (intstr-width i width) ""))))

(define natstr-list
  :short "Convert a list of natural numbers into a list of strings."
  ((x nat-listp))
  :returns (strs string-listp)
  (if (atom x)
      nil
    (cons (natstr (car x))
          (natstr-list (cdr x))))
  ///
  (defthm natstr-list-when-atom
    (implies (atom x)
             (equal (natstr-list x)
                    nil)))
  (defthm natstr-list-of-cons
    (equal (natstr-list (cons a x))
           (cons (natstr a)
                 (natstr-list x)))))

(define intstr-list
  :short "Convert a list of integers into a list of strings."
  ((x integer-listp))
  :returns (strs string-listp)
  (if (atom x)
      nil
    (cons (intstr (car x))
          (intstr-list (cdr x))))
  ///
  (defthm intstr-list-when-atom
    (implies (atom x)
             (equal (intstr-list x)
                    nil)))
  (defthm intstr-list-of-cons
    (equal (intstr-list (cons a x))
           (cons (intstr a)
                 (intstr-list x)))))


(define natsize-slow ((x natp))
  :parents (natsize)
  (if (< (lnfix x) 10)
      1
    (the unsigned-byte
      (+ 1 (the unsigned-byte
             (natsize-slow
              (the unsigned-byte (truncate x 10))))))))

(local (defthm natsize-slow-bound
         (implies (posp x)
                  (<= (natsize-slow x) x))
         :rule-classes ((:rewrite) (:linear))
         :hints(("Goal" :in-theory (enable natsize-slow)))))

(define natsize-fast ((x :type (unsigned-byte 29)))
  :parents (natsize)
  :verify-guards nil
  :enabled t
  (mbe :logic (natsize-slow x)
       :exec
       (if (< x 10)
           1
         (the (unsigned-byte 29)
           (+ 1
              (the (unsigned-byte 29)
                (natsize-fast (the (unsigned-byte 29) (truncate x 10))))))))
  ///
  (verify-guards natsize-fast
    :hints(("Goal" :in-theory (enable natsize-slow)))))

(define natsize
  :short "Number of characters in the decimal representation of a natural."
  ((x natp))
  :returns (size posp :rule-classes :type-prescription)
  :inline t
  :verify-guards nil
  (mbe :logic
       (if (< (lnfix x) 10)
           1
         (+ 1 (natsize (truncate x 10))))
       :exec
       (if (<= (mbe :logic (nfix x) :exec x) 536870911)
           (natsize-fast x)
         (natsize-slow x)))
  ///
  (defthm natsize-slow-removal
    (equal (natsize-slow x)
           (natsize x))
    :hints(("Goal" :in-theory (enable natsize-slow))))
  (defthm natsize-fast-removal
    (equal (natsize-fast x)
           (natsize x)))
  (verify-guards natsize$inline))


(define parse-nat-from-charlist
  :short "Parse a natural number from the beginning of a character list."
  ((x   character-listp "Characters to read from.")
   (val natp            "Accumulator for the value of the digits we have read so
                         far; typically 0 to start with.")
   (len natp            "Accumulator for the number of digits we have read;
                         typically 0 to start with."))
  :returns
  (mv (val  "Value of the initial digits as a natural number.")
      (len  "Number of initial digits we read.")
      (rest "The rest of @('x'), past the leading digits."))
  :long "<p>This function is somewhat complicated.  See also @(call
digit-list-value), which is a simpler way to interpret strings where all of the
characters are digits.</p>"
  :split-types t
  (declare (type unsigned-byte val len))
  :verify-guards nil
  (mbe :logic
       (cond ((atom x)
              (mv (nfix val) (nfix len) nil))
             ((digitp (car x))
              (let ((digit-val (digit-val (car x))))
                (parse-nat-from-charlist (cdr x)
                                         (+ digit-val (* 10 (nfix val)))
                                         (+ 1 (nfix len)))))
             (t
              (mv (nfix val) (nfix len) x)))
       :exec
       (b* (((when (atom x))
             (mv val len nil))
            ((the (unsigned-byte 8) code)
             (char-code (the character (car x))))
            ((unless (and (<= (the (unsigned-byte 8) code) (the (unsigned-byte 8) 57))
                          (<= (the (unsigned-byte 8) 48) (the (unsigned-byte 8) code))))
             (mv val len x))
            ((the (unsigned-byte 8) digit-val) (the (unsigned-byte 8)
                                                    (- (the (unsigned-byte 8) code)
                                                       (the (unsigned-byte 8) 48)))))
         (parse-nat-from-charlist
          (cdr x)
          (the unsigned-byte (+ (the (unsigned-byte 8) digit-val)
                                (the unsigned-byte (* 10 val))))
          (the unsigned-byte (+ 1 (the integer len))))))
  ///
  (verify-guards parse-nat-from-charlist
    :hints(("Goal" :in-theory (enable digitp digit-val char-fix))))

  (defthm val-of-parse-nat-from-charlist
    (equal (mv-nth 0 (parse-nat-from-charlist x val len))
           (+ (digit-list-value (take-leading-digits x))
              (* (nfix val) (expt 10 (len (take-leading-digits x))))))
    :hints(("Goal" :in-theory (enable take-leading-digits
                                      digit-list-value))))
  (defthm len-of-parse-nat-from-charlist
    (equal (mv-nth 1 (parse-nat-from-charlist x val len))
           (+ (nfix len) (len (take-leading-digits x))))
    :hints(("Goal" :in-theory (enable take-leading-digits))))
  (defthm rest-of-parse-nat-from-charlist
    (equal (mv-nth 2 (parse-nat-from-charlist x val len))
           (skip-leading-digits x))
    :hints(("Goal" :in-theory (enable skip-leading-digits)))))


(define parse-nat-from-string
  :short "Parse a natural number from a string, at some offset."
  ((x   stringp "The string to parse.")
   (val natp    "Accumulator for the value we have parsed so far; typically 0 to
                 start with.")
   (len natp    "Accumulator for the number of digits we have parsed so far; typically
                 0 to start with.")
   (n   natp    "Offset into @('x') where we should begin parsing.  Must be a valid
                 index into the string, i.e., @('0 <= n < (length x)').")
   (xl  (eql xl (length x)) "Pre-computed length of @('x')."))
  :guard (<= n xl)
  :returns
  (mv (val "The value of the digits we parsed."
           natp :rule-classes :type-prescription)
      (len "The number of digits we parsed."
           natp :rule-classes :type-prescription))
  :split-types t
  (declare (type string x)
           (type unsigned-byte val len n xl))

  :verify-guards nil
  :enabled t
  :long "<p>This function is flexible but very complicated.  See @(see strval)
for a very simple alternative that may do what you want.</p>

<p>The final @('val') and @('len') are guaranteed to be natural numbers;
failure is indicated by a return @('len') of zero.</p>

<p>Because of leading zeroes, the @('len') may be much larger than you would
expect based on @('val') alone.  The @('len') argument is generally useful if
you want to continue parsing through the string, i.e., the @('n') you started
with plus the @('len') you got out will be the next position in the string
after the number.</p>

<p>See also @(see parse-nat-from-charlist) for a simpler function that reads a
number from the start of a character list.  This function also serves as part
of our logical definition.</p>"

  (mbe :logic
       (b* (((mv val len ?rest)
             (parse-nat-from-charlist (nthcdr n (explode x)) val len)))
         (mv val len))
       :exec
       (b* (((when (eql n xl))
             (mv val len))
            ((the (unsigned-byte 8) code)
             (char-code (the character
                             (char (the string x)
                                   (the unsigned-byte n)))))
            ((unless (and (<= (the (unsigned-byte 8) code)
                              (the (unsigned-byte 8) 57))
                          (<= (the (unsigned-byte 8) 48)
                              (the (unsigned-byte 8) code))))
             (mv val len))
            ((the (unsigned-byte 8) digit-val)
             (the (unsigned-byte 8)
                  (- (the (unsigned-byte 8) code)
                     (the (unsigned-byte 8) 48)))))
         (parse-nat-from-string
          (the string x)
          (the unsigned-byte
               (+ (the (unsigned-byte 8) digit-val)
                  (the unsigned-byte (* 10 (the unsigned-byte val)))))
          (the unsigned-byte (+ 1 (the unsigned-byte len)))
          (the unsigned-byte (+ 1 (the unsigned-byte n)))
          (the unsigned-byte xl))))
  ///
  ;; Speed hint
  (local (in-theory (disable acl2::nth-when-bigger
                             acl2::negative-when-natp
                             default-+-2
                             default-+-1
                             default-<-2
                             commutativity-of-+
                             default-<-1
                             ACL2::|x < y  =>  0 < y-x|)))

  (verify-guards parse-nat-from-string
    :hints(("Goal" :in-theory (enable digitp
                                      digit-val
                                      take-leading-digits
                                      digit-list-value
                                      )))))

(define strval
  :short "Interpret a string as a decimal number."
  ((x stringp))
  :returns (value? (or (natp value?)
                       (not value?))
                   :rule-classes :type-prescription)
  :long "<p>For example, @('(strval \"35\")') is 35.  If the string has any
non-decimal digit characters or is empty, we return @('nil').</p>"
  :split-types t
  (declare (type string x))
  (mbe :logic
       (let ((chars (explode x)))
         (and (consp chars)
              (digit-listp chars)
              (digit-list-value chars)))
       :exec
       (b* (((the unsigned-byte xl) (length x))
            ((mv (the unsigned-byte val) (the unsigned-byte len))
             (parse-nat-from-string x 0 0 0 xl)))
         (and (not (eql 0 len))
              (eql len xl)
              val)))
  ///
  (defcong istreqv equal (strval x) 1))
