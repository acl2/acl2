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
; Contributing author: Alessandro Coglio <coglio@kestrel.edu>

(in-package "STR")
(include-book "ieqv")
(include-book "std/basic/defs" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "arithmetic"))
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

(local (defthm unsigned-byte-p-8-of-char-code
         (unsigned-byte-p 8 (char-code x))))

(local (in-theory (disable unsigned-byte-p
                           digit-to-char)))

(local (defthm unsigned-byte-p-8-of-new-trio-on-the-front
         (implies (and (unsigned-byte-p 3 a)
                       (unsigned-byte-p n b))
                  (unsigned-byte-p (+ 3 n) (+ b (ash a n))))
         :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
                                                  acl2::ihsext-inductions)))))

(local (defthm unsigned-byte-p-8-of-new-trio-on-the-front-alt
         (implies (and (unsigned-byte-p 3 a)
                       (unsigned-byte-p n b))
                  (unsigned-byte-p (+ 3 n) (+ (ash a n) b)))
         :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
                                                  acl2::ihsext-inductions)))))

(local (defthm shift-left-of-sum-of-integers
         (implies (and (natp n)
                       (integerp a)
                       (integerp b))
                  (equal (ash (+ a b) n)
                         (+ (ash a n)
                            (ash b n))))
         :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
                                                  acl2::ihsext-inductions)))))

(local (defthm logtail-decreases
         (implies (and (posp n)
                       (posp x))
                  (< (acl2::logtail n x) x))
         :rule-classes ((:rewrite) (:linear))
         :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
                                                  acl2::ihsext-inductions
                                                  acl2::logcons)))))



(defsection octal
  :parents (numbers)
  :short "Functions for working with octal numbers in strings.")

(local (xdoc::set-default-parents octal))

(define oct-digit-char-p (x)
  :short "Recognizer for octal digit characters: 0-7."
  :returns bool
  :long "<p>ACL2 provides @(see digit-char-p) which is more flexible and can
recognize numeric characters in other bases.  @(call oct-digit-char-p) only
recognizes base-8 digits, but is much faster, at least on CCL.  Here is an
experiment you can run in raw lisp, with times reported in CCL on an AMD
FX-8350.</p>

@({
  (defconstant *chars*
    (loop for i from 0 to 255 collect (code-char i)))

  ;; 18.137 seconds
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (digit-char-p c 16))))

  ;; 3.435 seconds
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (str::oct-digit-char-p c))))
})"
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (and (<= (char-code #\0) code) (<= code (char-code #\7))))
       :exec (and (characterp x)
                  (b* (((the (unsigned-byte 8) code) (char-code (the character x))))
                    ;; The ASCII ranges break down to: [48...57] or [65...70] or [97...102]
                    (and (<= code 55)
                         (<= 48 code)))))
  ///
  (defcong ichareqv equal (oct-digit-char-p x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))

  (defthm characterp-when-oct-digit-char-p
    (implies (oct-digit-char-p char)
             (characterp char))
    :rule-classes :compound-recognizer)

  (local (defun test (n)
           (let ((x (code-char n)))
             (and (iff (oct-digit-char-p x)
                       (member x '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7)))
                  (or (zp n)
                      (test (- n 1)))))))

  (local (defthm l0
           (implies (and (test n)
                         (natp i)
                         (natp n)
                         (<= i n))
                    (let ((x (code-char i)))
                      (iff (oct-digit-char-p x)
                           (member x '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7)))))))

  (defthmd oct-digit-char-p-cases
    (iff (oct-digit-char-p x)
         (member x '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7)))
    :hints(("Goal"
            :in-theory (e/d (member) (l0))
            :use ((:instance l0 (n 255) (i (char-code x))))))))


(define nonzero-oct-digit-char-p (x)
  :short "Recognizer for non-zero octal digit characters: 1-7."
  :returns bool
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (and (<= (char-code #\1) code)
                     (<= code (char-code #\7))))
       :exec (and (characterp x)
                  (b* (((the (unsigned-byte 8) code) (char-code (the character x))))
                    (and (<= code 55)
                         (<= 49 code)))))
  ///
  (defcong ichareqv equal (nonzero-oct-digit-char-p x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))
  (defthm oct-digit-char-p-when-nonzero-oct-digit-char-p
    (implies (nonzero-oct-digit-char-p x)
             (oct-digit-char-p x))
    :hints(("Goal" :in-theory (enable oct-digit-char-p)))))


(define oct-digit-char-value
  :short "Coerces a @(see oct-digit-char-p) character into a number."
  ((x oct-digit-char-p))
  :split-types t
  :returns (val natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(oct-digit-char-value #\\a)') is 10.  For any non-@(see
         oct-digit-char-p), 0 is returned.</p>"
  :inline t
  (mbe :logic
       (b* (((unless (oct-digit-char-p x))
             0)
            (code (char-code x)))
         (- code (char-code #\0)))
       :exec
       (the (unsigned-byte 8)
            (- (the (unsigned-byte 8)
                    (char-code (the character x)))
               48)))
  :prepwork
  ((local (in-theory (enable oct-digit-char-p char-fix))))
  ///
  (defcong ichareqv equal (oct-digit-char-value x) 1
    :hints(("Goal" :in-theory (enable ichareqv downcase-char))))
  (defthm oct-digit-char-value-upper-bound
    (< (oct-digit-char-value x) 8)
    :rule-classes ((:rewrite) (:linear)))
  (defthm unsigned-byte-p-of-oct-digit-char-value
    (unsigned-byte-p 3 (oct-digit-char-value x)))
  (defthm equal-of-oct-digit-char-value-and-oct-digit-char-value
    (implies (and (oct-digit-char-p x)
                  (oct-digit-char-p y))
             (equal (equal (oct-digit-char-value x) (oct-digit-char-value y))
                    (ichareqv x y)))
    :hints(("Goal" :in-theory (enable oct-digit-char-p-cases))))
  (defthm oct-digit-char-value-of-digit-to-char
    (implies (and (natp n)
                  (< n 8))
             (equal (oct-digit-char-value (digit-to-char n))
                    n))
    :hints(("Goal" :in-theory (enable digit-to-char)))))


(std::deflist oct-digit-char-listp (x)
  :short "Recognizes lists of @(see oct-digit-char-p) characters."
  (oct-digit-char-p x)
  ///
  (defcong icharlisteqv equal (oct-digit-char-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm character-listp-when-oct-digit-char-listp
    (implies (oct-digit-char-listp x)
             (equal (character-listp x)
                    (true-listp x)))
    :rule-classes ((:rewrite :backchain-limit-lst 1))))


(define oct-digit-chars-value1
  :parents (oct-digit-chars-value)
  ((x oct-digit-char-listp)
   (val :type unsigned-byte))
  :guard-debug t
  (if (consp x)
      (oct-digit-chars-value1
       (cdr x)
       (the unsigned-byte
            (+ (the (unsigned-byte 3) (oct-digit-char-value (car x)))
               (the unsigned-byte (ash (mbe :logic (lnfix val)
                                            :exec val)
                                       3)))))
    (lnfix val)))

(define oct-digit-chars-value
  :short "Coerces a @(see oct-digit-char-listp) into a natural number."
  ((x oct-digit-char-listp))
  :returns (value natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(oct-digit-chars-value '(#\1 #\7))') is 15.  See
         also @(see parse-octal-from-charlist) for a more flexible function that
         can tolerate non-octal characters after the number.</p>"
  :inline t
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (+ (ash (oct-digit-char-value (car x)) (* 3 (1- (len x))))
                     (oct-digit-chars-value (cdr x)))
                0)
       :exec (oct-digit-chars-value1 x 0))
  ///
  (defcong icharlisteqv equal (oct-digit-chars-value x) 1
    :hints(("Goal" :in-theory (e/d (icharlisteqv)))))
  (defthm unsigned-byte-p-of-oct-digit-chars-value
    (unsigned-byte-p (* 3 (len x)) (oct-digit-chars-value x)))
  (defthm oct-digit-chars-value-upper-bound
    (< (oct-digit-chars-value x)
       (expt 2 (* 3 (len x))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :in-theory (e/d (unsigned-byte-p)
                            (unsigned-byte-p-of-oct-digit-chars-value))
            :use ((:instance unsigned-byte-p-of-oct-digit-chars-value)))))
  (defthm oct-digit-chars-value-upper-bound-free
    (implies (equal n (len x))
             (< (oct-digit-chars-value x) (expt 2 (* 3 n)))))
  (defthm oct-digit-chars-value1-removal
    (implies (natp val)
             (equal (oct-digit-chars-value1 x val)
                    (+ (oct-digit-chars-value x)
                       (ash (nfix val) (* 3 (len x))))))
    :hints(("Goal"
            :in-theory (enable oct-digit-chars-value1)
            :induct (oct-digit-chars-value1 x val))))
  (verify-guards oct-digit-chars-value$inline)
  (defthm oct-digit-chars-value-of-append
    (equal (oct-digit-chars-value (append x (list a)))
           (+ (ash (oct-digit-chars-value x) 3)
              (oct-digit-char-value a)))))

(define skip-leading-octal-digits (x)
  :short "Skip over any leading octal digit characters at the start of a character list."
  :returns (tail character-listp :hyp (character-listp x))
  (cond ((atom x)               nil)
        ((oct-digit-char-p (car x)) (skip-leading-octal-digits (cdr x)))
        (t                      x))
  ///
  (local (defun ind (x y)
           (if (or (atom x) (atom y))
               (list x y)
             (ind (cdr x) (cdr y)))))
  (defcong charlisteqv charlisteqv (skip-leading-octal-digits x) 1
    :hints(("Goal" :induct (ind x x-equiv))))
  (defcong icharlisteqv icharlisteqv (skip-leading-octal-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm len-of-skip-leading-octal-digits
    (implies (oct-digit-char-p (car x))
             (< (len (skip-leading-octal-digits x))
                (len x)))))

(define take-leading-oct-digit-chars (x)
  :short "Collect any leading octal digit characters from the start of a character
          list."
  :returns (head character-listp :hyp (character-listp x))
  (cond ((atom x)               nil)
        ((oct-digit-char-p (car x)) (cons (car x) (take-leading-oct-digit-chars (cdr x))))
        (t                      nil))
  ///
  (local (defthm l0 ;; Gross, but gets us an equal congruence
           (implies (oct-digit-char-p x)
                    (equal (ichareqv x y)
                           (equal x y)))
           :hints(("Goal" :in-theory (enable ichareqv
                                             downcase-char
                                             oct-digit-char-p
                                             char-fix)))))
  (defcong icharlisteqv equal (take-leading-oct-digit-chars x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm oct-digit-char-listp-of-take-leading-oct-digit-chars
    (oct-digit-char-listp (take-leading-oct-digit-chars x)))
  (defthm bound-of-len-of-take-leading-oct-digit-chars
    (<= (len (take-leading-oct-digit-chars x)) (len x))
    :rule-classes :linear)
  (defthm equal-of-take-leading-oct-digit-chars-and-length
    (equal (equal (len (take-leading-oct-digit-chars x)) (len x))
           (oct-digit-char-listp x)))
  (defthm take-leading-oct-digit-chars-when-oct-digit-char-listp
    (implies (oct-digit-char-listp x)
             (equal (take-leading-oct-digit-chars x)
                    (list-fix x))))
  (defthm consp-of-take-leading-oct-digit-chars
    (equal (consp (take-leading-oct-digit-chars x))
           (oct-digit-char-p (car x)))))

(define oct-digit-string-p-aux
  :parents (oct-digit-string-p)
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
       (oct-digit-char-listp (nthcdr n (explode x)))
       :exec
       (if (eql n xl)
           t
         (and (oct-digit-char-p (char x n))
              (oct-digit-string-p-aux x
                                      (the unsigned-byte (+ 1 n))
                                      xl))))
  ///
  (verify-guards oct-digit-string-p-aux
    :hints(("Goal" :in-theory (enable oct-digit-char-listp)))))

(define oct-digit-string-p
  :short "Recognizer for strings whose characters are octal digits."
  ((x :type string))
  :returns bool
  :long "<p>Corner case: this accepts the empty string since all of its
characters are octal digits.</p>

<p>Logically this is defined in terms of @(see oct-digit-char-listp).  But in the
execution, we use a @(see char)-based function that avoids exploding the
string.  This provides much better performance, e.g., on an AMD FX-8350 with
CCL:</p>

@({
    ;; 0.13 seconds, no garbage
    (let ((x \"deadbeef\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::oct-digit-string-p x))))

    ;; 1.36 seconds, 1.28 GB allocated
    (let ((x \"deadbeef\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::oct-digit-char-listp (explode x)))))
})"
  :inline t
  :enabled t
  (mbe :logic (oct-digit-char-listp (explode x))
       :exec (oct-digit-string-p-aux x 0 (length x)))
  ///
  (defcong istreqv equal (oct-digit-string-p x) 1))


(define octal-digit-to-char ((n :type (unsigned-byte 3)))
  :short "Convert a number from 0-7 into a octal character."
  :long "<p>ACL2 has a built-in version of this function, @(see digit-to-char),
but @('octal-digit-to-char') is faster:</p>

@({
  (defconstant *codes*
    (loop for i from 0 to 7 collect i))

  ;; .114 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *codes* do (str::octal-digit-to-char c))))

  ;; .379 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *codes* do (digit-to-char c))))

})"

  :guard-hints(("Goal" :in-theory (enable unsigned-byte-p
                                          digit-to-char)))
  :inline t
  :enabled t
  (mbe :logic (digit-to-char n)
       :exec (code-char (the (unsigned-byte 8) (+ 48 n)))))

(define basic-nat-to-oct-chars
  :parents (nat-to-oct-chars)
  :short "Logically simple definition that is similar to @(see nat-to-oct-chars)."
  ((n natp))
  :returns (chars oct-digit-char-listp)
  :long "<p>This <i>almost</i> computes @('(nat-to-oct-chars n)'), but when @('n') is
zero it returns @('nil') instead of @('(#\\0)').  You would normally never call
this function directly, but it is convenient for reasoning about @(see
nat-to-oct-chars).</p>"
  (if (zp n)
      nil
    (cons (octal-digit-to-char (logand n #x7))
          (basic-nat-to-oct-chars (ash n -3))))
  :prepwork
  ((local (defthm l0
            (implies (and (< a 8)
                          (< b 8)
                          (natp a)
                          (natp b))
                     (equal (equal (digit-to-char a) (digit-to-char b))
                            (equal a b)))
            :hints(("Goal" :in-theory (enable digit-to-char)))))
   (local (defthm l1
            (implies (and (< a 8)
                          (natp a))
                     (oct-digit-char-p (digit-to-char a)))
            :hints(("Goal" :in-theory (enable digit-to-char)))))
   (local (in-theory (disable digit-to-char))))
  ///
  (defthm basic-nat-to-oct-chars-when-zp
    (implies (zp n)
             (equal (basic-nat-to-oct-chars n)
                    nil)))
  (defthm true-listp-of-basic-nat-to-oct-chars
    (true-listp (basic-nat-to-oct-chars n))
    :rule-classes :type-prescription)
  (defthm character-listp-of-basic-nat-to-oct-chars
    (character-listp (basic-nat-to-oct-chars n)))
  (defthm basic-nat-to-oct-chars-under-iff
    (iff (basic-nat-to-oct-chars n)
         (not (zp n))))
  (defthm consp-of-basic-nat-to-oct-chars
    (equal (consp (basic-nat-to-oct-chars n))
           (if (basic-nat-to-oct-chars n) t nil)))
  (local (defun my-induction (n m)
           (if (or (zp n)
                   (zp m))
               nil
             (my-induction (ash n -3) (ash m -3)))))
  (local (defthm c0
           (implies (and (integerp x)
                         (natp n))
                    (equal (logior (ash (acl2::logtail n x) n) (acl2::loghead n x))
                           x))
           :hints(("Goal"
                   :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
                                             acl2::ihsext-inductions)))))
  (local (defthm c1
           (implies (and (equal (acl2::logtail k n) (acl2::logtail k m))
                         (equal (acl2::loghead k n) (acl2::loghead k m))
                         (integerp n)
                         (integerp m)
                         (natp k))
                    (equal (equal n m)
                           t))
           :hints(("Goal"
                   :in-theory (disable c0)
                   :use ((:instance c0 (x n) (n k))
                         (:instance c0 (x m) (n k)))))))
  (defthm basic-nat-to-oct-chars-one-to-one
    (equal (equal (basic-nat-to-oct-chars n)
                  (basic-nat-to-oct-chars m))
           (equal (nfix n)
                  (nfix m)))
    :hints(("Goal" :induct (my-induction n m)))))

(define nat-to-oct-chars-aux ((n natp) acc)
  :parents (nat-to-oct-chars)
  :verify-guards nil
  :enabled t
  (mbe :logic
       (revappend (basic-nat-to-oct-chars n) acc)
       :exec
       (if (zp n)
           acc
         (nat-to-oct-chars-aux
          (the unsigned-byte (ash (the unsigned-byte n) -3))
          (cons (octal-digit-to-char
                 (the (unsigned-byte 3) (logand (the unsigned-byte n) #x7)))
                acc))))
  ///
  (verify-guards nat-to-oct-chars-aux
    :hints(("Goal" :in-theory (enable basic-nat-to-oct-chars)))))

(define nat-to-oct-chars
  :short "Convert a natural number into a list of octal bits."
  ((n natp))
  :returns (chars oct-digit-char-listp)
  :long "<p>For instance, @('(nat-to-oct-chars 15)') is @('(#\\1 #\\7)').</p>

<p>This is like ACL2's built-in function @(see explode-nonnegative-integer),
except that it doesn't deal with accumulators and is limited to base-8 numbers.
These simplifications lead to particularly nice rules, e.g., about @(see
oct-digit-chars-value), and somewhat better performance:</p>

@({
  ;; Times reported by an AMD FX-8350, Linux, 64-bit CCL:

  ;; 1.114 seconds, 1.241 GB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 10000000 do
                     (str::nat-to-oct-chars i))))

  ;; 4.727 seconds, 1.241 GB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 10000000 do
            (explode-nonnegative-integer i 8 nil))))
})"
  :inline t
  (or (nat-to-oct-chars-aux n nil) '(#\0))
  ///
  (defthm true-listp-of-nat-to-oct-chars
    (and (true-listp (nat-to-oct-chars n))
         (consp (nat-to-oct-chars n)))
    :rule-classes :type-prescription)
  (defthm character-listp-of-nat-to-oct-chars
    (character-listp (nat-to-oct-chars n)))
  (local (defthm lemma1
           (equal (equal (rev x) (list y))
                  (and (consp x)
                       (not (consp (cdr x)))
                       (equal (car x) y)))
           :hints(("Goal" :in-theory (enable rev)))))
  (local (defthm crock
           (IMPLIES (AND (EQUAL (ACL2::LOGTAIL n x) 0)
                         (EQUAL (ACL2::LOGHEAD n x) 0)
                         (natp n))
                    (zip x))
           :rule-classes :forward-chaining
           :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-inductions
                                                    acl2::ihsext-recursive-redefs
                                                    acl2::zip
                                                    acl2::zp)))))
  (local (defthm crock2
           (implies (AND (EQUAL (ACL2::LOGTAIL n x) 0)
                         (NOT (ZP x))
                         (natp n))
                    (< 0 (acl2::loghead n x)))
           :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-inductions
                                                    acl2::ihsext-recursive-redefs)))))
  (local (defthm crock3
           (equal (equal (digit-to-char n) #\0)
                  (or (zp n)
                      (< 15 n)))
           :hints(("Goal" :in-theory (enable digit-to-char)))))
  (local (defthmd lemma2
           (not (equal (basic-nat-to-oct-chars n) '(#\0)))
           :hints(("Goal" :in-theory (acl2::enable* basic-nat-to-oct-chars
                                                    acl2::ihsext-recursive-redefs)))))
  (defthm nat-to-oct-chars-one-to-one
    (equal (equal (nat-to-oct-chars n) (nat-to-oct-chars m))
           (equal (nfix n) (nfix m)))
    :hints(("Goal"
            :in-theory (disable basic-nat-to-oct-chars-one-to-one)
            :use ((:instance basic-nat-to-oct-chars-one-to-one)
                  (:instance lemma2)
                  (:instance lemma2 (n m))))))
  (local (defthm c0
           (implies (and (integerp x)
                         (natp n))
                    (equal (+ (acl2::loghead n x) (ash (acl2::logtail n x) n))
                           x))
           :hints(("Goal"
                   :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
                                             acl2::ihsext-inductions)))))
  (local (defthm oct-digit-chars-value-of-rev-of-basic-nat-to-oct-chars
           (equal (oct-digit-chars-value (rev (basic-nat-to-oct-chars n)))
                  (nfix n))
           :hints(("Goal"
                   :induct (basic-nat-to-oct-chars n)
                   :in-theory (acl2::enable* basic-nat-to-oct-chars
                                             acl2::ihsext-recursive-redefs
                                             acl2::logcons)))))
  (defthm oct-digit-chars-value-of-nat-to-oct-chars
    (equal (oct-digit-chars-value (nat-to-oct-chars n))
           (nfix n))))

(define revappend-nat-to-oct-chars-aux ((n natp) (acc))
  :parents (revappend-nat-to-oct-chars)
  :enabled t
  :verify-guards nil
  (mbe :logic
       (append (basic-nat-to-oct-chars n) acc)
       :exec
       (if (zp n)
           acc
         (cons (octal-digit-to-char (the (unsigned-byte 4)
                                       (logand (the unsigned-byte n) #x7)))
               (revappend-nat-to-oct-chars-aux
                (the unsigned-byte (ash (the unsigned-byte n) -3))
                acc))))
  ///
  (verify-guards revappend-nat-to-oct-chars-aux
    :hints(("Goal" :in-theory (enable basic-nat-to-oct-chars)))))

(define revappend-nat-to-oct-chars
  :short "More efficient version of @('(revappend (nat-to-oct-chars n) acc).')"
  ((n natp)
   (acc))
  :returns (new-acc)
  :long "<p>This strange operation can be useful when building strings by consing
         together characters in reverse order.</p>"
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable nat-to-oct-chars))))
  (mbe :logic (revappend (nat-to-oct-chars n) acc)
       :exec (if (zp n)
                 (cons #\0 acc)
               (revappend-nat-to-oct-chars-aux n acc))))

(define natstr8
  :short "Convert a natural number into a string with its octal digits."
  ((n natp))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>For instance, @('(natstr8 15)') is @('\"17\"').</p>"
  :inline t
  (implode (nat-to-oct-chars n))
  ///
  (defthm oct-digit-char-listp-of-natstr
    (oct-digit-char-listp (explode (natstr8 n))))
  (defthm natstr8-one-to-one
    (equal (equal (natstr8 n) (natstr8 m))
           (equal (nfix n) (nfix m))))
  (defthm oct-digit-chars-value-of-natstr
    (equal (oct-digit-chars-value (explode (natstr8 n)))
           (nfix n)))
  (defthm natstr8-nonempty
    (not (equal (natstr8 n) ""))))

(define natstr8-list
  :short "Convert a list of natural numbers into a list of octal digit strings."
  ((x nat-listp))
  :returns (strs string-listp)
  (if (atom x)
      nil
    (cons (natstr8 (car x))
          (natstr8-list (cdr x))))
  ///
  (defthm natstr8-list-when-atom
    (implies (atom x)
             (equal (natstr8-list x)
                    nil)))
  (defthm natstr8-list-of-cons
    (equal (natstr8-list (cons a x))
           (cons (natstr8 a)
                 (natstr8-list x)))))

(define natsize8-aux
  :parents (natsize8)
  ((n natp))
  :returns (size natp :rule-classes :type-prescription)
  (if (zp n)
      0
    (+ 1 (natsize8-aux (ash n -3))))
  :prepwork ((local (in-theory (enable nat-to-oct-chars))))
  ///
  ;; BOZO perhaps eventually reimplement this using integer-length.  See also
  ;; hex.lisp for some fledgling steps toward that.
  (defthm natsize8-aux-redef
    (equal (natsize8-aux n)
           (len (basic-nat-to-oct-chars n)))
    :hints(("Goal" :in-theory (enable basic-nat-to-oct-chars)))))

(define natsize8
  :short "Number of characters in the octal representation of a natural."
  ((x natp))
  :returns (size posp :rule-classes :type-prescription)
  :inline t
  (mbe :logic (len (nat-to-oct-chars x))
       :exec  (if (zp x)
                  1
                (natsize8-aux x)))
  :prepwork ((local (in-theory (enable nat-to-oct-chars)))))

(define parse-octal-from-charlist
  :short "Parse a octal number from the beginning of a character list."
  ((x   character-listp "Characters to read from.")
   (val natp            "Accumulator for the value of the octal digits we have read
                         so far; typically 0 to start with.")
   (len natp            "Accumulator for the number of octal digits we have read;
                         typically 0 to start with."))
  :returns (mv (val  "Value of the initial octal digits as a natural number.")
               (len  "Number of initial octal digits we read.")
               (rest "The rest of @('x'), past the leading octal digits."))
  :split-types t
  (declare (type unsigned-byte val len))
  :long "<p>This is like @(call parse-nat-from-charlist), but deals with octal
         digits and returns their octal value.</p>"
  (cond ((atom x)
         (mv (lnfix val) (lnfix len) nil))
        ((oct-digit-char-p (car x))
         (parse-octal-from-charlist
          (cdr x)
          (the unsigned-byte
               (+ (the unsigned-byte (oct-digit-char-value (car x)))
                  (the unsigned-byte (ash (the unsigned-byte (lnfix val)) 3))))
          (the unsigned-byte (+ 1 (the unsigned-byte (lnfix len))))))
        (t
         (mv (lnfix val) (lnfix len) x)))
  ///
  (defthm val-of-parse-octal-from-charlist
      (equal (mv-nth 0 (parse-octal-from-charlist x val len))
             (+ (oct-digit-chars-value (take-leading-oct-digit-chars x))
                (ash (nfix val) (* 3 (len (take-leading-oct-digit-chars x))))))
      :hints(("Goal" :in-theory (enable take-leading-oct-digit-chars
                                        oct-digit-chars-value))))
  (defthm len-of-parse-octal-from-charlist
    (equal (mv-nth 1 (parse-octal-from-charlist x val len))
           (+ (nfix len) (len (take-leading-oct-digit-chars x))))
    :hints(("Goal" :in-theory (enable take-leading-oct-digit-chars))))

  (defthm rest-of-parse-octal-from-charlist
    (equal (mv-nth 2 (parse-octal-from-charlist x val len))
           (skip-leading-octal-digits x))
    :hints(("Goal" :in-theory (enable skip-leading-octal-digits)))))

(define parse-octal-from-string
  :short "Parse a octal number from a string, at some offset."
  ((x   stringp "The string to parse.")
   (val natp    "Accumulator for the value we have parsed so far; typically 0 to
                 start with.")
   (len natp    "Accumulator for the number of octal digits we have parsed so far;
                 typically 0 to start with.")
   (n   natp    "Offset into @('x') where we should begin parsing.  Must be a valid
                 index into the string, i.e., @('0 <= n < (length x)').")
   (xl  (eql xl (length x)) "Pre-computed length of @('x')."))
  :guard (<= n xl)
  :returns
  (mv (val "The value of the octal digits we parsed."
           natp :rule-classes :type-prescription)
      (len "The number of octal digits we parsed."
           natp :rule-classes :type-prescription))
  :split-types t
  (declare (type string x)
           (type unsigned-byte val len n xl))
  :verify-guards nil
  :enabled t
  :long "<p>This function is flexible but very complicated.  See @(see strval8)
for a very simple alternative that may do what you want.</p>

<p>The final @('val') and @('len') are guaranteed to be natural numbers;
failure is indicated by a return @('len') of zero.</p>

<p>Because of leading zeroes, the @('len') may be much larger than you would
expect based on @('val') alone.  The @('len') argument is generally useful if
you want to continue parsing through the string, i.e., the @('n') you started
with plus the @('len') you got out will be the next position in the string
after the number.</p>

<p>See also @(see parse-octal-from-charlist) for a simpler function that reads a
number from the start of a character list.  This function also serves as part
of our logical definition.</p>"

  (mbe :logic
       (b* (((mv val len ?rest)
             (parse-octal-from-charlist (nthcdr n (explode x)) val len)))
         (mv val len))
       :exec
       (b* (((when (eql n xl))
             (mv val len))
            ((the character char) (char (the string x)
                                        (the unsigned-byte n)))
            ((when (oct-digit-char-p char))
             (parse-octal-from-string
              (the string x)
              (the unsigned-byte
                   (+ (the unsigned-byte (oct-digit-char-value char))
                      (the unsigned-byte (ash (the unsigned-byte val) 3))))
              (the unsigned-byte (+ 1 (the unsigned-byte len)))
              (the unsigned-byte (+ 1 n))
              (the unsigned-byte xl))))
         (mv val len)))
  ///
  ;; Minor speed hint
  (local (in-theory (disable BOUND-OF-LEN-OF-TAKE-LEADING-OCT-DIGIT-CHARS
                             ACL2::RIGHT-SHIFT-TO-LOGTAIL
                             OCT-DIGIT-CHAR-LISTP-OF-CDR-WHEN-OCT-DIGIT-CHAR-LISTP)))

  (verify-guards parse-octal-from-string
    :hints(("Goal" :in-theory (enable parse-octal-from-charlist
                                      take-leading-oct-digit-chars
                                      oct-digit-chars-value
                                      )))))


(define strval8
  :short "Interpret a string as a octal number."
  ((x stringp))
  :returns (value? (or (natp value?)
                       (not value?))
                   :rule-classes :type-prescription)
  :long "<p>For example, @('(strval8 \"17\")') is 15.  If the string is empty
or has any non octal digit characters (0-7), we return @('nil').</p>"
  :split-types t
  (declare (type string x))
  (mbe :logic
       (let ((chars (explode x)))
         (and (consp chars)
              (oct-digit-char-listp chars)
              (oct-digit-chars-value chars)))
       :exec
       (b* (((the unsigned-byte xl) (length x))
            ((mv (the unsigned-byte val) (the unsigned-byte len))
             (parse-octal-from-string x 0 0 0 xl)))
         (and (not (eql 0 len))
              (eql len xl)
              val)))
  ///
  (defcong istreqv equal (strval8 x) 1))
