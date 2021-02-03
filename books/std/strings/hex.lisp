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

(local (defthm unsigned-byte-p-8-of-new-nibble-on-the-front
         (implies (and (unsigned-byte-p 4 a)
                       (unsigned-byte-p n b))
                  (unsigned-byte-p (+ 4 n) (+ b (ash a n))))
         :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
                                                  acl2::ihsext-inductions)))))

(local (defthm unsigned-byte-p-8-of-new-nibble-on-the-front-alt
         (implies (and (unsigned-byte-p 4 a)
                       (unsigned-byte-p n b))
                  (unsigned-byte-p (+ 4 n) (+ (ash a n) b)))
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

(defsection hex
  :parents (numbers)
  :short "Functions for working with hexadecimal numbers in strings.")

(local (xdoc::set-default-parents hex))

(define hex-digit-char-p (x)
  :short "Recognizer for hexadecimal digit characters: 0-9, A-F, a-f."
  :returns bool
  :long "<p>ACL2 provides @(see digit-char-p) which is more flexible and can
recognize numeric characters in other bases.  @(call hex-digit-char-p) only
recognizes base-16 digits, but is much faster, at least on CCL.  Here is an
experiment you can run in raw lisp, with times reported in CCL on an AMD
FX-8350.</p>

@({
  (defconstant *chars*
    (loop for i from 0 to 255 collect (code-char i)))

  ;; 19.216 seconds
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (digit-char-p c 16))))

  ;; 4.711 seconds
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *chars* do (str::hex-digit-char-p c))))
})"
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (or (and (<= (char-code #\0) code) (<= code (char-code #\9)))
                    (and (<= (char-code #\a) code) (<= code (char-code #\f)))
                    (and (<= (char-code #\A) code) (<= code (char-code #\F)))))
       :exec (and (characterp x)
                  (b* (((the (unsigned-byte 8) code) (char-code (the character x))))
                    ;; The ASCII ranges break down to: [48...57] or [65...70] or [97...102]
                    (if (<= code 70)
                        (if (<= code 57)
                            (<= 48 code)
                          (<= 65 code))
                      (and (<= code 102)
                           (<= 97 code))))))
  ///
  (defcong ichareqv equal (hex-digit-char-p x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))

  (defthm characterp-when-hex-digit-char-p
    (implies (hex-digit-char-p char)
             (characterp char))
    :rule-classes :compound-recognizer)

  (local (defun test (n)
           (let ((x (code-char n)))
             (and (iff (hex-digit-char-p x)
                       (member x '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                                   #\a #\b #\c #\d #\e #\f
                                   #\A #\B #\C #\D #\E #\F)))
                  (or (zp n)
                      (test (- n 1)))))))

  (local (defthm l0
           (implies (and (test n)
                         (natp i)
                         (natp n)
                         (<= i n))
                    (let ((x (code-char i)))
                      (iff (hex-digit-char-p x)
                           (member x '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                                       #\a #\b #\c #\d #\e #\f
                                       #\A #\B #\C #\D #\E #\F)))))))

  (defthmd hex-digit-char-p-cases
    (iff (hex-digit-char-p x)
         (member x '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9
                     #\a #\b #\c #\d #\e #\f
                     #\A #\B #\C #\D #\E #\F)))
    :hints(("Goal"
            :in-theory (e/d (member) (l0))
            :use ((:instance l0 (n 255) (i (char-code x))))))))


(define nonzero-hex-digit-char-p (x)
  :short "Recognizer for non-zero hexadecimal digit characters: 1-9, A-F, a-f."
  :returns bool
  :inline t
  (mbe :logic (let ((code (char-code (char-fix x))))
                (or (and (<= (char-code #\1) code) (<= code (char-code #\9)))
                    (and (<= (char-code #\a) code) (<= code (char-code #\f)))
                    (and (<= (char-code #\A) code) (<= code (char-code #\F)))))
       :exec (and (characterp x)
                  (b* (((the (unsigned-byte 8) code) (char-code (the character x))))
                    (if (<= code 70)
                        (if (<= code 57)
                            (<= 49 code) ;; <-- 49 instead of 48, to exclude 0
                          (<= 65 code))
                      (and (<= code 102)
                           (<= 97 code))))))
  ///
  (defcong ichareqv equal (nonzero-hex-digit-char-p x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))
  (defthm hex-digit-char-p-when-nonzero-hex-digit-char-p
    (implies (nonzero-hex-digit-char-p x)
             (hex-digit-char-p x))
    :hints(("Goal" :in-theory (enable hex-digit-char-p)))))


(define hex-digit-char-value
  :short "Coerces a @(see hex-digit-char-p) character into a number."
  ((x hex-digit-char-p))
  :split-types t
  :returns (val natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(hex-digit-char-value #\\a)') is 10.  For any non-@(see
         hex-digit-char-p), 0 is returned.</p>"
  :inline t
  (mbe :logic
       (b* (((unless (hex-digit-char-p x))
             0)
            (code (char-code x))
            ((when (<= (char-code #\a) code))
             (- code (- (char-code #\a) 10)))
            ((when (<= (char-code #\A) code))
             (- code (- (char-code #\A) 10))))
         (- code (char-code #\0)))
       :exec
       (b* (((the (unsigned-byte 8) code) (char-code (the character x)))
            ((when (<= 97 code))
             (the (unsigned-byte 8) (- code 87)))
            ((when (<= 65 code))
             (the (unsigned-byte 8) (- code 55))))
         (the (unsigned-byte 8) (- code 48))))
  :prepwork
  ((local (in-theory (enable hex-digit-char-p char-fix))))
  ///
  (defcong ichareqv equal (hex-digit-char-value x) 1
    :hints(("Goal" :in-theory (enable ichareqv downcase-char))))
  (defthm hex-digit-char-value-upper-bound
    (< (hex-digit-char-value x) 16)
    :rule-classes ((:rewrite) (:linear)))
  (defthm unsigned-byte-p-of-hex-digit-char-value
    (unsigned-byte-p 4 (hex-digit-char-value x)))
  (defthm equal-of-hex-digit-char-value-and-hex-digit-char-value
    (implies (and (hex-digit-char-p x)
                  (hex-digit-char-p y))
             (equal (equal (hex-digit-char-value x) (hex-digit-char-value y))
                    (ichareqv x y)))
    :hints(("Goal" :in-theory (enable hex-digit-char-p-cases))))
  (defthm hex-digit-char-value-of-digit-to-char
    (implies (and (natp n)
                  (< n 16))
             (equal (hex-digit-char-value (digit-to-char n))
                    n))
    :hints(("Goal" :in-theory (enable digit-to-char)))))


(std::deflist hex-digit-char-listp (x)
  :short "Recognizes lists of @(see hex-digit-char-p) characters."
  (hex-digit-char-p x)
  ///
  (defcong icharlisteqv equal (hex-digit-char-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm character-listp-when-hex-digit-char-listp
    (implies (hex-digit-char-listp x)
             (equal (character-listp x)
                    (true-listp x)))
    :rule-classes ((:rewrite :backchain-limit-lst 1))))


(define hex-digit-chars-value1
  :parents (hex-digit-chars-value)
  ((x hex-digit-char-listp)
   (val :type unsigned-byte))
  :guard-debug t
  (if (consp x)
      (hex-digit-chars-value1
       (cdr x)
       (the unsigned-byte
            (+ (the (unsigned-byte 4) (hex-digit-char-value (car x)))
               (the unsigned-byte (ash (mbe :logic (lnfix val)
                                            :exec val)
                                       4)))))
    (lnfix val)))

(define hex-digit-chars-value
  :short "Coerces a @(see hex-digit-char-listp) into a natural number."
  ((x hex-digit-char-listp))
  :returns (value natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(hex-digit-chars-value '(#\1 #\F))') is 31.  See
         also @(see parse-hex-from-charlist) for a more flexible function that
         can tolerate non-hexadecimal characters after the number.</p>"
  :inline t
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (+ (ash (hex-digit-char-value (car x)) (* 4 (1- (len x))))
                     (hex-digit-chars-value (cdr x)))
                0)
       :exec (hex-digit-chars-value1 x 0))
  ///
  (defcong icharlisteqv equal (hex-digit-chars-value x) 1
    :hints(("Goal" :in-theory (e/d (icharlisteqv)))))
  (defthm unsigned-byte-p-of-hex-digit-chars-value
    (unsigned-byte-p (* 4 (len x)) (hex-digit-chars-value x)))
  (defthm hex-digit-chars-value-upper-bound
    (< (hex-digit-chars-value x)
       (expt 2 (* 4 (len x))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :in-theory (e/d (unsigned-byte-p)
                            (unsigned-byte-p-of-hex-digit-chars-value))
            :use ((:instance unsigned-byte-p-of-hex-digit-chars-value)))))
  (defthm hex-digit-chars-value-upper-bound-free
    (implies (equal n (len x))
             (< (hex-digit-chars-value x) (expt 2 (* 4 n)))))
  (defthm hex-digit-chars-value1-removal
    (implies (natp val)
             (equal (hex-digit-chars-value1 x val)
                    (+ (hex-digit-chars-value x)
                       (ash (nfix val) (* 4 (len x))))))
    :hints(("Goal"
            :in-theory (enable hex-digit-chars-value1)
            :induct (hex-digit-chars-value1 x val))))
  (verify-guards hex-digit-chars-value$inline)
  (defthm hex-digit-chars-value-of-append
    (equal (hex-digit-chars-value (append x (list a)))
           (+ (ash (hex-digit-chars-value x) 4)
              (hex-digit-char-value a)))))

(define skip-leading-hex-digits (x)
  :short "Skip over any leading hex digit characters at the start of a character list."
  :returns (tail character-listp :hyp (character-listp x))
  (cond ((atom x)             nil)
        ((hex-digit-char-p (car x)) (skip-leading-hex-digits (cdr x)))
        (t                    x))
  ///
  (local (defun ind (x y)
           (if (or (atom x) (atom y))
               (list x y)
             (ind (cdr x) (cdr y)))))
  (defcong charlisteqv charlisteqv (skip-leading-hex-digits x) 1
    :hints(("Goal" :induct (ind x x-equiv))))
  (defcong icharlisteqv icharlisteqv (skip-leading-hex-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm len-of-skip-leading-hex-digits
    (implies (hex-digit-char-p (car x))
             (< (len (skip-leading-hex-digits x))
                (len x)))))

(define take-leading-hex-digit-chars (x)
  :short "Collect any leading hex digit characters from the start of a character
          list."
  :returns (head character-listp :hyp (character-listp x))
  (cond ((atom x)             nil)
        ((hex-digit-char-p (car x)) (cons (car x) (take-leading-hex-digit-chars (cdr x))))
        (t                    nil))
  ///
  ;; Unlike decimal/binary/octal versions, here we don't get an EQUAL
  ;; congruence when given ichareqvlists, because we might have, e.g., #\a
  ;; versus #\A.  So, we end up with two different congruences.
  (local (defun ind (x y)
           (if (or (atom x) (atom y))
               (list x y)
             (ind (cdr x) (cdr y)))))
  (defcong charlisteqv equal (take-leading-hex-digit-chars x) 1
    :hints(("Goal" :induct (ind x x-equiv)
            :in-theory (enable charlisteqv))))
  (defcong icharlisteqv icharlisteqv (take-leading-hex-digit-chars x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm hex-digit-char-listp-of-take-leading-hex-digit-chars
    (hex-digit-char-listp (take-leading-hex-digit-chars x)))
  (defthm bound-of-len-of-take-leading-hex-digit-chars
    (<= (len (take-leading-hex-digit-chars x)) (len x))
    :rule-classes :linear)
  (defthm equal-of-take-leading-hex-digit-chars-and-length
    (equal (equal (len (take-leading-hex-digit-chars x)) (len x))
           (hex-digit-char-listp x)))
  (defthm take-leading-hex-digit-chars-when-hex-digit-char-listp
    (implies (hex-digit-char-listp x)
             (equal (take-leading-hex-digit-chars x)
                    (list-fix x))))
  (defthm consp-of-take-leading-hex-digit-chars
    (equal (consp (take-leading-hex-digit-chars x))
           (hex-digit-char-p (car x)))))

(define hex-digit-string-p-aux
  :parents (hex-digit-string-p)
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
       (hex-digit-char-listp (nthcdr n (explode x)))
       :exec
       (if (eql n xl)
           t
         (and (hex-digit-char-p (char x n))
              (hex-digit-string-p-aux x
                                      (the unsigned-byte (+ 1 n))
                                      xl))))
  ///
  (verify-guards hex-digit-string-p-aux
    :hints(("Goal" :in-theory (enable hex-digit-char-listp)))))

(define hex-digit-string-p
  :short "Recognizer for strings whose characters are hexadecimal digits."
  ((x :type string))
  :returns bool
  :long "<p>Corner case: this accepts the empty string since all of its
characters are hex digits.</p>

<p>Logically this is defined in terms of @(see hex-digit-char-listp).  But in the
execution, we use a @(see char)-based function that avoids exploding the
string.  This provides much better performance, e.g., on an AMD FX-8350 with
CCL:</p>

@({
    ;; 0.97 seconds, no garbage
    (let ((x \"deadbeef\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::hex-digit-string-p x))))

    ;; 1.74 seconds, 1.28 GB allocated
    (let ((x \"deadbeef\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::hex-digit-char-listp (explode x)))))
})"
  :inline t
  :enabled t
  (mbe :logic (hex-digit-char-listp (explode x))
       :exec (hex-digit-string-p-aux x 0 (length x)))
  ///
  (defcong istreqv equal (hex-digit-string-p x) 1))


(define hex-digit-to-char ((n :type (unsigned-byte 4)))
  :short "Convert a number from 0-15 into a hex character."
  :long "<p>ACL2 has a built-in version of this function, @(see digit-to-char),
but @('hex-digit-to-char') is faster:</p>

@({
  (defconstant *codes*
    (loop for i from 0 to 15 collect i))

  ;; .217 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *codes* do (str::hex-digit-to-char c))))

  ;; .881 seconds, no garbage
  (time (loop for i fixnum from 1 to 10000000 do
              (loop for c in *codes* do (digit-to-char c))))

})"

  :guard-hints(("Goal" :in-theory (enable unsigned-byte-p
                                          digit-to-char)))
  :inline t
  :enabled t
  (mbe :logic (digit-to-char n)
       :exec
       (if (< n 10)
           (code-char (the (unsigned-byte 8) (+ 48 n)))
         ;; Naively this is (code-char A) + N-10
         ;; But we merge (code-char A) == 65 and -10 together to get 55.
         (code-char (the (unsigned-byte 8) (+ 55 n))))))

(define basic-natchars16
  :parents (natchars16)
  :short "Logically simple definition that is similar to @(see natchars16)."
  ((n natp))
  :returns (chars hex-digit-char-listp)
  :long "<p>This <i>almost</i> computes @('(natchars16 n)'), but when @('n') is
zero it returns @('nil') instead of @('(#\\0)').  You would normally never call
this function directly, but it is convenient for reasoning about @(see
natchars16).</p>"
  (if (zp n)
      nil
    (cons (hex-digit-to-char (logand n #xF))
          (basic-natchars16 (ash n -4))))
  :prepwork
  ((local (defthm l0
            (implies (and (< a 16)
                          (< b 16)
                          (natp a)
                          (natp b))
                     (equal (equal (digit-to-char a) (digit-to-char b))
                            (equal a b)))
            :hints(("Goal" :in-theory (enable digit-to-char)))))
   (local (defthm l1
            (implies (and (< a 16)
                          (natp a))
                     (hex-digit-char-p (digit-to-char a)))
            :hints(("Goal" :in-theory (enable digit-to-char)))))
   (local (in-theory (disable digit-to-char))))
  ///
  (defthm basic-natchars16-when-zp
    (implies (zp n)
             (equal (basic-natchars16 n)
                    nil)))
  (defthm true-listp-of-basic-natchars16
    (true-listp (basic-natchars16 n))
    :rule-classes :type-prescription)
  (defthm character-listp-of-basic-natchars16
    (character-listp (basic-natchars16 n)))
  (defthm basic-natchars16-under-iff
    (iff (basic-natchars16 n)
         (not (zp n))))
  (defthm consp-of-basic-natchars16
    (equal (consp (basic-natchars16 n))
           (if (basic-natchars16 n) t nil)))
  (local (defun my-induction (n m)
           (if (or (zp n)
                   (zp m))
               nil
             (my-induction (ash n -4) (ash m -4)))))
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
  (defthm basic-natchars16-one-to-one
    (equal (equal (basic-natchars16 n)
                  (basic-natchars16 m))
           (equal (nfix n)
                  (nfix m)))
    :hints(("Goal" :induct (my-induction n m)))))

(define natchars16-aux ((n natp) acc)
  :parents (natchars16)
  :verify-guards nil
  :enabled t
  (mbe :logic
       (revappend (basic-natchars16 n) acc)
       :exec
       (if (zp n)
           acc
         (natchars16-aux
          (the unsigned-byte (ash (the unsigned-byte n) -4))
          (cons (hex-digit-to-char
                 (the (unsigned-byte 4) (logand (the unsigned-byte n) #xF)))
                acc))))
  ///
  (verify-guards natchars16-aux
    :hints(("Goal" :in-theory (enable basic-natchars16)))))

(define natchars16
  :short "Convert a natural number into a list of hexadecimal bits."
  ((n natp))
  :returns (chars hex-digit-char-listp)
  :long "<p>For instance, @('(natchars16 31)') is @('(#\\1 #\\F)').</p>

<p>This is like ACL2's built-in function @(see explode-nonnegative-integer),
except that it doesn't deal with accumulators and is limited to base-16 numbers.
These simplifications lead to particularly nice rules, e.g., about @(see
hex-digit-chars-value), and somewhat better performance:</p>

@({
  ;; Times reported by an AMD FX-8350, Linux, 64-bit CCL:

  ;; .732 seconds, 942 MB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 10000000 do
                     (str::natchars16 i))))

  ;; 3.71 seconds, 942 MB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 10000000 do
            (explode-nonnegative-integer i 16 nil))))
})"
  :inline t
  (or (natchars16-aux n nil) '(#\0))
  ///

  (defthm true-listp-of-natchars16
    (and (true-listp (natchars16 n))
         (consp (natchars16 n)))
    :rule-classes :type-prescription)
  (defthm character-listp-of-natchars16
    (character-listp (natchars16 n)))
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
           (not (equal (basic-natchars16 n) '(#\0)))
           :hints(("Goal" :in-theory (acl2::enable* basic-natchars16
                                                    acl2::ihsext-recursive-redefs)))))
  (defthm natchars16-one-to-one
    (equal (equal (natchars16 n) (natchars16 m))
           (equal (nfix n) (nfix m)))
    :hints(("Goal"
            :in-theory (disable basic-natchars16-one-to-one)
            :use ((:instance basic-natchars16-one-to-one)
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
  (local (defthm hex-digit-chars-value-of-rev-of-basic-natchars16
           (equal (hex-digit-chars-value (rev (basic-natchars16 n)))
                  (nfix n))
           :hints(("Goal"
                   :induct (basic-natchars16 n)
                   :in-theory (acl2::enable* basic-natchars16
                                             acl2::ihsext-recursive-redefs
                                             acl2::logcons)))))
  (defthm hex-digit-chars-value-of-natchars16
    (equal (hex-digit-chars-value (natchars16 n))
           (nfix n))))

(define revappend-natchars16-aux ((n natp) (acc))
  :parents (revappend-natchars16)
  :enabled t
  :verify-guards nil
  (mbe :logic
       (append (basic-natchars16 n) acc)
       :exec
       (if (zp n)
           acc
         (cons (hex-digit-to-char (the (unsigned-byte 4)
                                       (logand (the unsigned-byte n) #xF)))
               (revappend-natchars16-aux
                (the unsigned-byte (ash (the unsigned-byte n) -4))
                acc))))
  ///
  (verify-guards revappend-natchars16-aux
    :hints(("Goal" :in-theory (enable basic-natchars16)))))

(define revappend-natchars16
  :short "More efficient version of @('(revappend (natchars16 n) acc).')"
  ((n natp)
   (acc))
  :returns (new-acc)
  :long "<p>This strange operation can be useful when building strings by consing
         together characters in reverse order.</p>"
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable natchars16))))
  (mbe :logic (revappend (natchars16 n) acc)
       :exec (if (zp n)
                 (cons #\0 acc)
               (revappend-natchars16-aux n acc))))

(define natstr16
  :short "Convert a natural number into a string with its hex digits."
  ((n natp))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>For instance, @('(natstr16 31)') is @('\"1F\"').</p>"
  :inline t
  (implode (natchars16 n))
  ///
  (defthm hex-digit-char-listp-of-natstr
    (hex-digit-char-listp (explode (natstr16 n))))
  (defthm natstr16-one-to-one
    (equal (equal (natstr16 n) (natstr16 m))
           (equal (nfix n) (nfix m))))
  (defthm hex-digit-chars-value-of-natstr
    (equal (hex-digit-chars-value (explode (natstr16 n)))
           (nfix n)))
  (defthm natstr16-nonempty
    (not (equal (natstr16 n) ""))))

(define natstr16-list
  :short "Convert a list of natural numbers into a list of hex digit strings."
  ((x nat-listp))
  :returns (strs string-listp)
  (if (atom x)
      nil
    (cons (natstr16 (car x))
          (natstr16-list (cdr x))))
  ///
  (defthm natstr16-list-when-atom
    (implies (atom x)
             (equal (natstr16-list x)
                    nil)))
  (defthm natstr16-list-of-cons
    (equal (natstr16-list (cons a x))
           (cons (natstr16 a)
                 (natstr16-list x)))))


(define natsize16-aux
  :parents (natsize16)
  ((n natp))
  :returns (size natp :rule-classes :type-prescription)
  (if (zp n)
      0
    (+ 1 (natsize16-aux (ash n -4))))
  :prepwork ((local (in-theory (enable natchars16))))
  ///
  ;; BOZO perhaps eventually reimplement this using integer-length.  Here are
  ;; some fledgling steps toward that... natsize16 is probably something like:
  ;;   (+ 1 (ash (+ -1 (integer-length x)) -2)))

  ;; (local (defthm c1
  ;;          (equal (acl2::logtail 2 x)
  ;;                 (acl2::logcdr (acl2::logcdr x)))
  ;;          :hints(("Goal"
  ;;                  :expand ((acl2::logtail 2 x))
  ;;                  :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
  ;;                                            acl2::logtail**)))))

  ;; (local (defthm c2
  ;;          (equal (acl2::logtail 4 x)
  ;;                 (acl2::logcdr (acl2::logcdr (acl2::logcdr (acl2::logcdr x)))))
  ;;          :hints(("Goal"
  ;;                  :expand ((acl2::logtail 4 x))
  ;;                  :in-theory (acl2::enable* acl2::ihsext-recursive-redefs
  ;;                                            acl2::logtail**)))))

  ;; (local (defthm natsize16-aux-redef
  ;;          (equal (natsize16-aux n)
  ;;                 (if (zp n)
  ;;                     0
  ;;                   (+ 1 (natsize16-aux
  ;;                         (acl2::logcdr (acl2::logcdr (acl2::logcdr (acl2::logcdr n))))))))
  ;;          :rule-classes ((:definition :clique (natsize16-aux)
  ;;                          :controller-alist ((natsize16-aux t))))))

  ;; (local (in-theory (disable natsize16-aux)))

  ;; (DEFTHM ACL2::INTEGER-LENGTH**
  ;;   (EQUAL (INTEGER-LENGTH I)
  ;;          (COND ((ZIP I) 0)
  ;;                ((EQUAL I -1) 0)
  ;;                (T (1+ (INTEGER-LENGTH (ACL2::LOGCDR I))))))
  ;;   :HINTS (("goal" :BY ACL2::INTEGER-LENGTH*))
  ;;   :RULE-CLASSES
  ;;   ((:DEFINITION :CLIQUE (INTEGER-LENGTH)
  ;;     :CONTROLLER-ALIST ((INTEGER-LENGTH T)))))

  (defthm natsize16-aux-redef
    (equal (natsize16-aux n)
           (len (basic-natchars16 n)))
    :hints(("Goal" :in-theory (enable basic-natchars16)))))

(define natsize16
  :short "Number of characters in the hexadecimal representation of a natural."
  ((x natp))
  :returns (size posp :rule-classes :type-prescription)
  :inline t
  (mbe :logic (len (natchars16 x))
       :exec
       (if (zp x)
           1
         (natsize16-aux x)))
  :prepwork ((local (in-theory (enable natchars16)))))

(define parse-hex-from-charlist
  :short "Parse a hexadecimal number from the beginning of a character list."
  ((x   character-listp "Characters to read from.")
   (val natp            "Accumulator for the value of the hex digits we have read
                         so far; typically 0 to start with.")
   (len natp            "Accumulator for the number of hex digits we have read;
                         typically 0 to start with."))
  :returns (mv (val  "Value of the initial hex digits as a natural number.")
               (len  "Number of initial hex digits we read.")
               (rest "The rest of @('x'), past the leading hex digits."))
  :split-types t
  (declare (type unsigned-byte val len))
  :long "<p>This is like @(call parse-nat-from-charlist), but deals with hex
         digits and returns their hexadecimal value.</p>"
  (cond ((atom x)
         (mv (lnfix val) (lnfix len) nil))
        ((hex-digit-char-p (car x))
         (parse-hex-from-charlist
          (cdr x)
          (the unsigned-byte
               (+ (the unsigned-byte (hex-digit-char-value (car x)))
                  (the unsigned-byte (ash (the unsigned-byte (lnfix val)) 4))))
          (the unsigned-byte (+ 1 (the unsigned-byte (lnfix len))))))
        (t
         (mv (lnfix val) (lnfix len) x)))
  ///
  (defthm val-of-parse-hex-from-charlist
      (equal (mv-nth 0 (parse-hex-from-charlist x val len))
             (+ (hex-digit-chars-value (take-leading-hex-digit-chars x))
                (ash (nfix val) (* 4 (len (take-leading-hex-digit-chars x))))))
      :hints(("Goal" :in-theory (enable take-leading-hex-digit-chars
                                        hex-digit-chars-value))))
  (defthm len-of-parse-hex-from-charlist
    (equal (mv-nth 1 (parse-hex-from-charlist x val len))
           (+ (nfix len) (len (take-leading-hex-digit-chars x))))
    :hints(("Goal" :in-theory (enable take-leading-hex-digit-chars))))

  (defthm rest-of-parse-hex-from-charlist
    (equal (mv-nth 2 (parse-hex-from-charlist x val len))
           (skip-leading-hex-digits x))
    :hints(("Goal" :in-theory (enable skip-leading-hex-digits)))))

(define parse-hex-from-string
  :short "Parse a hexadecimal number from a string, at some offset."
  ((x   stringp "The string to parse.")
   (val natp    "Accumulator for the value we have parsed so far; typically 0 to
                 start with.")
   (len natp    "Accumulator for the number of hex digits we have parsed so far;
                 typically 0 to start with.")
   (n   natp    "Offset into @('x') where we should begin parsing.  Must be a valid
                 index into the string, i.e., @('0 <= n < (length x)').")
   (xl  (eql xl (length x)) "Pre-computed length of @('x')."))
  :guard (<= n xl)
  :returns
  (mv (val "The value of the hex digits we parsed."
           natp :rule-classes :type-prescription)
      (len "The number of hex digits we parsed."
           natp :rule-classes :type-prescription))
  :split-types t
  (declare (type string x)
           (type unsigned-byte val len n xl))
  :verify-guards nil
  :enabled t
  :long "<p>This function is flexible but very complicated.  See @(see strval16)
for a very simple alternative that may do what you want.</p>

<p>The final @('val') and @('len') are guaranteed to be natural numbers;
failure is indicated by a return @('len') of zero.</p>

<p>Because of leading zeroes, the @('len') may be much larger than you would
expect based on @('val') alone.  The @('len') argument is generally useful if
you want to continue parsing through the string, i.e., the @('n') you started
with plus the @('len') you got out will be the next position in the string
after the number.</p>

<p>See also @(see parse-hex-from-charlist) for a simpler function that reads a
number from the start of a character list.  This function also serves as part
of our logical definition.</p>"

  (mbe :logic
       (b* (((mv val len ?rest)
             (parse-hex-from-charlist (nthcdr n (explode x)) val len)))
         (mv val len))
       :exec
       (b* (((when (eql n xl))
             (mv val len))
            ((the character char) (char (the string x)
                                        (the unsigned-byte n)))
            ((when (hex-digit-char-p char))
             (parse-hex-from-string
              (the string x)
              (the unsigned-byte
                   (+ (the unsigned-byte (hex-digit-char-value char))
                      (the unsigned-byte (ash (the unsigned-byte val) 4))))
              (the unsigned-byte (+ 1 (the unsigned-byte len)))
              (the unsigned-byte (+ 1 n))
              (the unsigned-byte xl))))
         (mv val len)))
  ///
  ;; Minor speed hint
  (local (in-theory (disable BOUND-OF-LEN-OF-TAKE-LEADING-HEX-DIGIT-CHARS
                             ACL2::RIGHT-SHIFT-TO-LOGTAIL
                             HEX-DIGIT-CHAR-LISTP-OF-CDR-WHEN-HEX-DIGIT-CHAR-LISTP)))

  (verify-guards parse-hex-from-string
    :hints(("Goal" :in-theory (enable parse-hex-from-charlist
                                      take-leading-hex-digit-chars
                                      hex-digit-chars-value
                                      )))))


(define strval16
  :short "Interpret a string as a hexadecimal number."
  ((x stringp))
  :returns (value? (or (natp value?)
                       (not value?))
                   :rule-classes :type-prescription)
  :long "<p>For example, @('(strval16 \"1F\")') is 31.  If the string is empty
or has any non hexadecimal digit characters (0-9, A-F, a-f), we return
@('nil').</p>"
  :split-types t
  (declare (type string x))
  (mbe :logic
       (let ((chars (explode x)))
         (and (consp chars)
              (hex-digit-char-listp chars)
              (hex-digit-chars-value chars)))
       :exec
       (b* (((the unsigned-byte xl) (length x))
            ((mv (the unsigned-byte val) (the unsigned-byte len))
             (parse-hex-from-string x 0 0 0 xl)))
         (and (not (eql 0 len))
              (eql len xl)
              val)))
  ///
  (defcong istreqv equal (strval16 x) 1))
