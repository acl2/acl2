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
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable unsigned-byte-p)))
(local (in-theory (acl2::enable* acl2::arith-equiv-forwarding)))

(local (defthm loghead-of-1
         (equal (acl2::loghead 1 n)
                (acl2::logcar n))
         :hints(("Goal" :in-theory (enable acl2::loghead**)))))

#!ACL2
(local (progn
         ;; BOZO re-prove things from ihs-extensions to avoid "apparent" dependency loop
         ;; with defs-program
         (defthm logcar-possibilities
           (or (equal (logcar a) 0)
               (equal (logcar a) 1))
           :rule-classes ((:forward-chaining :trigger-terms ((logcar a))))
           :hints(("Goal" :use logcar-type)))

         (defthm +-of-logcons-with-cin
           (implies (bitp cin)
                    (equal (+ cin
                              (logcons b1 r1)
                              (logcons b2 r2))
                           (logcons (b-xor cin (b-xor b1 b2))
                                    (+ (b-ior (b-and cin b1)
                                              (b-ior (b-and cin b2)
                                                     (b-and b1 b2)))
                                       (ifix r1)
                                       (ifix r2)))))
           :hints(("Goal" :in-theory (enable logcons b-ior b-and b-xor bitp))))

         (defthm +-of-logcons
           (equal (+ (logcons b1 r1)
                     (logcons b2 r2))
                  (logcons (b-xor b1 b2)
                           (+ (b-and b1 b2)
                              (ifix r1)
                              (ifix r2))))
           :hints(("Goal" :use ((:instance +-of-logcons-with-cin (cin 0))))))

         (defthm logcdr-of-+
           (implies (and (integerp a)
                         (integerp b))
                    (equal (logcdr (+ a b))
                           (+ (logcdr a) (logcdr b)
                              (b-and (logcar a) (logcar b))))))))

(local (defthm unsigned-byte-p-of-new-bit-on-the-front
         (implies (and (unsigned-byte-p 1 a)
                       (unsigned-byte-p n b))
                  (unsigned-byte-p (+ 1 n) (+ (ash a n) b)))
         :hints(("Goal" :in-theory (acl2::enable* acl2::ihsext-recursive-redefs)))))

(local (defthm unsigned-byte-p-of-new-bit-on-the-front-alt
         (implies (and (unsigned-byte-p 1 a)
                       (unsigned-byte-p n b))
                  (unsigned-byte-p (+ 1 n) (+ b (ash a n))))
         :hints(("Goal"
                 :in-theory (disable unsigned-byte-p-of-new-bit-on-the-front)
                 :use ((:instance unsigned-byte-p-of-new-bit-on-the-front))))))

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

(defsection binary
  :parents (numbers)
  :short "Functions for working with binary numbers in strings.")

(local (xdoc::set-default-parents binary))

(define bin-digit-char-p (x)
  :short "Recognizer for characters #\\0 and #\\1."
  :returns bool
  :long "<p>@(call bin-digit-char-p) is the binary alternative to @(see dec-digit-char-p).</p>"
  :inline t
  (or (eql x #\0)
      (eql x #\1))
  ///
  (defcong ichareqv equal (bin-digit-char-p x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))
  (defthm characterp-when-bin-digit-char-p
    (implies (bin-digit-char-p char)
             (characterp char))
    :rule-classes :compound-recognizer))

(std::deflist bin-digit-char-listp (x)
  :short "Recognizes lists of @(see bin-digit-char-p) characters."
  (bin-digit-char-p x)
  ///
  (defcong icharlisteqv equal (bin-digit-char-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv)))))

(define bin-digit-char-value
  :short "Coerces a @(see bin-digit-char-p) character into a number, 0 or 1."
  ((x bin-digit-char-p :type character))
  :returns (bit bitp :rule-classes :type-prescription)
  :split-types t
  :inline t
  (if (eql x #\1)
      1
    0)
  ///
  (local (in-theory (enable bin-digit-char-p)))

  (defcong ichareqv equal (bin-digit-char-value x) 1
    :hints(("Goal" :in-theory (enable ichareqv downcase-char char-fix))))

  ;; [Jared] 2016-04-08: shouldn't be needed now that we have a bitp type-prescription
  ;; :returns specifier.
  ;;
  ;; (defthm bin-digit-char-value-upper-bound
  ;;   (< (bin-digit-char-value x) 2)
  ;;   :rule-classes ((:rewrite) (:linear)))
  ;;
  ;; (defthm bitp-of-bin-digit-char-value
  ;;   (acl2::bitp (bin-digit-char-value x))
  ;;   :rule-classes :type-prescription)

  ;; [Jared] this is kind of ugly, might be better to just have a global rule
  ;; that bitp means unsigned-byte-p 1.
  (defthm unsigned-byte-p-of-bin-digit-char-value
    (unsigned-byte-p 1 (bin-digit-char-value x)))
  (defthm equal-of-bin-digit-char-value-and-bin-digit-char-value
    (implies (and (bin-digit-char-p x)
                  (bin-digit-char-p y))
             (equal (equal (bin-digit-char-value x) (bin-digit-char-value y))
                    (equal x y))))
  (defthm bin-digit-char-value-of-digit-to-char
    (implies (bitp n)
             (equal (bin-digit-char-value (digit-to-char n))
                    n))))

(define bin-digit-chars-value1
  :parents (bin-digit-chars-value)
  ((x bin-digit-char-listp)
   (val :type unsigned-byte))
  (mbe :logic (if (consp x)
                  (bin-digit-chars-value1 (cdr x)
                                          (+ (bin-digit-char-value (car x))
                                             (ash (nfix val) 1)))
                (nfix val))
       :exec (if (consp x)
                 (bin-digit-chars-value1
                  (cdr x)
                  (the unsigned-byte
                    (+ (the (unsigned-byte 8) (if (eql (car x) #\1) 1 0))
                       (the unsigned-byte (ash (the unsigned-byte val) 1)))))
               (the unsigned-byte val)))
  :guard-hints (("Goal" :in-theory (enable bin-digit-char-value bin-digit-char-p))))

(define bin-digit-chars-value
  :short "Coerces a list of bit digits into a natural number."
  ((x bin-digit-char-listp))
  :returns (value natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(bin-digit-chars-value '(#\1 #\0 #\0 #\0))') is 8.
See also @(see parse-bits-from-charlist) for a more flexible function that can
tolerate non-bit digits after the number.</p>"
  :inline t
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (+ (ash (bin-digit-char-value (car x)) (1- (len x)))
                     (bin-digit-chars-value (cdr x)))
                0)
       :exec (bin-digit-chars-value1 x 0))
  ///
  (defcong icharlisteqv equal (bin-digit-chars-value x) 1
    :hints(("Goal" :in-theory (e/d (icharlisteqv)))))
  (defthm unsigned-byte-p-of-bin-digit-chars-value
    (unsigned-byte-p (len x) (bin-digit-chars-value x)))
  (defthm bin-digit-chars-value-upper-bound
    (< (bin-digit-chars-value x)
       (expt 2 (len x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :in-theory (e/d (unsigned-byte-p)
                            (unsigned-byte-p-of-bin-digit-chars-value))
            :use ((:instance unsigned-byte-p-of-bin-digit-chars-value)))))
  (defthm bin-digit-chars-value-upper-bound-free
    (implies (equal n (len x))
             (< (bin-digit-chars-value x) (expt 2 n))))
  (defthm bin-digit-chars-value1-removal
    (equal (bin-digit-chars-value1 x val)
           (+ (bin-digit-chars-value x)
              (ash (nfix val) (len x))))
    :hints(("Goal"
            :in-theory (enable bin-digit-chars-value1)
            :induct (bin-digit-chars-value1 x val))))
  (verify-guards bin-digit-chars-value$inline)
  (defthm bin-digit-chars-value-of-append
    (equal (bin-digit-chars-value (append x (list a)))
           (+ (ash (bin-digit-chars-value x) 1)
              (bin-digit-char-value a)))))

(define skip-leading-bit-digits
  :short "Skip over any leading 0-1 characters at the start of a character list."
  ((x character-listp))
  :returns (tail character-listp :hyp :guard)
  (cond ((atom x)             nil)
        ((bin-digit-char-p (car x)) (skip-leading-bit-digits (cdr x)))
        (t                    x))
  ///
  (local (defun ind (x y)
           (if (or (atom x) (atom y))
               (list x y)
             (ind (cdr x) (cdr y)))))
  (defcong charlisteqv charlisteqv (skip-leading-bit-digits x) 1
    :hints(("Goal" :induct (ind x x-equiv))))
  (defcong icharlisteqv icharlisteqv (skip-leading-bit-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm len-of-skip-leading-bit-digits
    (implies (bin-digit-char-p (car x))
             (< (len (skip-leading-bit-digits x))
                (len x)))))

(define take-leading-bin-digit-chars
  :short "Collect any leading 0-1 characters from the start of a character list."
  ((x character-listp))
  :returns (head character-listp)
  (cond ((atom x)             nil)
        ((bin-digit-char-p (car x)) (cons (car x) (take-leading-bin-digit-chars (cdr x))))
        (t                    nil))
  ///
  (local (defthm l0 ;; Gross, but gets us an equal congruence
           (implies (bin-digit-char-p x)
                    (equal (ichareqv x y)
                           (equal x y)))
           :hints(("Goal" :in-theory (enable ichareqv
                                             downcase-char
                                             bin-digit-char-p
                                             char-fix)))))
  (defcong icharlisteqv equal (take-leading-bin-digit-chars x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm bin-digit-char-listp-of-take-leading-bin-digit-chars
    (bin-digit-char-listp (take-leading-bin-digit-chars x)))
  (defthm bound-of-len-of-take-leading-bin-digit-chars
    (<= (len (take-leading-bin-digit-chars x)) (len x))
    :rule-classes :linear)
  (defthm equal-of-take-leading-bin-digit-chars-and-length
    (equal (equal (len (take-leading-bin-digit-chars x)) (len x))
           (bin-digit-char-listp x)))
  (defthm take-leading-bin-digit-chars-when-bin-digit-char-listp
    (implies (bin-digit-char-listp x)
             (equal (take-leading-bin-digit-chars x)
                    (list-fix x))))
  (defthm consp-of-take-leading-bin-digit-chars
    (equal (consp (take-leading-bin-digit-chars x))
           (bin-digit-char-p (car x)))))

(define bin-digit-string-p-aux
  :parents (bin-digit-string-p)
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
       (bin-digit-char-listp (nthcdr n (explode x)))
       :exec
       (if (eql n xl)
           t
         (and (bin-digit-char-p (char x n))
              (bin-digit-string-p-aux x
                                      (the unsigned-byte (+ 1 n))
                                      xl))))
  ///
  (verify-guards bin-digit-string-p-aux
    :hints(("Goal" :in-theory (enable bin-digit-char-listp)))))

(define bin-digit-string-p
  :short "Recognizer for strings whose characters are all 0 or 1."
  ((x :type string))
  :returns bool
  :long "<p>Corner case: this accepts the empty string since all of its
characters are bit digits.</p>

<p>Logically this is defined in terms of @(see bin-digit-char-listp).  But in the
execution, we use a @(see char)-based function that avoids exploding the
string.  This provides much better performance, e.g., on an AMD FX-8350 with
CCL:</p>

@({
    ;; 0.53 seconds, no garbage
    (let ((x \"01001\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::bin-digit-string-p x))))

    ;; 0.99 seconds, 800 MB allocated
    (let ((x \"01001\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::bin-digit-char-listp (explode x)))))
})"
  :inline t
  :enabled t
  (mbe :logic (bin-digit-char-listp (explode x))
       :exec (bin-digit-string-p-aux x 0 (length x)))
  ///
  (defcong istreqv equal (bin-digit-string-p x) 1))


(define basic-nat-to-bin-chars
  :parents (nat-to-bin-chars)
  :short "Logically simple definition that is similar to @(see nat-to-bin-chars)."
  ((n natp))
  :returns (chars bin-digit-char-listp)
  :long "<p>This <i>almost</i> computes @('(nat-to-bin-chars n)'), but when @('n') is
zero it returns @('nil') instead of @('(#\\0)').  You would normally never call
this function directly, but it is convenient for reasoning about @(see
nat-to-bin-chars).</p>"
  (if (zp n)
      nil
    (cons (if (eql (the bit (logand n 1)) 1) #\1 #\0)
          (basic-nat-to-bin-chars (ash n -1))))
  ///
  (defthm basic-nat-to-bin-chars-when-zp
    (implies (zp n)
             (equal (basic-nat-to-bin-chars n)
                    nil)))
  (defthm true-listp-of-basic-nat-to-bin-chars
    (true-listp (basic-nat-to-bin-chars n))
    :rule-classes :type-prescription)
  (defthm character-listp-of-basic-nat-to-bin-chars
    (character-listp (basic-nat-to-bin-chars n)))
  (defthm basic-nat-to-bin-chars-under-iff
    (iff (basic-nat-to-bin-chars n)
         (not (zp n))))
  (defthm consp-of-basic-nat-to-bin-chars
    (equal (consp (basic-nat-to-bin-chars n))
           (if (basic-nat-to-bin-chars n) t nil)))
  (local (defun my-induction (n m)
           (if (or (zp n)
                   (zp m))
               nil
             (my-induction (ash n -1) (ash m -1)))))
  (defthm basic-nat-to-bin-chars-one-to-one
    (equal (equal (basic-nat-to-bin-chars n)
                  (basic-nat-to-bin-chars m))
           (equal (nfix n)
                  (nfix m)))
    :hints(("Goal" :induct (my-induction n m)
            :in-theory (acl2::enable* acl2::ihsext-recursive-redefs)))))

(define nat-to-bin-chars-aux ((n natp) acc)
  :parents (nat-to-bin-chars)
  :verify-guards nil
  :enabled t
  (mbe :logic
       (revappend (basic-nat-to-bin-chars n) acc)
       :exec
       (if (zp n)
           acc
         (nat-to-bin-chars-aux
          (the unsigned-byte (ash (the unsigned-byte n) -1))
          (cons (if (eql (the bit (logand n 1)) 1) #\1 #\0)
                acc))))
  ///
  (verify-guards nat-to-bin-chars-aux
    :hints(("Goal" :in-theory (enable basic-nat-to-bin-chars)))))

(define nat-to-bin-chars
  :short "Convert a natural number into a list of bits."
  ((n natp))
  :returns (chars bin-digit-char-listp)
  :long "<p>For instance, @('(nat-to-dec-chars 8)') is @('(#\\1 #\\0 #\\0 #\\0)').</p>

<p>This is like ACL2's built-in function @(see explode-nonnegative-integer),
except that it doesn't deal with accumulators and is limited to base 2 numbers.
These simplifications lead to particularly nice rules, e.g., about @(see
bin-digit-chars-value), and somewhat better performance:</p>

@({
  ;; Times reported by an AMD FX-8350, Linux, 64-bit CCL:

  ;; .204 seconds, 303 MB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 1000000 do
                     (str::nat-to-bin-chars i))))

  ;; 1.04 seconds, 303 MB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 1000000 do
            (explode-nonnegative-integer i 2 nil))))
})"
  :inline t
  (or (nat-to-bin-chars-aux n nil) '(#\0))
  ///
  (defthm true-listp-of-nat-to-bin-chars
    (and (true-listp (nat-to-bin-chars n))
         (consp (nat-to-bin-chars n)))
    :rule-classes :type-prescription)
  (defthm character-listp-of-nat-to-bin-chars
    (character-listp (nat-to-bin-chars n)))
  (local (defthm lemma1
           (equal (equal (rev x) (list y))
                  (and (consp x)
                       (not (consp (cdr x)))
                       (equal (car x) y)))
           :hints(("Goal" :in-theory (enable rev)))))
  (local (defthmd lemma2
           (not (equal (basic-nat-to-bin-chars n) '(#\0)))
           :hints(("Goal" :in-theory (acl2::enable* basic-nat-to-bin-chars
                                                    acl2::ihsext-recursive-redefs)))))
  (defthm nat-to-bin-chars-one-to-one
    (equal (equal (nat-to-bin-chars n) (nat-to-bin-chars m))
           (equal (nfix n) (nfix m)))
    :hints(("Goal"
            :in-theory (disable basic-nat-to-bin-chars-one-to-one)
            :use ((:instance basic-nat-to-bin-chars-one-to-one)
                  (:instance lemma2)
                  (:instance lemma2 (n m))))))
  (local (defthm bin-digit-chars-value-of-rev-of-basic-nat-to-bin-chars
           (equal (bin-digit-chars-value (rev (basic-nat-to-bin-chars n)))
                  (nfix n))
           :hints(("Goal"
                   :induct (basic-nat-to-bin-chars n)
                   :in-theory (acl2::enable* basic-nat-to-bin-chars
                                             acl2::ihsext-recursive-redefs
                                             acl2::logcons)))))
  (defthm bin-digit-chars-value-of-nat-to-bin-chars
    (equal (bin-digit-chars-value (nat-to-bin-chars n))
           (nfix n))))


(define revappend-nat-to-bin-chars-aux ((n natp) (acc))
  :parents (revappend-nat-to-bin-chars)
  :enabled t
  :verify-guards nil
  (mbe :logic
       (append (basic-nat-to-bin-chars n) acc)
       :exec
       (if (zp n)
           acc
         (cons (if (eql (the bit (logand n 1)) 1) #\1 #\0)
               (revappend-nat-to-bin-chars-aux
                (the unsigned-byte (ash (the unsigned-byte n) -1))
                acc))))
  ///
  (verify-guards revappend-nat-to-bin-chars-aux
    :hints(("Goal" :in-theory (enable basic-nat-to-bin-chars)))))

(define revappend-nat-to-bin-chars
  :short "More efficient version of @('(revappend (nat-to-bin-chars n) acc).')"
  ((n natp)
   (acc))
  :returns (new-acc)
  :long "<p>This strange operation can be useful when building strings by
consing together characters in reverse order.</p>"
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable nat-to-bin-chars))))
  (mbe :logic (revappend (nat-to-bin-chars n) acc)
       :exec (if (zp n)
                 (cons #\0 acc)
               (revappend-nat-to-bin-chars-aux n acc))))

(define nat-to-bin-string
  :short "Convert a natural number into a string with its bits."
  ((n natp))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>For instance, @('(nat-to-bin-string 8)') is @('\"1000\"').</p>"
  :inline t
  (implode (nat-to-bin-chars n))
  ///
  (defthm bin-digit-char-listp-of-nat-to-dec-string
    (bin-digit-char-listp (explode (nat-to-bin-string n))))
  (defthm nat-to-bin-string-one-to-one
    (equal (equal (nat-to-bin-string n) (nat-to-bin-string m))
           (equal (nfix n) (nfix m))))
  (defthm bin-digit-chars-value-of-nat-to-dec-string
    (equal (bin-digit-chars-value (explode (nat-to-bin-string n)))
           (nfix n)))
  (defthm nat-to-bin-string-nonempty
    (not (equal (nat-to-bin-string n) ""))))

(define nat-to-bin-string-list
  :short "Convert a list of natural numbers into a list of bit strings."
  ((x nat-listp))
  :returns (strs string-listp)
  (if (atom x)
      nil
    (cons (nat-to-bin-string (car x))
          (nat-to-bin-string-list (cdr x))))
  ///
  (defthm nat-to-bin-string-list-when-atom
    (implies (atom x)
             (equal (nat-to-bin-string-list x)
                    nil)))
  (defthm nat-to-bin-string-list-of-cons
    (equal (nat-to-bin-string-list (cons a x))
           (cons (nat-to-bin-string a)
                 (nat-to-bin-string-list x)))))

(define nat-to-bin-string-size
  :short "Number of characters in the binary representation of a natural."
  ((x natp))
  :returns (size posp :rule-classes :type-prescription
                 :hints(("Goal" :in-theory (enable integer-length))))
  :inline t
  (if (zp x)
      1
    (integer-length x))
  ///
  (defthm len-of-nat-to-bin-chars
    (equal (len (nat-to-bin-chars x))
           (nat-to-bin-string-size x))
    :hints(("Goal" :in-theory (acl2::enable* nat-to-bin-chars
                                             basic-nat-to-bin-chars
                                             acl2::ihsext-recursive-redefs))))
  (defthm length-of-nat-to-bin-string
    (equal (length (nat-to-bin-string x))
           (nat-to-bin-string-size x))
    :hints(("Goal" :in-theory (enable nat-to-bin-string)))))

(define parse-bits-from-charlist
  :short "Parse a binary number from the beginning of a character list."
  ((x   character-listp "Characters to read from.")
   (val natp            "Accumulator for the value of the bits we have read so
                         far; typically 0 to start with.")
   (len natp            "Accumulator for the number of bits we have read;
                         typically 0 to start with."))
  :returns
  (mv (val  "Value of the initial bits as a natural number.")
      (len  "Number of initial bits we read.")
      (rest "The rest of @('x'), past the leading bits."))
  :long "<p>This function is somewhat complicated.  See also @(call
bin-digit-chars-value), which is a simpler way to interpret strings where all of
the characters are 0 or 1.</p>"
  :split-types t
  (declare (type unsigned-byte val len))
  :verify-guards nil
  (mbe :logic
       (cond ((atom x)
              (mv (nfix val) (nfix len) nil))
             ((bin-digit-char-p (car x))
              (let ((digit-val (bin-digit-char-value (car x))))
                (parse-bits-from-charlist (cdr x)
                                          (+ digit-val (ash (nfix val) 1))
                                          (+ 1 (nfix len)))))
             (t
              (mv (nfix val) (nfix len) x)))
       :exec
       (b* (((when (atom x))
             (mv val len nil))
            (car (car x))
            ((when (equal car #\0))
             (parse-bits-from-charlist (cdr x)
                                       (the unsigned-byte (ash val 1))
                                       (the unsigned-byte (+ 1 len))))
            ((when (equal car #\1))
             (parse-bits-from-charlist (cdr x)
                                       (the unsigned-byte (+ 1 (the unsigned-byte (ash val 1))))
                                       (the unsigned-byte (+ 1 len)))))
         (mv val len x)))
  ///
  (verify-guards parse-bits-from-charlist
    :hints(("Goal" :in-theory (enable bin-digit-char-p
                                      bin-digit-char-value
                                      char-fix))))
  (defthm val-of-parse-bits-from-charlist
    (equal (mv-nth 0 (parse-bits-from-charlist x val len))
           (+ (bin-digit-chars-value (take-leading-bin-digit-chars x))
              (ash (nfix val) (len (take-leading-bin-digit-chars x)))))
    :hints(("Goal" :in-theory (enable take-leading-bin-digit-chars
                                      bin-digit-chars-value))))

  (defthm len-of-parse-bits-from-charlist
    (equal (mv-nth 1 (parse-bits-from-charlist x val len))
           (+ (nfix len) (len (take-leading-bin-digit-chars x))))
    :hints(("Goal" :in-theory (enable take-leading-bin-digit-chars))))

  (defthm rest-of-parse-bits-from-charlist
    (equal (mv-nth 2 (parse-bits-from-charlist x val len))
           (skip-leading-bit-digits x))
    :hints(("Goal" :in-theory (enable skip-leading-bit-digits)))))


(define parse-bits-from-string
  :short "Parse a binary number from a string, at some offset."
  ((x   stringp "The string to parse.")
   (val natp    "Accumulator for the value we have parsed so far; typically 0 to
                 start with.")
   (len natp    "Accumulator for the number of bits we have parsed so far; typically
                 0 to start with.")
   (n   natp    "Offset into @('x') where we should begin parsing.  Must be a valid
                 index into the string, i.e., @('0 <= n < (length x)').")
   (xl  (eql xl (length x)) "Pre-computed length of @('x')."))
  :guard (<= n xl)
  :returns
  (mv (val "The value of the bits we parsed."
           natp :rule-classes :type-prescription)
      (len "The number of bits we parsed."
           natp :rule-classes :type-prescription))
  :split-types t
  (declare (type string x)
           (type unsigned-byte val len n xl))
  :verify-guards nil
  :enabled t
  :long "<p>This function is flexible but very complicated.  See @(see strval2)
for a very simple alternative that may do what you want.</p>

<p>The final @('val') and @('len') are guaranteed to be natural numbers;
failure is indicated by a return @('len') of zero.</p>

<p>Because of leading zeroes, the @('len') may be much larger than you would
expect based on @('val') alone.  The @('len') argument is generally useful if
you want to continue parsing through the string, i.e., the @('n') you started
with plus the @('len') you got out will be the next position in the string
after the number.</p>

<p>See also @(see parse-bits-from-charlist) for a simpler function that reads a
number from the start of a character list.  This function also serves as part
of our logical definition.</p>"

  (mbe :logic
       (b* (((mv val len ?rest)
             (parse-bits-from-charlist (nthcdr n (explode x)) val len)))
         (mv val len))
       :exec
       (b* (((when (eql n xl))
             (mv val len))
            ((the character char) (char (the string x)
                                        (the unsigned-byte n)))
            ((when (equal char #\0))
             (parse-bits-from-string (the string x)
                                     (the unsigned-byte (ash val 1))
                                     (the unsigned-byte (+ 1 len))
                                     (the unsigned-byte (+ 1 n))
                                     (the unsigned-byte xl)))
            ((when (equal char #\1))
             (parse-bits-from-string (the string x)
                                     (the unsigned-byte (+ 1 (the unsigned-byte (ash val 1))))
                                     (the unsigned-byte (+ 1 len))
                                     (the unsigned-byte (+ 1 n))
                                     (the unsigned-byte xl))))
         (mv val len)))
  ///
  ;; Minor speed hint
  (local (in-theory (disable BOUND-OF-LEN-OF-TAKE-LEADING-BIN-DIGIT-CHARS
                             ACL2::RIGHT-SHIFT-TO-LOGTAIL
                             BIN-DIGIT-CHAR-LISTP-OF-CDR-WHEN-BIN-DIGIT-CHAR-LISTP)))

  (verify-guards parse-bits-from-string
    :hints(("Goal" :in-theory (enable bin-digit-char-p
                                      bin-digit-char-value
                                      bin-digit-chars-value
                                      take-leading-bin-digit-chars)))))


(define strval2
  :short "Interpret a string as a binary number."
  ((x stringp))
  :returns (value? (or (natp value?)
                       (not value?))
                   :rule-classes :type-prescription)
  :long "<p>For example, @('(strval2 \"1000\")') is 8.  If the string has any
characters other than 0 or 1, or is empty, we return @('nil').</p>"
  :split-types t
  (declare (type string x))
  (mbe :logic
       (let ((chars (explode x)))
         (and (consp chars)
              (bin-digit-char-listp chars)
              (bin-digit-chars-value chars)))
       :exec
       (b* (((the unsigned-byte xl) (length x))
            ((mv (the unsigned-byte val) (the unsigned-byte len))
             (parse-bits-from-string x 0 0 0 xl)))
         (and (not (eql 0 len))
              (eql len xl)
              val)))
  ///
  (defcong istreqv equal (strval2 x) 1))
