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

(define bit-digitp (x)
  :short "Recognizer for characters #\\0 and #\\1."
  :returns bool
  :long "<p>@(call bit-digitp) is the binary alternative to @(see digitp).</p>"
  :inline t
  (or (eql x #\0)
      (eql x #\1))
  ///
  (defcong ichareqv equal (bit-digitp x) 1
    :hints(("Goal" :in-theory (enable ichareqv
                                      downcase-char
                                      char-fix))))
  (defthm characterp-when-bit-digitp
    (implies (bit-digitp char)
             (characterp char))
    :rule-classes :compound-recognizer))

(std::deflist bit-digit-listp (x)
  :short "Recognizes lists of @(see bit-digitp) characters."
  (bit-digitp x)
  ///
  (defcong icharlisteqv equal (bit-digit-listp x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv)))))

(define bit-digit-val
  :short "Coerces a @(see bit-digitp) character into a number, 0 or 1."
  ((x bit-digitp :type character))
  :returns (bit bitp :rule-classes :type-prescription)
  :split-types t
  :inline t
  (if (eql x #\1)
      1
    0)
  ///
  (local (in-theory (enable bit-digitp)))

  (defcong ichareqv equal (bit-digit-val x) 1
    :hints(("Goal" :in-theory (enable ichareqv downcase-char char-fix))))

  ;; [Jared] 2016-04-08: shouldn't be needed now that we have a bitp type-prescription
  ;; :returns specifier.
  ;;
  ;; (defthm bit-digit-val-upper-bound
  ;;   (< (bit-digit-val x) 2)
  ;;   :rule-classes ((:rewrite) (:linear)))
  ;;
  ;; (defthm bitp-of-bit-digit-val
  ;;   (acl2::bitp (bit-digit-val x))
  ;;   :rule-classes :type-prescription)

  ;; [Jared] this is kind of ugly, might be better to just have a global rule
  ;; that bitp means unsigned-byte-p 1.
  (defthm unsigned-byte-p-of-bit-digit-val
    (unsigned-byte-p 1 (bit-digit-val x)))
  (defthm equal-of-bit-digit-val-and-bit-digit-val
    (implies (and (bit-digitp x)
                  (bit-digitp y))
             (equal (equal (bit-digit-val x) (bit-digit-val y))
                    (equal x y))))
  (defthm bit-digit-val-of-digit-to-char
    (implies (bitp n)
             (equal (bit-digit-val (digit-to-char n))
                    n))))

(define bit-digit-list-value1
  :parents (bit-digit-list-value)
  ((x bit-digit-listp)
   (val :type unsigned-byte))
  (mbe :logic (if (consp x)
                  (bit-digit-list-value1 (cdr x)
                                         (+ (bit-digit-val (car x))
                                            (ash (nfix val) 1)))
                (nfix val))
       :exec (if (consp x)
                 (bit-digit-list-value1
                  (cdr x)
                  (the unsigned-byte
                    (+ (the (unsigned-byte 8) (if (eql (car x) #\1) 1 0))
                       (the unsigned-byte (ash (the unsigned-byte val) 1)))))
               (the unsigned-byte val)))
  :guard-hints (("Goal" :in-theory (enable bit-digit-val bit-digitp))))

(define bit-digit-list-value
  :short "Coerces a list of bit digits into a natural number."
  ((x bit-digit-listp))
  :returns (value natp :rule-classes :type-prescription)
  :long "<p>For instance, @('(bit-digit-list-value '(#\1 #\0 #\0 #\0))') is 8.
See also @(see parse-bits-from-charlist) for a more flexible function that can
tolerate non-bit digits after the number.</p>"
  :inline t
  :verify-guards nil
  (mbe :logic (if (consp x)
                  (+ (ash (bit-digit-val (car x)) (1- (len x)))
                     (bit-digit-list-value (cdr x)))
                0)
       :exec (bit-digit-list-value1 x 0))
  ///
  (defcong icharlisteqv equal (bit-digit-list-value x) 1
    :hints(("Goal" :in-theory (e/d (icharlisteqv)))))
  (defthm unsigned-byte-p-of-bit-digit-list-value
    (unsigned-byte-p (len x) (bit-digit-list-value x)))
  (defthm bit-digit-list-value-upper-bound
    (< (bit-digit-list-value x)
       (expt 2 (len x)))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal"
            :in-theory (e/d (unsigned-byte-p)
                            (unsigned-byte-p-of-bit-digit-list-value))
            :use ((:instance unsigned-byte-p-of-bit-digit-list-value)))))
  (defthm bit-digit-list-value-upper-bound-free
    (implies (equal n (len x))
             (< (bit-digit-list-value x) (expt 2 n))))
  (defthm bit-digit-list-value1-removal
    (equal (bit-digit-list-value1 x val)
           (+ (bit-digit-list-value x)
              (ash (nfix val) (len x))))
    :hints(("Goal"
            :in-theory (enable bit-digit-list-value1)
            :induct (bit-digit-list-value1 x val))))
  (verify-guards bit-digit-list-value$inline)
  (defthm bit-digit-list-value-of-append
    (equal (bit-digit-list-value (append x (list a)))
           (+ (ash (bit-digit-list-value x) 1)
              (bit-digit-val a)))))

(define skip-leading-bit-digits
  :short "Skip over any leading 0-1 characters at the start of a character list."
  ((x character-listp))
  :returns (tail character-listp :hyp :guard)
  (cond ((atom x)             nil)
        ((bit-digitp (car x)) (skip-leading-bit-digits (cdr x)))
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
    (implies (bit-digitp (car x))
             (< (len (skip-leading-bit-digits x))
                (len x)))))

(define take-leading-bit-digits
  :short "Collect any leading 0-1 characters from the start of a character list."
  ((x character-listp))
  :returns (head character-listp)
  (cond ((atom x)             nil)
        ((bit-digitp (car x)) (cons (car x) (take-leading-bit-digits (cdr x))))
        (t                    nil))
  ///
  (local (defthm l0 ;; Gross, but gets us an equal congruence
           (implies (bit-digitp x)
                    (equal (ichareqv x y)
                           (equal x y)))
           :hints(("Goal" :in-theory (enable ichareqv
                                             downcase-char
                                             bit-digitp
                                             char-fix)))))
  (defcong icharlisteqv equal (take-leading-bit-digits x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))
  (defthm bit-digit-listp-of-take-leading-bit-digits
    (bit-digit-listp (take-leading-bit-digits x)))
  (defthm bound-of-len-of-take-leading-bit-digits
    (<= (len (take-leading-bit-digits x)) (len x))
    :rule-classes :linear)
  (defthm equal-of-take-leading-bit-digits-and-length
    (equal (equal (len (take-leading-bit-digits x)) (len x))
           (bit-digit-listp x)))
  (defthm take-leading-bit-digits-when-bit-digit-listp
    (implies (bit-digit-listp x)
             (equal (take-leading-bit-digits x)
                    (list-fix x))))
  (defthm consp-of-take-leading-bit-digits
    (equal (consp (take-leading-bit-digits x))
           (bit-digitp (car x)))))

(define bit-digit-string-p-aux
  :parents (bit-digit-string-p)
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
       (bit-digit-listp (nthcdr n (explode x)))
       :exec
       (if (eql n xl)
           t
         (and (bit-digitp (char x n))
              (bit-digit-string-p-aux x
                                      (the unsigned-byte (+ 1 n))
                                      xl))))
  ///
  (verify-guards bit-digit-string-p-aux
    :hints(("Goal" :in-theory (enable bit-digit-listp)))))

(define bit-digit-string-p
  :short "Recognizer for strings whose characters are all 0 or 1."
  ((x :type string))
  :returns bool
  :long "<p>Corner case: this accepts the empty string since all of its
characters are bit digits.</p>

<p>Logically this is defined in terms of @(see bit-digit-listp).  But in the
execution, we use a @(see char)-based function that avoids exploding the
string.  This provides much better performance, e.g., on an AMD FX-8350 with
CCL:</p>

@({
    ;; 0.53 seconds, no garbage
    (let ((x \"01001\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::bit-digit-string-p x))))

    ;; 0.99 seconds, 800 MB allocated
    (let ((x \"01001\"))
      (time$ (loop for i fixnum from 1 to 10000000 do
                   (str::bit-digit-listp (explode x)))))
})"
  :inline t
  :enabled t
  (mbe :logic (bit-digit-listp (explode x))
       :exec (bit-digit-string-p-aux x 0 (length x)))
  ///
  (defcong istreqv equal (bit-digit-string-p x) 1))


(define basic-natchars2
  :parents (natchars2)
  :short "Logically simple definition that is similar to @(see natchars2)."
  ((n natp))
  :returns (chars bit-digit-listp)
  :long "<p>This <i>almost</i> computes @('(natchars2 n)'), but when @('n') is
zero it returns @('nil') instead of @('(#\\0)').  You would normally never call
this function directly, but it is convenient for reasoning about @(see
natchars2).</p>"
  (if (zp n)
      nil
    (cons (if (eql (the bit (logand n 1)) 1) #\1 #\0)
          (basic-natchars2 (ash n -1))))
  ///
  (defthm basic-natchars2-when-zp
    (implies (zp n)
             (equal (basic-natchars2 n)
                    nil)))
  (defthm true-listp-of-basic-natchars2
    (true-listp (basic-natchars2 n))
    :rule-classes :type-prescription)
  (defthm character-listp-of-basic-natchars2
    (character-listp (basic-natchars2 n)))
  (defthm basic-natchars2-under-iff
    (iff (basic-natchars2 n)
         (not (zp n))))
  (defthm consp-of-basic-natchars2
    (equal (consp (basic-natchars2 n))
           (if (basic-natchars2 n) t nil)))
  (local (defun my-induction (n m)
           (if (or (zp n)
                   (zp m))
               nil
             (my-induction (ash n -1) (ash m -1)))))
  (defthm basic-natchars2-one-to-one
    (equal (equal (basic-natchars2 n)
                  (basic-natchars2 m))
           (equal (nfix n)
                  (nfix m)))
    :hints(("Goal" :induct (my-induction n m)
            :in-theory (acl2::enable* acl2::ihsext-recursive-redefs)))))

(define natchars2-aux ((n natp) acc)
  :parents (natchars2)
  :verify-guards nil
  :enabled t
  (mbe :logic
       (revappend (basic-natchars2 n) acc)
       :exec
       (if (zp n)
           acc
         (natchars2-aux
          (the unsigned-byte (ash (the unsigned-byte n) -1))
          (cons (if (eql (the bit (logand n 1)) 1) #\1 #\0)
                acc))))
  ///
  (verify-guards natchars2-aux
    :hints(("Goal" :in-theory (enable basic-natchars2)))))

(define natchars2
  :short "Convert a natural number into a list of bits."
  ((n natp))
  :returns (chars bit-digit-listp)
  :long "<p>For instance, @('(natchars 8)') is @('(#\\1 #\\0 #\\0 #\\0)').</p>

<p>This is like ACL2's built-in function @(see explode-nonnegative-integer),
except that it doesn't deal with accumulators and is limited to base 2 numbers.
These simplifications lead to particularly nice rules, e.g., about @(see
bit-digit-list-value), and somewhat better performance:</p>

@({
  ;; Times reported by an AMD FX-8350, Linux, 64-bit CCL:

  ;; .204 seconds, 303 MB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 1000000 do
                     (str::natchars2 i))))

  ;; 1.04 seconds, 303 MB allocated
  (progn (gc$)
         (time (loop for i fixnum from 1 to 1000000 do
            (explode-nonnegative-integer i 2 nil))))
})"
  :inline t
  (or (natchars2-aux n nil) '(#\0))
  ///
  (defthm true-listp-of-natchars2
    (and (true-listp (natchars2 n))
         (consp (natchars2 n)))
    :rule-classes :type-prescription)
  (defthm character-listp-of-natchars2
    (character-listp (natchars2 n)))
  (local (defthm lemma1
           (equal (equal (rev x) (list y))
                  (and (consp x)
                       (not (consp (cdr x)))
                       (equal (car x) y)))
           :hints(("Goal" :in-theory (enable rev)))))
  (local (defthmd lemma2
           (not (equal (basic-natchars2 n) '(#\0)))
           :hints(("Goal" :in-theory (acl2::enable* basic-natchars2
                                                    acl2::ihsext-recursive-redefs)))))
  (defthm natchars2-one-to-one
    (equal (equal (natchars2 n) (natchars2 m))
           (equal (nfix n) (nfix m)))
    :hints(("Goal"
            :in-theory (disable basic-natchars2-one-to-one)
            :use ((:instance basic-natchars2-one-to-one)
                  (:instance lemma2)
                  (:instance lemma2 (n m))))))
  (local (defthm bit-digit-list-value-of-rev-of-basic-natchars2
           (equal (bit-digit-list-value (rev (basic-natchars2 n)))
                  (nfix n))
           :hints(("Goal"
                   :induct (basic-natchars2 n)
                   :in-theory (acl2::enable* basic-natchars2
                                             acl2::ihsext-recursive-redefs
                                             acl2::logcons)))))
  (defthm bit-digit-list-value-of-natchars2
    (equal (bit-digit-list-value (natchars2 n))
           (nfix n))))


(define revappend-natchars2-aux ((n natp) (acc))
  :parents (revappend-natchars2)
  :enabled t
  :verify-guards nil
  (mbe :logic
       (append (basic-natchars2 n) acc)
       :exec
       (if (zp n)
           acc
         (cons (if (eql (the bit (logand n 1)) 1) #\1 #\0)
               (revappend-natchars2-aux
                (the unsigned-byte (ash (the unsigned-byte n) -1))
                acc))))
  ///
  (verify-guards revappend-natchars2-aux
    :hints(("Goal" :in-theory (enable basic-natchars2)))))

(define revappend-natchars2
  :short "More efficient version of @('(revappend (natchars2 n) acc).')"
  ((n natp)
   (acc))
  :returns (new-acc)
  :long "<p>This strange operation can be useful when building strings by
consing together characters in reverse order.</p>"
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable natchars2))))
  (mbe :logic (revappend (natchars2 n) acc)
       :exec (if (zp n)
                 (cons #\0 acc)
               (revappend-natchars2-aux n acc))))

(define natstr2
  :short "Convert a natural number into a string with its bits."
  ((n natp))
  :returns (str stringp :rule-classes :type-prescription)
  :long "<p>For instance, @('(natstr2 8)') is @('\"1000\"').</p>"
  :inline t
  (implode (natchars2 n))
  ///
  (defthm bit-digit-listp-of-natstr
    (bit-digit-listp (explode (natstr2 n))))
  (defthm natstr2-one-to-one
    (equal (equal (natstr2 n) (natstr2 m))
           (equal (nfix n) (nfix m))))
  (defthm bit-digit-list-value-of-natstr
    (equal (bit-digit-list-value (explode (natstr2 n)))
           (nfix n)))
  (defthm natstr2-nonempty
    (not (equal (natstr2 n) ""))))

(define natstr2-list
  :short "Convert a list of natural numbers into a list of bit strings."
  ((x nat-listp))
  :returns (strs string-listp)
  (if (atom x)
      nil
    (cons (natstr2 (car x))
          (natstr2-list (cdr x))))
  ///
  (defthm natstr2-list-when-atom
    (implies (atom x)
             (equal (natstr2-list x)
                    nil)))
  (defthm natstr2-list-of-cons
    (equal (natstr2-list (cons a x))
           (cons (natstr2 a)
                 (natstr2-list x)))))

(define natsize2
  :short "Number of characters in the binary representation of a natural."
  ((x natp))
  :returns (size posp :rule-classes :type-prescription
                 :hints(("Goal" :in-theory (enable integer-length))))
  :inline t
  (if (zp x)
      1
    (integer-length x))
  ///
  (defthm len-of-natchars2
    (equal (len (natchars2 x))
           (natsize2 x))
    :hints(("Goal" :in-theory (acl2::enable* natchars2
                                             basic-natchars2
                                             acl2::ihsext-recursive-redefs))))
  (defthm length-of-natstr2
    (equal (length (natstr2 x))
           (natsize2 x))
    :hints(("Goal" :in-theory (enable natstr2)))))

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
bit-digit-list-value), which is a simpler way to interpret strings where all of
the characters are 0 or 1.</p>"
  :split-types t
  (declare (type unsigned-byte val len))
  :verify-guards nil
  (mbe :logic
       (cond ((atom x)
              (mv (nfix val) (nfix len) nil))
             ((bit-digitp (car x))
              (let ((digit-val (bit-digit-val (car x))))
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
    :hints(("Goal" :in-theory (enable bit-digitp
                                      bit-digit-val
                                      char-fix))))
  (defthm val-of-parse-bits-from-charlist
    (equal (mv-nth 0 (parse-bits-from-charlist x val len))
           (+ (bit-digit-list-value (take-leading-bit-digits x))
              (ash (nfix val) (len (take-leading-bit-digits x)))))
    :hints(("Goal" :in-theory (enable take-leading-bit-digits
                                      bit-digit-list-value))))

  (defthm len-of-parse-bits-from-charlist
    (equal (mv-nth 1 (parse-bits-from-charlist x val len))
           (+ (nfix len) (len (take-leading-bit-digits x))))
    :hints(("Goal" :in-theory (enable take-leading-bit-digits))))

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
  (local (in-theory (disable BOUND-OF-LEN-OF-TAKE-LEADING-BIT-DIGITS
                             ACL2::RIGHT-SHIFT-TO-LOGTAIL
                             BIT-DIGIT-LISTP-OF-CDR-WHEN-BIT-DIGIT-LISTP)))

  (verify-guards parse-bits-from-string
    :hints(("Goal" :in-theory (enable bit-digitp
                                      bit-digit-val
                                      bit-digit-list-value
                                      take-leading-bit-digits)))))


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
              (bit-digit-listp chars)
              (bit-digit-list-value chars)))
       :exec
       (b* (((the unsigned-byte xl) (length x))
            ((mv (the unsigned-byte val) (the unsigned-byte len))
             (parse-bits-from-string x 0 0 0 xl)))
         (and (not (eql 0 len))
              (eql len xl)
              val)))
  ///
  (defcong istreqv equal (strval2 x) 1))
