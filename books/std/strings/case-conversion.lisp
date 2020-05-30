; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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


; case-conversion.lisp
;
; Original author: Sol Swords <sswords@centtech.com>
;
; Updated by Jared Davis <jared@centtech.com> to add documentation, improve
; efficiency in some cases, and integrate into congruences.

(in-package "STR")
(include-book "ieqv")
(include-book "cat")
(local (include-book "arithmetic"))
(local (include-book "subseq"))

(local (defthm append-singleton-crock
         (equal (append (append a (list x)) y)
                (append a (cons x y)))))

(define charlist-has-some-down-alpha-p ((x character-listp))
  :parents (upcase-charlist)
  (if (atom x)
      nil
    (or (down-alpha-p (car x))
        (charlist-has-some-down-alpha-p (cdr x)))))

(define upcase-charlist-aux ((x character-listp) acc)
  :parents (upcase-charlist)
  (if (atom x)
      acc
    (upcase-charlist-aux (cdr x)
                         (cons (upcase-char (car x)) acc))))

(define upcase-charlist ((x character-listp))
  :parents (cases)
  :short "Convert every character in a list to upper case."

  :long "<p>ACL2 has a built-in alternative to this function,
@('string-upcase1'), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('upcase-charlist') works on arbitrary
characters.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when it has no characters that need to be converted.  Of course,
deciding whether some conversion is necessary will marginally slow this
function down when some conversion is necessary, but we think the gain of not
consing outweighs this.  At any rate, this optimization does not affect the
logical definition.</p>"

  :verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (cons (upcase-char (car x))
               (upcase-charlist (cdr x))))
       :exec
       ;; Avoid consing when no characters need to be converted.
       (if (charlist-has-some-down-alpha-p x)
           (reverse (upcase-charlist-aux x nil))
         x))
  ///
  (local (in-theory (enable upcase-charlist-aux
                            charlist-has-some-down-alpha-p)))

  (defthm upcase-charlist-when-atom
    (implies (atom x)
             (equal (upcase-charlist x)
                    nil)))

  (defthm upcase-charlist-of-cons
    (equal (upcase-charlist (cons a x))
           (cons (upcase-char a)
                 (upcase-charlist x))))

  (defcong icharlisteqv equal (upcase-charlist x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))

  (defthm character-listp-upcase-charlist
    (character-listp (upcase-charlist x)))

  (defthm consp-of-upcase-charlist
    (equal (consp (upcase-charlist x))
           (consp x)))

  (defthm upcase-charlist-under-iff
    (iff (upcase-charlist x)
         (consp x))
    :hints(("Goal" :in-theory (enable upcase-charlist))))

  (defthm len-of-upcase-charlist
    (equal (len (upcase-charlist x))
           (len x)))

  (defthm upcase-charlist-aux-is-upcase-charlist
    (equal (upcase-charlist-aux x acc)
           (revappend (upcase-charlist x)
                      acc)))

  (defthm upcase-charlist-does-nothing-unless-charlist-has-some-down-alpha-p
    (implies (and (not (charlist-has-some-down-alpha-p x))
                  (character-listp x))
             (equal (upcase-charlist x)
                    x)))

  (verify-guards upcase-charlist)

  (defthm string-upcase1-is-upcase-charlist
    (equal (acl2::string-upcase1 x)
           (upcase-charlist (double-rewrite x))))

  ;; Mihir M. mod: added a lemma.
  (defthm
    not-charlist-has-some-down-alpha-p-of-upcase-charlist
    (not (charlist-has-some-down-alpha-p
          (upcase-charlist x)))
    :hints
    (("goal"
      :in-theory (enable charlist-has-some-down-alpha-p
                         upcase-charlist)))))


(define charlist-has-some-up-alpha-p ((x character-listp))
  :parents (downcase-charlist)
  (if (atom x)
      nil
    (or (up-alpha-p (car x))
        (charlist-has-some-up-alpha-p (cdr x)))))

(define downcase-charlist-aux ((x character-listp) acc)
  :parents (downcase-charlist)
  (if (atom x)
      acc
    (downcase-charlist-aux (cdr x)
                           (cons (downcase-char (car x)) acc))))


(define downcase-charlist ((x character-listp))
  :parents (cases)
  :short "Convert every character in a list to lower case."

  :long "<p>ACL2 has a built-in alternative to this function,
@('string-downcase1'), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('downcase-charlist') works on
arbitrary characters.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when it has no characters that need to be converted.  Of course,
deciding whether some conversion is necessary will marginally slow this
function down when some conversion is necessary, but we think the gain of not
consing outweighs this.  At any rate, this optimization does not affect the
logical definition.</p>"

  :verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (cons (downcase-char (car x))
               (downcase-charlist (cdr x))))
       :exec
       ;; Avoid consing when no characters need to be converted.
       (if (charlist-has-some-up-alpha-p x)
           (reverse (downcase-charlist-aux x nil))
         x))
  ///
  (local (in-theory (enable downcase-charlist-aux
                            charlist-has-some-up-alpha-p)))

  (defthm downcase-charlist-when-atom
    (implies (atom x)
             (equal (downcase-charlist x)
                    nil)))

  (defthm downcase-charlist-of-cons
    (equal (downcase-charlist (cons a x))
           (cons (downcase-char a)
                 (downcase-charlist x))))

  (defcong icharlisteqv equal (downcase-charlist x) 1
    :hints(("Goal" :in-theory (enable icharlisteqv))))

  (defthm character-listp-downcase-charlist
    (character-listp (downcase-charlist x)))

  (defthm consp-of-downcase-charlist
    (equal (consp (downcase-charlist x))
           (consp x)))

  (defthm downcase-charlist-under-iff
    (iff (downcase-charlist x)
         (consp x))
    :hints(("Goal" :in-theory (enable downcase-charlist))))

  (defthm len-of-downcase-charlist
    (equal (len (downcase-charlist x))
           (len x)))

  (defthm downcase-charlist-aux-is-downcase-charlist
    (equal (downcase-charlist-aux x acc)
           (revappend (downcase-charlist x) acc)))

  (defthm downcase-charlist-does-nothing-unless-charlist-has-some-up-alpha-p
    (implies (and (not (charlist-has-some-up-alpha-p x))
                  (character-listp x))
             (equal (downcase-charlist x)
                    x)))

  (verify-guards downcase-charlist)

  (defthm string-downcase1-redef
    (equal (acl2::string-downcase1 x)
           (downcase-charlist (double-rewrite x)))))


(define string-has-some-down-alpha-p
  :parents (upcase-string)
  ((x  stringp             :type string)
   (n  natp                :type (integer 0 *))
   (xl (eql xl (length x)) :type (integer 0 *)))
  :guard (<= n xl)
  :enabled t
  :split-types t
  :verify-guards nil
  (mbe :logic
       (charlist-has-some-down-alpha-p (nthcdr n (explode x)))
       :exec
       (if (eql n xl)
           nil
         (or (down-alpha-p (char x n))
             (string-has-some-down-alpha-p x (the (integer 0 *) (+ 1 n)) xl))))
  ///
  (local (in-theory (enable charlist-has-some-down-alpha-p)))
  (verify-guards string-has-some-down-alpha-p))


(define upcase-string-aux
  :parents (upcase-string)
  ((x  stringp             :type string)
   (n  natp                :type (integer 0 *))
   (xl (eql xl (length x)) :type (integer 0 *))
   (acc))
  :guard (<= n xl)
  :split-types t
  :verify-guards nil
  :enabled t
  (mbe :logic
       (revappend (upcase-charlist (nthcdr n (explode x))) acc)
       :exec
       (b* (((when (eql n xl))
             acc)
            (char   (char x n))
            (upchar (upcase-char char))
            ((the unsigned-byte n) (+ 1 n)))
         (upcase-string-aux x n xl (cons upchar acc))))
  ///
  (local (in-theory (enable upcase-charlist)))
  (verify-guards upcase-string-aux))


(define upcase-string
  :parents (cases acl2::string-upcase)
  :short "Convert a string to upper case."
  ((x :type string))

  :long "<p>@(call upcase-string) converts a string to upper case, effectively
by transforming each of its characters with @(see upcase-char).</p>

<p>ACL2 has a built-in alternative to this function, @(see
acl2::string-upcase), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('upcase-string') works on strings with
arbitrary characters.</p>

<p>We try to make this fast.  For better performance, we avoid consing and
simply return @('x') unchanged when it has no characters that need to be
converted.  Of course, deciding whether some conversion is necessary will
marginally slow this function down when some conversion is necessary, but we
think the gain of not consing outweighs this.  At any rate, this optimization
does not affect the logical definition.</p>

<p>Despite trying to make this fast, the builtin @('string-upcase') can really
outperform us since it doesn't have to build the intermediate list, etc.  It's
really a shame that @('string-upcase') has such a terrible guard.  Well, at
least we're better when no work needs to be done:</p>

@({
    (time (loop for i fixnum from 1 to 1000000 do
            (str::upcase-string \"Hello, World!\")))  ;; 1.2 seconds, 336 MB
    (time (loop for i fixnum from 1 to 1000000 do
            (string-upcase \"Hello, World!\")))       ;; .26 seconds, 64 MB

    (time (loop for i fixnum from 1 to 1000000 do
            (str::upcase-string \"HELLO, WORLD!\")))  ;; .15 seconds, 0 MB
    (time (loop for i fixnum from 1 to 1000000 do
            (string-upcase \"HELLO, WORLD!\")))       ;; .23 seconds, 64 MB
})"

  :verify-guards nil
  (mbe :logic (implode (upcase-charlist (explode x)))
       :exec
       (let ((xl (length x)))
         (if (not (string-has-some-down-alpha-p x 0 xl))
             ;; Avoid consing when no characters need to be converted.
             x
           (rchars-to-string
            (upcase-string-aux x 0 xl nil)))))
  ///
  (verify-guards upcase-string
    :hints(("Goal" :in-theory (enable string-has-some-down-alpha-p
                                      upcase-string-aux))))

  (defcong istreqv equal (upcase-string x) 1)

  (defthm len-of-upcase-string
    (equal (len (explode (upcase-string x)))
           (len (explode x))))

  (defthm length-of-upcase-string
    (equal (length (upcase-string x))
           (len (explode x))))

  (defthm equal-of-empty-string-with-upcase-string
    (equal (equal ""  (upcase-string x))
           (atom (explode x))))

  (defthm string-upcase-is-upcase-string
    (equal (acl2::string-upcase x)
           (upcase-string (double-rewrite x)))))


(define string-has-some-up-alpha-p
  :parents (downcase-string)
  ((x  stringp             :type string)
   (n  natp                :type (integer 0 *))
   (xl (eql xl (length x)) :type (integer 0 *)))
  :guard (<= n xl)
  :split-types t
  :verify-guards nil
  (mbe :logic
       (charlist-has-some-up-alpha-p (nthcdr n (explode x)))
       :exec
       (if (eql n xl)
           nil
         (or (up-alpha-p (char x n))
             (string-has-some-up-alpha-p x (+ 1 n) xl))))
  ///
  (local (in-theory (enable charlist-has-some-up-alpha-p)))
  (verify-guards string-has-some-up-alpha-p))

(define downcase-string-aux
  :parents (downcase-string)
  :enabled t
  ((x  stringp             :type string)
   (n  natp                :type (integer 0 *))
   (xl (eql xl (length x)) :type (integer 0 *))
   (acc))
  :guard (<= n xl)
  :split-types t
  :verify-guards nil
  (mbe :logic
       (revappend (downcase-charlist (nthcdr n (explode x))) acc)
       :exec
       (if (eql n xl)
           acc
         (let* ((char     (char x n))
                (downchar (downcase-char char)))
           (downcase-string-aux x (+ 1 n) xl (cons downchar acc)))))
  ///
  (local (in-theory (enable downcase-charlist)))
  (verify-guards downcase-string-aux))

(define downcase-string ((x :type string))
  :parents (cases acl2::string-downcase)
  :short "Convert a string to lower case."
  :long "<p>@(call downcase-string) converts a string to lower case,
effectively by transforming each of its characters with @(see
downcase-char).</p>

<p>ACL2 has a built-in alternative to this function, @(see
acl2::string-downcase), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('downcase-string') works on strings
with arbitrary characters.</p>

<p>See also @(see upcase-string), which has more discussion on how we try to
make this fast.</p>"

  :verify-guards nil

  (mbe :logic (implode (downcase-charlist (explode x)))
       :exec
       (let ((xl (length x)))
         (if (not (string-has-some-up-alpha-p x 0 xl))
             ;; Avoid consing when no characters need to be converted.
             x
           (rchars-to-string (downcase-string-aux x 0 xl nil)))))
  ///
  (verify-guards downcase-string
    :hints(("Goal" :in-theory (enable string-has-some-up-alpha-p
                                      downcase-string-aux))))

  (defcong istreqv equal (downcase-string x) 1)

  (defthm len-of-downcase-string
    (equal (len (explode (downcase-string x)))
           (len (explode x))))

  (defthm length-of-downcase-string
    (equal (length (downcase-string x))
           (len (explode x))))

  (defthm equal-of-empty-string-with-downcase-string
    (equal (equal ""  (downcase-string x))
           (atom (explode x))))

  (defthm string-downcase-is-downcase-string
    (equal (acl2::string-downcase x)
           (downcase-string (double-rewrite x)))))


(define upcase-string-list-aux ((x string-listp) acc)
  :parents (upcase-string-list)
  (if (atom x)
      acc
    (upcase-string-list-aux (cdr x)
                            (cons (upcase-string (car x)) acc))))

(define upcase-string-list
  :parents (cases)
  :short "Convert every string in a list to upper case."
  ((x string-listp))
  :returns (upcased string-listp)
  :verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (cons (upcase-string (car x))
               (upcase-string-list (cdr x))))
       :exec
       (reverse (upcase-string-list-aux x nil)))
  ///
  (defthm upcase-string-list-aux-is-upcase-string-list
    (equal (upcase-string-list-aux x acc)
           (revappend (upcase-string-list x) acc))
    :hints(("Goal" :in-theory (enable upcase-string-list-aux))))

  (verify-guards upcase-string-list))


(define downcase-string-list-aux ((x string-listp) acc)
  :parents (downcase-string-list)
  (if (atom x)
      acc
    (downcase-string-list-aux (cdr x)
                              (cons (downcase-string (car x)) acc))))

(define downcase-string-list
  :parents (cases)
  :short "Convert every string in a list to lower case."
  ((x string-listp))
  :returns (downcased string-listp)
  :verify-guards nil
  (mbe :logic
       (if (atom x)
           nil
         (cons (downcase-string (car x))
               (downcase-string-list (cdr x))))
       :exec
       (reverse (downcase-string-list-aux x nil)))
  ///
  (defthm downcase-string-list-aux-is-downcase-string-list
    (equal (downcase-string-list-aux x acc)
           (revappend (downcase-string-list x) acc))
    :hints(("Goal" :in-theory (enable downcase-string-list-aux))))

  (verify-guards downcase-string-list))



(define upcase-first-charlist
  :parents (cases)
  :short "Convert the first character of a character list to upper case."
  ((x character-listp))
  :returns (upcased character-listp)
  (mbe :logic
       (if (atom x)
           nil
         (cons (upcase-char (car x))
               (make-character-list (cdr x))))
       :exec
       (cond ((atom x)
              nil)
             ((down-alpha-p (car x))
              (cons (upcase-char (car x)) (cdr x)))
             (t
              x)))
  ///
  (defcong charlisteqv  equal        (upcase-first-charlist x) 1)
  (defcong icharlisteqv icharlisteqv (upcase-first-charlist x) 1)

  (defthm upcase-first-charlist-when-atom
    (implies (atom x)
             (equal (upcase-first-charlist x)
                    nil)))

  (defthm len-of-upcase-first-charlist
    (equal (len (upcase-first-charlist x))
           (len x)))

  (defthm consp-of-upcase-first-charlist
    (equal (consp (upcase-first-charlist x))
           (consp x)))

  (defthm upcase-first-charlist-under-iff
    (iff (upcase-first-charlist x)
         (consp x))))


(define upcase-first
  :parents (cases)
  :short "Convert the first character of a string to upper case."
  ((x :type string))
  :returns (upcased stringp :rule-classes :type-prescription)

  :long "<p>@(call upcase-first) returns a copy of the string @('x') except
that the first character is upcased using @(see upcase-char).  If the string is
empty, we return it unchanged.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when its first character is not a lower-case letter.</p>"

  (mbe :logic
       (implode (upcase-first-charlist (explode x)))
       :exec
       (if (eql (length x) 0)
           x
         (let ((c (char x 0)))
           (if (down-alpha-p c)
               (cat (upcase-char-str c) (subseq x 1 nil))
             x))))

  :prepwork ((local (in-theory (enable upcase-first-charlist
                                       subseq
                                       subseq-list))))
  ///
  (defcong streqv equal (upcase-first x) 1)
  (defcong istreqv istreqv (upcase-first x) 1))


(define downcase-first-charlist ((x character-listp))
  :parents (cases)
  :short "Convert the first character of a character list to lower case."
  :returns (downcased character-listp)
  (mbe :logic
       (if (atom x)
           nil
         (cons (downcase-char (car x))
               (make-character-list (cdr x))))
       :exec
       (cond ((atom x)
              nil)
             ((up-alpha-p (car x))
              (cons (downcase-char (car x)) (cdr x)))
             (t
              x)))
  ///
  (defcong charlisteqv  equal        (downcase-first-charlist x) 1)
  (defcong icharlisteqv icharlisteqv (downcase-first-charlist x) 1)

  (defthm downcase-first-charlist-when-atom
    (implies (atom x)
             (equal (downcase-first-charlist x)
                    nil)))

  (defthm len-of-downcase-first-charlist
    (equal (len (downcase-first-charlist x))
           (len x)))

  (defthm consp-of-downcase-first-charlist
    (equal (consp (downcase-first-charlist x))
           (consp x)))

  (defthm downcase-first-charlist-under-iff
    (iff (downcase-first-charlist x)
         (consp x))))


(define downcase-first
  :parents (cases)
  :short "Convert the first character of a string to lower case."
  ((x :type string))
  :returns (downcased stringp :rule-classes :type-prescription)

  :long "<p>@(call downcase-first) returns a copy of the string @('x') except
that the first character is downcased using @(see downcase-char).  If the
string is empty, we return it unchanged.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when its first character is not an upper-case letter.</p>"

  (mbe :logic
       (implode (downcase-first-charlist (explode x)))
       :exec
       (if (eql (length x) 0)
           x
         (let ((c (char x 0)))
           (if (up-alpha-p c)
               (cat (downcase-char-str c) (subseq x 1 nil))
             x))))

  :prepwork
  ((local (in-theory (enable downcase-first-charlist
                             subseq
                             subseq-list))))

  ///
  (defcong streqv equal (downcase-first x) 1)
  (defcong istreqv istreqv (downcase-first x) 1))
