; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.


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

(defsection upcase-charlist
  :parents (case-conversion)
  :short "Convert every character in a list to upper case."

  :long "<p>@(call upcase-charlist) maps @(see upcase-char) across a character
list.</p>

<p>ACL2 has a built-in alternative to this function, @('string-upcase1'), but
it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, @('upcase-charlist') works on arbitrary characters.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when it has no characters that need to be converted.  Of course,
deciding whether some conversion is necessary will marginally slow this
function down when some conversion is necessary, but we think the gain of not
consing outweighs this.  At any rate, this optimization does not affect the
logical definition.</p>"

  (defund charlist-has-some-down-alpha-p (x)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        nil
      (or (down-alpha-p (car x))
          (charlist-has-some-down-alpha-p (cdr x)))))

  (defund upcase-charlist-aux (x acc)
    (declare (xargs :guard (and (character-listp x)
                                (character-listp acc))))
    (if (atom x)
        acc
      (upcase-charlist-aux (cdr x)
                           (cons (upcase-char (car x)) acc))))

  (defund upcase-charlist (x)
    (declare (xargs :guard (character-listp x)
                    :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (upcase-char (car x))
                 (upcase-charlist (cdr x))))
         :exec
         ;; Avoid consing when no characters need to be converted.
         (if (charlist-has-some-down-alpha-p x)
             (reverse (upcase-charlist-aux x nil))
           x)))

  (local (in-theory (enable upcase-charlist
                            upcase-charlist-aux
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
           (upcase-charlist (double-rewrite x)))))



(defsection downcase-charlist
  :parents (case-conversion)
  :short "Convert every character in a list to lower case."

  :long "<p>@(call downcase-charlist) maps @(see downcase-char) across a
character list.</p>

<p>ACL2 has a built-in alternative to this function, @('string-downcase1'), but
it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, @('downcase-charlist') works on arbitrary characters.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when it has no characters that need to be converted.  Of course,
deciding whether some conversion is necessary will marginally slow this
function down when some conversion is necessary, but we think the gain of not
consing outweighs this.  At any rate, this optimization does not affect the
logical definition.</p>"

  (defund charlist-has-some-up-alpha-p (x)
    (declare (xargs :guard (character-listp x)))
    (if (atom x)
        nil
      (or (up-alpha-p (car x))
          (charlist-has-some-up-alpha-p (cdr x)))))

  (defund downcase-charlist-aux (x acc)
    (declare (xargs :guard (and (character-listp x)
                                (character-listp acc))))
    (if (atom x)
        acc
      (downcase-charlist-aux (cdr x)
                             (cons (downcase-char (car x)) acc))))

  (defund downcase-charlist (x)
    (declare (xargs :guard (character-listp x)
                    :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (downcase-char (car x))
                 (downcase-charlist (cdr x))))
         :exec
         ;; Avoid consing when no characters need to be converted.
         (if (charlist-has-some-up-alpha-p x)
             (reverse (downcase-charlist-aux x nil))
           x)))

  (local (in-theory (enable downcase-charlist
                            downcase-charlist-aux
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




(defsection upcase-string
  :parents (case-conversion acl2::string-upcase)
  :short "Convert a string to upper case."

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

  (defund string-has-some-down-alpha-p (x n xl)
    (declare (type string x)
             (type integer n)
             (type integer xl)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (= xl (length x))
                                (<= n xl))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        nil
      (or (down-alpha-p (char x n))
          (string-has-some-down-alpha-p x (+ 1 (lnfix n)) xl))))

  (defund upcase-string-aux (x n xl acc)
    (declare (type string x)
             (type integer n)
             (type integer xl)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (= xl (length x))
                                (<= n xl))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        acc
      (let* ((char   (char x n))
             (upchar (upcase-char char)))
        (upcase-string-aux x (+ 1 (lnfix n)) xl (cons upchar acc)))))

  (defund upcase-string (x)
    (declare (type string x)
             (xargs :verify-guards nil))
    (mbe :logic (implode (upcase-charlist (explode x)))
         :exec
         (let ((xl (length x)))
           (if (not (string-has-some-down-alpha-p x 0 xl))
               ;; Avoid consing when no characters need to be converted.
               x
             (rchars-to-string
              (upcase-string-aux x 0 xl nil))))))

  (local (in-theory (enable upcase-string)))

  (defthm string-has-some-down-alpha-p-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (string-has-some-down-alpha-p x n xl)
                    (charlist-has-some-down-alpha-p (nthcdr n (explode x)))))
    :hints(("Goal" :in-theory (enable string-has-some-down-alpha-p
                                      charlist-has-some-down-alpha-p))))

  (defthm upcase-string-aux-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (upcase-string-aux x n xl acc)
                    (revappend (upcase-charlist (nthcdr n (explode x)))
                               acc)))
    :hints(("Goal" :in-theory (enable upcase-string-aux
                                      upcase-charlist))))

  (verify-guards upcase-string)

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



(defsection downcase-string
  :parents (case-conversion acl2::string-downcase)
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

  (defund string-has-some-up-alpha-p (x n xl)
    (declare (type string x)
             (type integer n)
             (type integer xl)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (= xl (length x))
                                (<= n xl))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        nil
      (or (up-alpha-p (char x n))
          (string-has-some-up-alpha-p x (+ 1 (lnfix n)) xl))))

  (defund downcase-string-aux (x n xl acc)
    (declare (type string x)
             (type integer n)
             (type integer xl)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (= xl (length x))
                                (<= n xl))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        acc
      (let* ((char     (char x n))
             (downchar (downcase-char char)))
        (downcase-string-aux x (+ 1 (lnfix n)) xl (cons downchar acc)))))

  (defund downcase-string (x)
    (declare (type string x)
             (xargs :verify-guards nil))
    (mbe :logic (implode (downcase-charlist (explode x)))
         :exec
         (let ((xl (length x)))
           (if (not (string-has-some-up-alpha-p x 0 xl))
               ;; Avoid consing when no characters need to be converted.
               x
             (rchars-to-string (downcase-string-aux x 0 xl nil))))))

  (local (in-theory (enable downcase-string)))

  (defthm string-has-some-up-alpha-p-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (string-has-some-up-alpha-p x n xl)
                    (charlist-has-some-up-alpha-p (nthcdr n (explode x)))))
    :hints(("Goal" :in-theory (enable string-has-some-up-alpha-p
                                      charlist-has-some-up-alpha-p))))

  (defthm downcase-string-aux-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (downcase-string-aux x n xl acc)
                    (revappend (downcase-charlist (nthcdr n (explode x)))
                               acc)))
    :hints(("Goal" :in-theory (enable downcase-string-aux
                                      downcase-charlist))))

  (verify-guards downcase-string)

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



(defsection upcase-string-list
  :parents (case-conversion)
  :short "Convert every string in a list to upper case."

  (defund upcase-string-list-aux (x acc)
    (declare (xargs :guard (and (string-listp x)
                                (string-listp acc))))
    (if (atom x)
        acc
      (upcase-string-list-aux (cdr x)
                              (cons (upcase-string (car x)) acc))))

  (defund upcase-string-list (x)
    (declare (xargs :guard (string-listp x)
                    :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (upcase-string (car x))
                 (upcase-string-list (cdr x))))
         :exec
         (reverse (upcase-string-list-aux x nil))))

  (local (in-theory (enable upcase-string-list-aux
                            upcase-string-list)))

  (defthm string-listp-upcase-string-list
    (string-listp (upcase-string-list x)))

  (defthm upcase-string-list-aux-is-upcase-string-list
    (equal (upcase-string-list-aux x acc)
           (revappend (upcase-string-list x) acc)))

  (verify-guards upcase-string-list))



(defsection downcase-string-list
  :parents (case-conversion)
  :short "Convert every string in a list to lower case."

  (defund downcase-string-list-aux (x acc)
    (declare (xargs :guard (and (string-listp x)
                                (string-listp acc))))
    (if (atom x)
        acc
      (downcase-string-list-aux (cdr x)
                                (cons (downcase-string (car x)) acc))))

  (defund downcase-string-list (x)
    (declare (xargs :guard (string-listp x)
                    :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (cons (downcase-string (car x))
                 (downcase-string-list (cdr x))))
         :exec
         (reverse (downcase-string-list-aux x nil))))

  (local (in-theory (enable downcase-string-list-aux
                            downcase-string-list)))

  (defthm string-listp-downcase-string-list
    (string-listp (downcase-string-list x)))

  (defthm downcase-string-list-aux-is-downcase-string-list
    (equal (downcase-string-list-aux x acc)
           (revappend (downcase-string-list x) acc)))

  (verify-guards downcase-string-list))



(defsection upcase-first-charlist
  :parents (case-conversion)
  :short "Convert the first character of a character list to upper case."

  (defund upcase-first-charlist (x)
    (declare (xargs :guard (character-listp x)))
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
                x))))

  (local (in-theory (enable upcase-first-charlist)))

  (defcong charlisteqv  equal        (upcase-first-charlist x) 1)
  (defcong icharlisteqv icharlisteqv (upcase-first-charlist x) 1)

  (defthm upcase-first-charlist-when-atom
    (implies (atom x)
             (equal (upcase-first-charlist x)
                    nil)))

  (defthm character-listp-of-upcase-first-charlist
    (implies (character-listp x)
             (character-listp (upcase-first-charlist x))))

  (defthm len-of-upcase-first-charlist
    (equal (len (upcase-first-charlist x))
           (len x)))

  (defthm consp-of-upcase-first-charlist
    (equal (consp (upcase-first-charlist x))
           (consp x)))

  (defthm upcase-first-charlist-under-iff
    (iff (upcase-first-charlist x)
         (consp x))))




(defsection upcase-first
  :parents (case-conversion)
  :short "Convert the first character of a string to upper case."

  :long "<p>@(call upcase-first) returns a copy of the string @('x') except
that the first character is upcased using @(see upcase-char).  If the string is
empty, we return it unchanged.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when its first character is not a lower-case letter.</p>"

  (defund upcase-first (x)
    (declare (type string x)
             (xargs :verify-guards nil))
    (mbe :logic
         (implode (upcase-first-charlist (explode x)))
         :exec
         (if (eql (length x) 0)
             x
           (let ((c (char x 0)))
             (if (down-alpha-p c)
                 (cat (upcase-char-str c) (subseq x 1 nil))
               x)))))

  (local (in-theory (enable upcase-first-charlist
                            upcase-first
                            subseq
                            subseq-list)))

  (verify-guards upcase-first)

  (defthm stringp-of-upcase-first
    (stringp (upcase-first x))
    :rule-classes :type-prescription)

  (defcong streqv equal (upcase-first x) 1)
  (defcong istreqv istreqv (upcase-first x) 1))



(defsection downcase-first-charlist
  :parents (case-conversion)
  :short "Convert the first character of a character list to downper case."

  (defund downcase-first-charlist (x)
    (declare (xargs :guard (character-listp x)))
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
                x))))

  (local (in-theory (enable downcase-first-charlist)))

  (defcong charlisteqv  equal        (downcase-first-charlist x) 1)
  (defcong icharlisteqv icharlisteqv (downcase-first-charlist x) 1)

  (defthm downcase-first-charlist-when-atom
    (implies (atom x)
             (equal (downcase-first-charlist x)
                    nil)))

  (defthm character-listp-of-downcase-first-charlist
    (implies (character-listp x)
             (character-listp (downcase-first-charlist x))))

  (defthm len-of-downcase-first-charlist
    (equal (len (downcase-first-charlist x))
           (len x)))

  (defthm consp-of-downcase-first-charlist
    (equal (consp (downcase-first-charlist x))
           (consp x)))

  (defthm downcase-first-charlist-under-iff
    (iff (downcase-first-charlist x)
         (consp x))))



(defsection downcase-first
  :parents (case-conversion)
  :short "Convert the first character of a string to downper case."

  :long "<p>@(call downcase-first) returns a copy of the string @('x') except
that the first character is downcased using @(see downcase-char).  If the
string is empty, we return it unchanged.</p>

<p>For sometimes-better performance, we avoid consing and simply return @('x')
unchanged when its first character is not an upper-case letter.</p>"

  (defund downcase-first (x)
    (declare (type string x)
             (xargs :verify-guards nil))
    (mbe :logic
         (implode (downcase-first-charlist (explode x)))
         :exec
         (if (eql (length x) 0)
             x
           (let ((c (char x 0)))
             (if (up-alpha-p c)
                 (cat (downcase-char-str c) (subseq x 1 nil))
               x)))))

  (local (in-theory (enable downcase-first-charlist
                            downcase-first
                            subseq
                            subseq-list)))

  (verify-guards downcase-first)

  (defthm stringp-of-downcase-first
    (stringp (downcase-first x))
    :rule-classes :type-prescription)

  (defcong streqv equal (downcase-first x) 1)
  (defcong istreqv istreqv (downcase-first x) 1))


