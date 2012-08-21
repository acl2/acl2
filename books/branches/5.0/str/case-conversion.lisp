; ACL2 String Library
; Copyright (C) 2009-2010 Centaur Technology
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
; Updated by Jared Davis <jared@centtech.com> to add documentation and improve
; efficiency in some cases.

(in-package "STR")
(include-book "char-case")
(local (include-book "unicode/rev" :dir :system))
(local (include-book "arithmetic"))


(local (defthm append-singleton-crock
         (equal (append (append a (list x)) y)
                (append a (cons x y)))))





(defsection upcase-charlist
  :parents (case-conversion)
  :short "Convert every character in a list to upper case."

  :long "<p>@(call upcase-charlist) maps @(see upcase-char) across a character
list.</p>

<p>ACL2 has a built-in alternative to this function, <tt>string-upcase1</tt>,
but it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, <tt>upcase-charlist</tt> works on arbitrary characters.</p>

<p>For sometimes-better performance, we avoid consing and simply return
<tt>x</tt> unchanged when it has no characters that need to be converted.  Of
course, deciding whether some conversion is necessary will marginally slow this
function down when some conversion is necessary, but we think the gain of not
consing outweighs this.  At any rate, this optimization does not affect the
logical definition.</p>"

  (defund charlist-has-some-down-alpha-p (x)
    (declare (xargs :guard (character-listp x)
                    :guard-hints(("Goal" :in-theory (enable down-alpha-p)))))
    (if (atom x)
        nil
      (or (mbe :logic (down-alpha-p (car x))
               :exec (let ((code (char-code (car x))))
                       (declare (type (unsigned-byte 8) code))
                       (and (<= (little-a) code)
                            (<= code (little-z)))))
          (charlist-has-some-down-alpha-p (cdr x)))))

  (defund upcase-charlist-aux (x acc)
    (declare (Xargs :guard (and (character-listp x)
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

  (defthm character-listp-upcase-charlist
    (character-listp (upcase-charlist x)))

  (defcong charlisteqv equal (upcase-charlist x) 1
    :hints(("Goal" :in-theory (enable charlisteqv))))

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

  (defthm len-of-upcase-charlist
    (equal (len (upcase-charlist x))
           (len x)))

  (defthm string-upcase1-is-upcase-charlist
    (equal (acl2::string-upcase1 x)
           (upcase-charlist (double-rewrite x)))))





(defsection downcase-charlist
  :parents (case-conversion)
  :short "Convert every character in a list to lower case."

  :long "<p>@(call downcase-charlist) maps @(see downcase-char) across a
character list.</p>

<p>ACL2 has a built-in alternative to this function, <tt>string-downcase1</tt>,
but it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, <tt>downcase-charlist</tt> works on arbitrary characters.</p>

<p>For sometimes-better performance, we avoid consing and simply return
<tt>x</tt> unchanged when it has no characters that need to be converted.  Of
course, deciding whether some conversion is necessary will marginally slow this
function down when some conversion is necessary, but we think the gain of not
consing outweighs this.  At any rate, this optimization does not affect the
logical definition.</p>"

  (defund charlist-has-some-up-alpha-p (x)
    (declare (xargs :guard (character-listp x)
                    :guard-hints(("Goal" :in-theory (enable up-alpha-p)))))
    (if (atom x)
        nil
      (or (mbe :logic (up-alpha-p (car x))
               :exec (let ((code (char-code (car x))))
                       (declare (type (unsigned-byte 8) code))
                       (and (<= (big-a) code)
                            (<= code (big-z)))))
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

  (defthm character-listp-downcase-charlist
    (character-listp (downcase-charlist x)))

  (defcong charlisteqv equal (downcase-charlist x) 1
    :hints(("Goal" :in-theory (enable charlisteqv))))

  (defthm downcase-charlist-aux-is-downcase-charlist
    (equal (downcase-charlist-aux x acc)
           (revappend (downcase-charlist x) acc)))

  (defthm downcase-charlist-does-nothing-unless-charlist-has-some-up-alpha-p
    (implies (and (not (charlist-has-some-up-alpha-p x))
                  (character-listp x))
             (equal (downcase-charlist x)
                    x)))

  (verify-guards downcase-charlist)

  (defthm len-of-downcase-charlist
    (equal (len (downcase-charlist x))
           (len x)))

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
standard-char-p) guards.  In contrast, <tt>upcase-string</tt> works on strings
with arbitrary characters.</p>

<p>We try to make this fast.  For better performance, we avoid consing and
simply return <tt>x</tt> unchanged when it has no characters that need to be
converted.  Of course, deciding whether some conversion is necessary will
marginally slow this function down when some conversion is necessary, but we
think the gain of not consing outweighs this.  At any rate, this optimization
does not affect the logical definition.</p>

<p>Despite trying to make this fast, the builtin <tt>string-upcase</tt> can
really outperform us since it doesn't have to build the intermediate list, etc.
It's really a shame that <tt>string-upcase</tt> has such a terrble guard.
Well, at least we're better when no work needs to be done:</p>

<code>
    (time (loop for i fixnum from 1 to 1000000 do
            (str::upcase-string \"Hello, World!\")))  ;; 1.2 seconds, 336 MB
    (time (loop for i fixnum from 1 to 1000000 do
            (string-upcase \"Hello, World!\")))       ;; .26 seconds, 64 MB

    (time (loop for i fixnum from 1 to 1000000 do
            (str::upcase-string \"HELLO, WORLD!\")))  ;; .15 seconds, 0 MB
    (time (loop for i fixnum from 1 to 1000000 do
            (string-upcase \"HELLO, WORLD!\")))       ;; .23 seconds, 64 MB
</code>"

  (defund string-has-some-down-alpha-p (x n xl)
    (declare (type string x)
             (type integer n)
             (type integer xl)
             (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (= xl (length x))
                                (<= n xl))
                    :measure (nfix (- (nfix xl) (nfix n)))
                    :guard-hints(("Goal" :in-theory (enable down-alpha-p)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (= n xl))
        nil
      (or (mbe :logic (down-alpha-p (char x n))
               :exec (let ((code (char-code (char x n))))
                       (declare (type (unsigned-byte 8) code))
                       (and (<= (little-a) code)
                            (<= code (little-z)))))
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
                    :measure (nfix (- (nfix xl) (nfix n)))
                    :guard-debug t
                    :guard-hints(("Goal" :in-theory (enable upcase-char)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (= n xl))
        acc
      (let* ((char   (char x n))
             (upchar (mbe :logic (upcase-char char)
                          :exec (let ((code (char-code char)))
                                  (declare (type (unsigned-byte 8) code))
                                  (if (and (<= (little-a) code)
                                           (<= code (little-z)))
                                      (code-char (the (unsigned-byte 8)
                                                   (- code (case-delta))))
                                    char)))))
        (upcase-string-aux x (+ 1 (lnfix n)) xl (cons upchar acc)))))

  (defund upcase-string (x)
    (declare (type string x)
             (xargs :verify-guards nil))
    (mbe :logic (coerce (upcase-charlist (coerce x 'list)) 'string)
         :exec
         (let ((xl (length x)))
           (if (not (string-has-some-down-alpha-p x 0 xl))
               ;; Avoid consing when no characters need to be converted.
               x
             (let* ((acc     (upcase-string-aux x 0 xl nil))
                    (rev-ans (coerce acc 'string)))
               ;; Generally best to reverse the string, rather than the chars.
               (reverse rev-ans))))))

  (defthm string-has-some-down-alpha-p-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (string-has-some-down-alpha-p x n xl)
                    (charlist-has-some-down-alpha-p (nthcdr n (coerce x 'list)))))
    :hints(("Goal" :in-theory (enable string-has-some-down-alpha-p
                                      charlist-has-some-down-alpha-p))))

  (defthm upcase-string-aux-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (upcase-string-aux x n xl acc)
                    (revappend (upcase-charlist (nthcdr n (coerce x 'list)))
                               acc)))
    :hints(("Goal" :in-theory (enable upcase-string-aux
                                      upcase-charlist))))

  (verify-guards upcase-string)

  (defthm len-of-upcase-string
    (equal (len (coerce (upcase-string x) 'list))
           (len (coerce x 'list)))
    :hints(("Goal" :in-theory (enable upcase-string))))

  (defthm length-of-upcase-string
    (equal (length (upcase-string x))
           (length (coerce x 'list))))

  (defthm string-upcase-is-upcase-string
    (equal (acl2::string-upcase x)
           (upcase-string x))
    :hints(("Goal" :in-theory (enable upcase-string)))))




(defsection downcase-string
  :parents (case-conversion acl2::string-downcase)
  :short "Convert a string to lower case."

  :long "<p>@(call downcase-string) converts a string to lower case,
effectively by transforming each of its characters with @(see
downcase-char).</p>

<p>ACL2 has a built-in alternative to this function, @(see
acl2::string-downcase), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, <tt>downcase-string</tt> works on
strings with arbitrary characters.</p>

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
                    :measure (nfix (- (nfix xl) (nfix n)))
                    :guard-hints(("Goal" :in-theory (enable up-alpha-p)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (= n xl))
        nil
      (or (mbe :logic (up-alpha-p (char x n))
               :exec (let ((code (char-code (char x n))))
                       (declare (type (unsigned-byte 8) code))
                       (and (<= (big-a) code)
                            (<= code (big-z)))))
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
                    :measure (nfix (- (nfix xl) (nfix n)))
                    :guard-debug t
                    :guard-hints(("Goal" :in-theory (enable downcase-char)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (= n xl))
        acc
      (let* ((char   (char x n))
             (downchar (mbe :logic (downcase-char char)
                            :exec (let ((code (char-code char)))
                                    (declare (type (unsigned-byte 8) code))
                                    (if (and (<= (big-a) code)
                                             (<= code (big-z)))
                                        (code-char (the (unsigned-byte 8)
                                                     (+ code (case-delta))))
                                      char)))))
        (downcase-string-aux x (+ 1 (lnfix n)) xl (cons downchar acc)))))

  (defund downcase-string (x)
    (declare (type string x)
             (xargs :verify-guards nil))
    (mbe :logic (coerce (downcase-charlist (coerce x 'list)) 'string)
         :exec
         (let ((xl (length x)))
           (if (not (string-has-some-up-alpha-p x 0 xl))
               ;; Avoid consing when no characters need to be converted.
               x
             (let* ((acc     (downcase-string-aux x 0 xl nil))
                    (rev-ans (coerce acc 'string)))
               ;; Generally best to reverse the string, rather than the chars.
               (reverse rev-ans))))))

  (defthm string-has-some-up-alpha-p-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (string-has-some-up-alpha-p x n xl)
                    (charlist-has-some-up-alpha-p (nthcdr n (coerce x 'list)))))
    :hints(("Goal" :in-theory (enable string-has-some-up-alpha-p
                                      charlist-has-some-up-alpha-p))))

  (defthm downcase-string-aux-redef
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (= xl (length x))
                  (<= n xl))
             (equal (downcase-string-aux x n xl acc)
                    (revappend (downcase-charlist (nthcdr n (coerce x 'list)))
                               acc)))
    :hints(("Goal" :in-theory (enable downcase-string-aux
                                      downcase-charlist))))

  (verify-guards downcase-string)

  (defthm len-of-downcase-string
    (equal (len (coerce (downcase-string x) 'list))
           (len (coerce x 'list)))
    :hints(("Goal" :in-theory (enable downcase-string))))

  (defthm length-of-downcase-string
    (equal (length (downcase-string x))
           (len (coerce x 'list))))

  (defthm string-downcase-is-downcase-string
    (equal (acl2::string-downcase x)
           (downcase-string x))
    :hints(("Goal" :in-theory (enable downcase-string)))))



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


