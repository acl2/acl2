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
(include-book "eqv")
(local (include-book "char-support"))
(local (include-book "unicode/rev" :dir :system))
(local (include-book "arithmetic"))

(defmacro little-a () (char-code #\a))
(defmacro little-z () (char-code #\z))
(defmacro big-a () (char-code #\A))
(defmacro big-z () (char-code #\Z))
(defmacro case-delta () (- (little-a) (big-a)))


(defund up-alpha-p (x)

  ":Doc-Section Str
  Determine if a character is an upper-case alphabetic character (A-Z).~/

  ACL2's built-in version of the function ~il[upper-case-p] is irritating to
  use because it has standard-char-p guards.  ~c[(str::up-alpha-p x)] is like
  it, but works on arbitrary characters.~/~/"

  (declare (type character x))
  (let ((code (char-code x)))
    (declare (type (unsigned-byte 8) code))
    (and (<= (big-a) code)
         (<= code (big-z)))))

(defund down-alpha-p (x)

  ":Doc-Section Str
  Determine if a character is a lower-case alphabetic character (a-z).~/

  ACL2's built-in version of the function ~il[lower-case-p] is irritating to
  use because it has standard-char-p guards.  ~c[(str::down-alpha-p x)] is like
  it, but works on arbitrary characters.~/~/"

  (declare (type character x))
  (let ((code (char-code x)))
    (declare (type (unsigned-byte 8) code))
    (and (<= (little-a) code)
         (<= code (little-z)))))



(defund upcase-char (x)

  ":Doc-Section Str
  Convert a character to upper-case.~/

  ACL2's built-in version of the function ~il[char-upcase] is irritating to use
  because it has standard-char-p guards.  ~c[(str::upcase-char x)] is like it,
  but works on arbitrary characters.~/~/"

  (declare (type character x))
  (let ((code (char-code x)))
    (declare (type (unsigned-byte 8) code))
    (if (and (<= (little-a) code)
             (<= code (little-z)))
        (code-char (the (unsigned-byte 8)
                     (- code (case-delta))))
      (mbe :logic (char-fix x)
           :exec x))))

(defthm upcase-char-does-nothing-unless-down-alpha-p
  (implies (and (not (down-alpha-p x))
                (characterp x))
           (equal (upcase-char x)
                  x))
  :hints(("Goal" :in-theory (enable upcase-char down-alpha-p))))

(defthm char-upcase-redef
  (equal (acl2::char-upcase x)
         (upcase-char x))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable upcase-char char-fix))))



(defund downcase-char (x)

  ":Doc-Section Str
  Convert a character to lower-case.~/

  ACL2's built-in version of the function ~il[char-downcase] is irritating to
  use because it has standard-char-p guards.  ~c[(str::downcase-char x)] is
  like it, but works on arbitrary characters.~/~/"

  (declare (type character x))
  (let ((code (char-code x)))
    (declare (type (unsigned-byte 8) code))
    (if (and (<= (big-a) code)
             (<= code (big-z)))
        (code-char (the (unsigned-byte 8)
                     (+ code (case-delta))))
      (mbe :logic (char-fix x)
           :exec x))))

(defthm downcase-char-does-nothing-unless-up-alpha-p
  (implies (and (not (up-alpha-p x))
                (characterp x))
           (equal (downcase-char x)
                  x))
  :hints(("Goal" :in-theory (enable downcase-char up-alpha-p))))

(defthm char-downcase-redef
  (equal (acl2::char-downcase x)
         (downcase-char x))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable downcase-char char-fix))))



; We write scanner functions to see if we actually have to do any work to
; upcase/downcase a string.  This helps avoid consing in the fairly common case
; that the string is already the case you want, but of course slows things down
; in the case where some conversion is indeed necessary.

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
        (string-has-some-up-alpha-p x
                                    (+ 1 (mbe :logic (nfix n) :exec n))
                                    xl))))

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
        (string-has-some-down-alpha-p x
                                      (+ 1 (mbe :logic (nfix n) :exec n))
                                      xl))))

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




(defund upcase-charlist-aux (x acc)
  (declare (Xargs :guard (and (character-listp x)
                              (character-listp acc))))
  (if (atom x)
      acc
    (upcase-charlist-aux (cdr x)
                         (cons (upcase-char (car x)) acc))))

(defund upcase-charlist (x)

  ":Doc-Section Str
  Convert every character in a list to upper case.~/~/~/"

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

(defthm character-listp-upcase-charlist
  (character-listp (upcase-charlist x))
  :hints(("Goal" :in-theory (enable upcase-charlist))))

(defthm upcase-charlist-aux-is-upcase-charlist
  (equal (upcase-charlist-aux x acc)
         (revappend (upcase-charlist x)
                    acc))
  :hints(("Goal" :in-theory (enable upcase-charlist-aux
                                    upcase-charlist))))

(defthm upcase-charlist-does-nothing-unless-charlist-has-some-down-alpha-p
  (implies (and (not (charlist-has-some-down-alpha-p x))
                (character-listp x))
           (equal (upcase-charlist x)
                  x))
  :hints(("Goal" :in-theory (enable charlist-has-some-down-alpha-p
                                    upcase-charlist))))

(verify-guards upcase-charlist
  :hints(("Goal" :in-theory (enable upcase-charlist
                                    charlist-has-some-down-alpha-p))))

(defthm string-upcase1-redef
  (equal (acl2::string-upcase1 x)
         (upcase-charlist x))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable upcase-charlist))))




(defund downcase-charlist-aux (x acc)
  (declare (xargs :guard (and (character-listp x)
                              (character-listp acc))))
  (if (atom x)
      acc
    (downcase-charlist-aux (cdr x)
                           (cons (downcase-char (car x)) acc))))

(defund downcase-charlist (x)

  ":Doc-Section Str
  Convert every character in a list to lower case.~/~/~/"

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

(defthm character-listp-downcase-charlist
  (character-listp (downcase-charlist x))
  :hints(("Goal" :in-theory (enable downcase-charlist))))

(defthm downcase-charlist-aux-is-downcase-charlist
  (equal (downcase-charlist-aux x acc)
         (revappend (downcase-charlist x) acc))
  :hints(("Goal" :in-theory (enable downcase-charlist-aux
                                    downcase-charlist))))

(defthm downcase-charlist-does-nothing-unless-charlist-has-some-up-alpha-p
  (implies (and (not (charlist-has-some-up-alpha-p x))
                (character-listp x))
           (equal (downcase-charlist x)
                  x))
  :hints(("Goal" :in-theory (enable downcase-charlist
                                    charlist-has-some-up-alpha-p))))

(verify-guards downcase-charlist
  :hints(("Goal" :in-theory (enable downcase-charlist
                                    charlist-has-some-up-alpha-p))))

(defthm string-downcase1-redef
  (equal (acl2::string-downcase1 x)
         (downcase-charlist x))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable acl2::string-downcase1
                                    downcase-charlist))))





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
      (upcase-string-aux x
                         (+ 1 (mbe :logic (nfix n) :exec n))
                         xl
                         (cons upchar acc)))))

(local (defthm append-singleton-crock
         (equal (append (append a (list x)) y)
                (append a (cons x y)))))

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




(defund upcase-string (x)

  ":Doc-Section Str
  Convert a string to upper case.~/

  ACL2's built-in version of the function ~il[string-upcase] is irritating to use
  because it has standard-char-p guards.  ~c[(str::upcase-string x)] is like it,
  but works on arbitrary strings.

  Despite trying to make this fast, the builtin string-upcase can really
  outperform us since it doesn't have to build the intermediate list, etc.
  It's really a shame that string-upcase has such a terrble guard.  Well, at
  least we're better when no work needs to be done. :)

    (time (loop for i fixnum from 1 to 1000000 do
            (str::upcase-string \"Hello, World!\")))  ;; 1.2 seconds, 336 MB
    (time (loop for i fixnum from 1 to 1000000 do
            (string-upcase \"Hello, World!\")))       ;; .26 seconds, 64 MB

    (time (loop for i fixnum from 1 to 1000000 do
            (str::upcase-string \"HELLO, WORLD!\")))  ;; .15 seconds, 0 MB
    (time (loop for i fixnum from 1 to 1000000 do
            (string-upcase \"HELLO, WORLD!\")))       ;; .23 seconds, 64 MB

   ~/~/"

  (declare (type string x))
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

(defthm string-upcase-redef
  (equal (acl2::string-upcase x)
         (upcase-string x))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable upcase-string))))







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
      (downcase-string-aux x
                           (+ 1 (mbe :logic (nfix n) :exec n))
                           xl
                           (cons downchar acc)))))

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

(defund downcase-string (x)

  ":Doc-Section Str
  Convert a string to lower case.~/

  ACL2's built-in version of the function ~il[string-downcase] is irritating to use
  because it has standard-char-p guards.  ~c[(str::downcase-string x)] is like it,
  but works on arbitrary characters.~/~/"

  (declare (type string x))
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

(defthm string-downcase-redef
  (equal (acl2::string-downcase x)
         (downcase-string x))
  :rule-classes :definition
  :hints(("Goal" :in-theory (enable downcase-string))))




(defun upcase-string-list-aux (x acc)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp acc))))
  (if (atom x)
      acc
    (upcase-string-list-aux (cdr x)
                            (cons (upcase-string (car x)) acc))))

(defun upcase-string-list (x)

  ":Doc-Section Str
  Convert every string in a list to upper-case.~/~/~/"

  (declare (xargs :guard (string-listp x)
                  :verify-guards nil))
  (mbe :logic
       (if (atom x)
           nil
         (cons (upcase-string (car x))
               (upcase-string-list (cdr x))))
       :exec
       (reverse (upcase-string-list-aux x nil))))

(defthm string-listp-upcase-string-list
  (string-listp (upcase-string-list x)))

(defthm upcase-string-list-aux-is-upcase-string-list
  (equal (upcase-string-list-aux x acc)
         (revappend (upcase-string-list x) acc)))

(verify-guards upcase-string-list)



(defun downcase-string-list-aux (x acc)
  (declare (xargs :guard (and (string-listp x)
                              (string-listp acc))))
  (if (atom x)
      acc
    (downcase-string-list-aux (cdr x)
                              (cons (downcase-string (car x)) acc))))

(defun downcase-string-list (x)

  ":Doc-Section Str
  Convert every string in a list to lower-case.~/~/~/"

  (declare (xargs :guard (string-listp x)
                  :verify-guards nil))
  (mbe :logic
       (if (atom x)
           nil
         (cons (downcase-string (car x))
               (downcase-string-list (cdr x))))
       :exec
       (reverse (downcase-string-list-aux x nil))))

(defthm string-listp-downcase-string-list
  (string-listp (downcase-string-list x)))

(defthm downcase-string-list-aux-is-downcase-string-list
  (equal (downcase-string-list-aux x acc)
         (revappend (downcase-string-list x) acc)))

(verify-guards downcase-string-list)


