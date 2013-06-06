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


; char-case.lisp
;
; Original authors: Jared Davis <jared@centtech.com> and
;                   Sol Swords <sswords@centtech.com>

(in-package "STR")
(include-book "eqv")
(include-book "tools/bstar" :dir :system)
(local (include-book "arithmetic"))

(defmacro little-a ()   (char-code #\a))
(defmacro little-z ()   (char-code #\z))
(defmacro big-a ()      (char-code #\A))
(defmacro big-z ()      (char-code #\Z))
(defmacro case-delta () (- (little-a) (big-a)))



(defsection up-alpha-p
  :parents (case-conversion acl2::upper-case-p)
  :short "Determine if a character is an upper-case letter (A-Z)."

  :long "<p>@(call up-alpha-p) determines if @('x') is an upper-case alphabetic
character.</p>

<p>ACL2 has a built-in alternative to this function, @(see acl2::upper-case-p),
but it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, @('up-alpha-p') works on arbitrary characters.</p>"

  (definlined up-alpha-p (x)
    (declare (type character x))
    (b* (((the (unsigned-byte 8) code) (char-code x)))
      (and (<= (big-a) code)
           (<= code (big-z)))))

  (local (in-theory (enable up-alpha-p)))

  (defcong chareqv equal (up-alpha-p x) 1)

  ;; Rewrite ACL2's upper-case-p to up-alpha-p.  It seems simplest to just do
  ;; the proof by exhaustive testing.

  (local (defund exhaustive-test (n)
           (and (let ((x (code-char n)))
                  (equal (acl2::upper-case-p x)
                         (and (<= (big-a) (char-code x))
                              (<= (char-code x) (big-z)))))
                (or (zp n)
                    (exhaustive-test (- n 1))))))

  (local (defthm lemma1
           (implies (and (natp n)
                         (<= n 255))
                    (equal (char-code (code-char n))
                           n))))

  (local (defthm lemma2
           (implies (and (natp n)
                         (natp m)
                         (exhaustive-test n)
                         (= x (code-char m))
                         (<= m n)
                         (<= n 255))
                    (equal (acl2::upper-case-p x)
                           (and (<= (big-a) (char-code x))
                                (<= (char-code x) (big-z)))))
           :hints(("Goal"
                   :induct (exhaustive-test n)
                   :in-theory (enable exhaustive-test)))))

  (local (defthm lemma3
           (implies (characterp x)
                    (equal (acl2::upper-case-p x)
                           (and (<= (big-a) (char-code x))
                                (<= (char-code x) (big-z)))))
           :hints(("Goal"
                   :in-theory (disable lemma2)
                   :use ((:instance lemma2
                                    (n 255)
                                    (m (char-code x))))))))

  (local (defthm lemma4
           (implies (not (characterp x))
                    (not (acl2::upper-case-p x)))
           :hints(("Goal" :in-theory (enable acl2::upper-case-p)))))

  (local (defthm lemma5
           (equal (acl2::upper-case-p x)
                  (and (<= (big-a) (char-code x))
                       (<= (char-code x) (big-z))))
           :hints(("Goal" :cases ((characterp x))))))

  (defthm upper-case-p-is-up-alpha-p
    (equal (acl2::upper-case-p x)
           (up-alpha-p (double-rewrite x)))))



(defsection down-alpha-p
  :parents (case-conversion acl2::lower-case-p)
  :short "Determine if a character is a lower-case letter (a-z)."

  :long "<p>@(call down-alpha-p) determines if @('x') is an lower-case
alphabetic character.</p>

<p>ACL2 has a built-in alternative to this function, @(see acl2::lower-case-p),
but it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, @('down-alpha-p') works on arbitrary characters.</p>"

  (definlined down-alpha-p (x)
    (declare (type character x))
    (b* (((the (unsigned-byte 8) code) (char-code x)))
      (and (<= (little-a) code)
           (<= code (little-z)))))

  (local (in-theory (enable down-alpha-p)))

  (defcong chareqv equal (down-alpha-p x) 1)

  ;; Rewrite ACL2's lower-case-p to down-alpha-p.  It seems simplest to just do
  ;; the proof by exhaustive testing.

  (local (defund exhaustive-test (n)
           (and (let ((x (code-char n)))
                  (equal (acl2::lower-case-p x)
                         (and (<= (little-a) (char-code x))
                              (<= (char-code x) (little-z)))))
                (or (zp n)
                    (exhaustive-test (- n 1))))))

  (local (defthm lemma1
           (implies (and (natp n)
                         (<= n 255))
                    (equal (char-code (code-char n))
                           n))))

  (local (defthm lemma2
           (implies (and (natp n)
                         (natp m)
                         (exhaustive-test n)
                         (= x (code-char m))
                         (<= m n)
                         (<= n 255))
                    (equal (acl2::lower-case-p x)
                           (and (<= (little-a) (char-code x))
                                (<= (char-code x) (little-z)))))
           :hints(("Goal"
                   :induct (exhaustive-test n)
                   :in-theory (enable exhaustive-test)))))

  (local (defthm lemma3
           (implies (characterp x)
                    (equal (acl2::lower-case-p x)
                           (and (<= (little-a) (char-code x))
                                (<= (char-code x) (little-z)))))
           :hints(("Goal"
                   :in-theory (disable lemma2)
                   :use ((:instance lemma2
                                    (n 255)
                                    (m (char-code x))))))))

  (local (defthm lemma4
           (implies (not (characterp x))
                    (not (acl2::lower-case-p x)))
           :hints(("Goal" :in-theory (enable acl2::lower-case-p)))))

  (local (defthm lemma5
           (equal (acl2::lower-case-p x)
                  (and (<= (little-a) (char-code x))
                       (<= (char-code x) (little-z))))
           :hints(("Goal" :cases ((characterp x))))))

  (defthm lower-case-p-is-down-alpha-p
    (equal (acl2::lower-case-p x)
           (down-alpha-p (double-rewrite x)))))



(defsection upcase-char
  :parents (case-conversion acl2::char-upcase)
  :short "Convert a character to upper-case."

  :long "<p>@(call upcase-char) converts lower-case characters into their
upper-case equivalents, and returns other characters unchanged.</p>

<p>ACL2 has a built-in alternative to this function, @(see acl2::char-upcase),
but it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, @('upcase-char') works on arbitrary characters.</p>"

  (definlined upcase-char (x)
    (declare (type character x))
    (b* (((the (unsigned-byte 8) code) (char-code x)))
      (if (and (<= (little-a) code)
               (<= code (little-z)))
          (code-char (the (unsigned-byte 8) (- code (case-delta))))
        (mbe :logic (char-fix x) :exec x))))

  (local (in-theory (enable upcase-char)))

  (defcong chareqv equal (upcase-char x) 1)

  (defthm upcase-char-does-nothing-unless-down-alpha-p
    (implies (not (down-alpha-p x))
             (equal (upcase-char x)
                    (char-fix x)))
    :hints(("Goal" :in-theory (enable down-alpha-p))))

  ;; Rewrite ACL2's char-upcase to upcase-char.  It seems simplest to just do
  ;; the proof by exhaustive testing.

  (local (defund exhaustive-test (n)
           (and (let ((x (code-char n)))
                  (equal (acl2::char-upcase x)
                         (if (and (<= (little-a) (char-code x))
                                  (<= (char-code x) (little-z)))
                             (code-char (- (char-code x) (case-delta)))
                           x)))
                (or (zp n)
                    (exhaustive-test (- n 1))))))

  (local (defthm lemma1
           (implies (and (natp n)
                         (<= n 255))
                    (equal (char-code (code-char n))
                           n))))

  (local (defthm lemma2
           (implies (and (natp n)
                         (natp m)
                         (exhaustive-test n)
                         (= x (code-char m))
                         (<= m n)
                         (<= n 255))
                    (equal (acl2::char-upcase x)
                           (if (and (<= (little-a) (char-code x))
                                    (<= (char-code x) (little-z)))
                               (code-char (- (char-code x) (case-delta)))
                             x)))
           :hints(("Goal"
                   :induct (exhaustive-test n)
                   :in-theory (enable exhaustive-test)))))

  (local (defthm lemma3
           (implies (characterp x)
                    (equal (acl2::char-upcase x)
                           (if (and (<= (little-a) (char-code x))
                                    (<= (char-code x) (little-z)))
                               (code-char (- (char-code x) (case-delta)))
                             x)))
           :hints(("Goal"
                   :in-theory (disable lemma2)
                   :use ((:instance lemma2
                                    (n 255)
                                    (m (char-code x))))))))

  (local (defthm lemma4
           (implies (not (characterp x))
                    (equal (acl2::char-upcase x)
                           (code-char 0)))
           :hints(("Goal" :in-theory (enable acl2::char-upcase)))))

  (local (defthm lemma5
           (equal (acl2::char-upcase x)
                  (if (characterp x)
                      (if (and (<= (little-a) (char-code x))
                               (<= (char-code x) (little-z)))
                          (code-char (- (char-code x) (case-delta)))
                        x)
                    (code-char 0)))))

  (defthm char-upcase-is-upcase-char
    (equal (acl2::char-upcase x)
           (upcase-char (double-rewrite x)))))



(defsection downcase-char
  :parents (case-conversion acl2::char-downcase)
  :short "Convert a character to lower-case."

  :long "<p>@(call downcase-char) converts upper-case characters into their
lower-case equivalents, and returns other characters unchanged.</p>

<p>ACL2 has a built-in alternative to this function, @(see
acl2::char-downcase), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('downcase-char') works on arbitrary
characters.</p>"

  (definlined downcase-char (x)
    (declare (type character x))
    (b* (((the (unsigned-byte 8) code) (char-code x)))
      (if (and (<= (big-a) code)
               (<= code (big-z)))
          (code-char (the (unsigned-byte 8) (+ code (case-delta))))
        (mbe :logic (char-fix x) :exec x))))

  (local (in-theory (enable downcase-char)))

  (defcong chareqv equal (downcase-char x) 1)

  (defthm downcase-char-does-nothing-unless-up-alpha-p
    (implies (not (up-alpha-p x))
             (equal (downcase-char x)
                    (char-fix x)))
    :hints(("Goal" :in-theory (enable up-alpha-p))))

  ;; Rewrite ACL2's char-downcase to downcase-char.  It seems simplest to just do
  ;; the proof by exhaustive testing.

  (local (defund exhaustive-test (n)
           (and (let ((x (code-char n)))
                  (equal (acl2::char-downcase x)
                         (if (and (<= (big-a) (char-code x))
                                  (<= (char-code x) (big-z)))
                             (code-char (+ (char-code x) (case-delta)))
                           x)))
                (or (zp n)
                    (exhaustive-test (- n 1))))))

  (local (defthm lemma1
           (implies (and (natp n)
                         (<= n 255))
                    (equal (char-code (code-char n))
                           n))))

  (local (defthm lemma2
           (implies (and (natp n)
                         (natp m)
                         (exhaustive-test n)
                         (= x (code-char m))
                         (<= m n)
                         (<= n 255))
                    (equal (acl2::char-downcase x)
                           (if (and (<= (big-a) (char-code x))
                                    (<= (char-code x) (big-z)))
                               (code-char (+ (char-code x) (case-delta)))
                             x)))
           :hints(("Goal"
                   :induct (exhaustive-test n)
                   :in-theory (enable exhaustive-test)))))

  (local (defthm lemma3
           (implies (characterp x)
                    (equal (acl2::char-downcase x)
                           (if (and (<= (big-a) (char-code x))
                                    (<= (char-code x) (big-z)))
                               (code-char (+ (char-code x) (case-delta)))
                             x)))
           :hints(("Goal"
                   :in-theory (disable lemma2)
                   :use ((:instance lemma2
                                    (n 255)
                                    (m (char-code x))))))))

  (local (defthm lemma4
           (implies (not (characterp x))
                    (equal (acl2::char-downcase x)
                           (code-char 0)))
           :hints(("Goal" :in-theory (enable acl2::char-downcase)))))

  (local (defthm lemma5
           (equal (acl2::char-downcase x)
                  (if (characterp x)
                      (if (and (<= (big-a) (char-code x))
                               (<= (char-code x) (big-z)))
                          (code-char (+ (char-code x) (case-delta)))
                        x)
                    (code-char 0)))))

  (defthm char-downcase-is-downcase-char
    (equal (acl2::char-downcase x)
           (downcase-char x))))



(defsection upcase-char-str
  :parents (case-conversion)
  :short "Convert a character into an upper-case one-element string."
  :long "<p>@(call upcase-char-str) is logically equal to:</p>

@({
 (coerce (list (upcase-char c)) 'string)
})

<p>But we store these strings in a table so that they don't have to be
recomputed.  This is mainly useful to reduce the creation of temporary strings
during @(see upcase-first).</p>"

  (defun make-upcase-first-strtbl (n)
    (declare (xargs :guard (and (natp n)
                                (<= n 255))
                    :ruler-extenders :all))
    (cons (cons n (coerce (list (upcase-char (code-char n))) 'string))
          (if (zp n)
              nil
            (make-upcase-first-strtbl (- n 1)))))

  (defconst *upcase-first-strtbl*
    (compress1 '*upcase-first-strtbl*
               (cons '(:header :dimensions (256)
                               :maximum-length 257)
                     (make-upcase-first-strtbl 255))))

  (local (in-theory (disable aref1)))

  (local (defun test (n)
           (declare (xargs :ruler-extenders :all))
           (and (equal (aref1 '*upcase-first-strtbl* *upcase-first-strtbl* n)
                       (coerce (list (upcase-char (code-char n))) 'string))
                (if (zp n)
                    t
                  (test (- n 1))))))

  (local (defthm l0
           (implies (and (natp i)
                         (natp n)
                         (<= i n)
                         (<= n 255)
                         (test n))
                    (equal (aref1 '*upcase-first-strtbl* *upcase-first-strtbl* i)
                           (coerce (list (upcase-char (code-char i))) 'string)))
           :hints(("Goal" :induct (test n)))))

  (local (defthm l1
           (implies (and (natp i)
                         (<= i 255))
                    (equal (aref1 '*upcase-first-strtbl* *upcase-first-strtbl* i)
                           (coerce (list (upcase-char (code-char i))) 'string)))
           :hints(("Goal" :use ((:instance l0 (n 255)))))))

  (definline upcase-char-str (c)
    (declare (type character c))
    (mbe :logic (coerce (list (upcase-char c)) 'string)
         :exec (aref1 '*upcase-first-strtbl* *upcase-first-strtbl* (char-code c)))))



(defsection downcase-char-str
  :parents (case-conversion)
  :short "Convert a character into a lower-case one-element string."
  :long "<p>@(call downcase-char-str) is logically equal to:</p>

@({
 (coerce (list (downcase-char c)) 'string)
})

<p>But we store these strings in a table so that they don't have to be
recomputed.  This is mainly useful to reduce the creation of temporary strings
during @(see downcase-first).</p>"

  (defun make-downcase-first-strtbl (n)
     (declare (xargs :guard (and (natp n)
                                 (<= n 255))
                     :ruler-extenders :all))
    (cons (cons n (coerce (list (downcase-char (code-char n))) 'string))
          (if (zp n)
              nil
            (make-downcase-first-strtbl (- n 1)))))

  (defconst *downcase-first-strtbl*
    (compress1 '*downcase-first-strtbl*
               (cons '(:header :dimensions (256)
                               :maximum-length 257)
                     (make-downcase-first-strtbl 255))))

  (local (in-theory (disable aref1)))

  (local (defun test (n)
           (declare (xargs :ruler-extenders :all))
           (and (equal (aref1 '*downcase-first-strtbl* *downcase-first-strtbl* n)
                       (coerce (list (downcase-char (code-char n))) 'string))
                (if (zp n)
                    t
                  (test (- n 1))))))

  (local (defthm l0
           (implies (and (natp i)
                         (natp n)
                         (<= i n)
                         (<= n 255)
                         (test n))
                    (equal (aref1 '*downcase-first-strtbl* *downcase-first-strtbl* i)
                           (coerce (list (downcase-char (code-char i))) 'string)))
           :hints(("Goal" :induct (test n)))))

  (local (defthm l1
           (implies (and (natp i)
                         (<= i 255))
                    (equal (aref1 '*downcase-first-strtbl* *downcase-first-strtbl* i)
                           (coerce (list (downcase-char (code-char i))) 'string)))
           :hints(("Goal" :use ((:instance l0 (n 255)))))))

  (definline downcase-char-str (c)
    (declare (type character c))
    (mbe :logic (coerce (list (downcase-char c)) 'string)
         :exec (aref1 '*downcase-first-strtbl* *downcase-first-strtbl* (char-code c)))))

