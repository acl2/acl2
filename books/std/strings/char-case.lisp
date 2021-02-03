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


; char-case.lisp
;
; Original authors: Jared Davis <jared@centtech.com> and
;                   Sol Swords <sswords@centtech.com>

(in-package "STR")
(include-book "eqv")
(local (include-book "arithmetic"))

(defmacro little-a ()   (char-code #\a))
(defmacro little-z ()   (char-code #\z))
(defmacro big-a ()      (char-code #\A))
(defmacro big-z ()      (char-code #\Z))
(defmacro case-delta () (- (little-a) (big-a)))



(define up-alpha-p ((x :type character))
  :returns bool
  :parents (cases acl2::upper-case-p)
  :short "Determine if a character is an upper-case letter (A-Z)."

  :long "<p>ACL2 has a built-in alternative to this function, @(see
acl2::upper-case-p), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('up-alpha-p') works on arbitrary
characters.</p>"
  :inline t
  (b* (((the (unsigned-byte 8) code) (char-code x)))
    (and (<= (big-a) code)
         (<= code (big-z))))
  ///
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
           (up-alpha-p (double-rewrite x))))

  ;; No longer necessary since we'll rewrite upper-case-p away
  (in-theory (disable acl2::upper-case-p-char-upcase)))



(define down-alpha-p ((x :type character))
  :returns bool
  :parents (cases acl2::lower-case-p)
  :short "Determine if a character is a lower-case letter (a-z)."

  :long "<p>ACL2 has a built-in alternative to this function, @(see
acl2::lower-case-p), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('down-alpha-p') works on arbitrary
characters.</p>"

  :inline t
  (b* (((the (unsigned-byte 8) code) (char-code x)))
    (and (<= (little-a) code)
         (<= code (little-z))))
  ///
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
           (down-alpha-p (double-rewrite x))))

  ;; No longer necessary since we'll rewrite lower-case-p away
  (in-theory (disable acl2::lower-case-p-char-downcase))

  (defthm down-alpha-p-when-up-alpha-p
    (implies (up-alpha-p x)
             (not (down-alpha-p x)))
    :hints(("Goal" :in-theory (enable up-alpha-p
                                      down-alpha-p)))))


(define upcase-char ((x :type character))
  :returns (char characterp :rule-classes :type-prescription)
  :parents (cases acl2::char-upcase)
  :short "Convert a character to upper-case."

  :long "<p>@(call upcase-char) converts lower-case characters into their
upper-case equivalents, and returns other characters unchanged.</p>

<p>ACL2 has a built-in alternative to this function, @(see acl2::char-upcase),
but it is irritating to use because it has @(see standard-char-p) guards.  In
contrast, @('upcase-char') works on arbitrary characters.</p>"
  :inline t
  (b* (((the (unsigned-byte 8) code) (char-code x)))
    (if (and (<= (little-a) code)
             (<= code (little-z)))
        (code-char (the (unsigned-byte 8) (- code (case-delta))))
      (mbe :logic (char-fix x) :exec x)))
  ///
  (defcong chareqv equal (upcase-char x) 1)

  (defthm upcase-char-does-nothing-unless-down-alpha-p
    (implies (not (down-alpha-p x))
             (equal (upcase-char x)
                    (char-fix x)))
    :hints(("Goal" :in-theory (enable down-alpha-p))))

  (defthm upcase-char-of-upcase-char
    (equal (upcase-char (upcase-char x))
           (upcase-char x)))

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
           (upcase-char (double-rewrite x))))

  ;; Mihir M. mod: added a lemma.
  (defthm
    not-down-alpha-p-of-upcase-char
    (not (down-alpha-p (upcase-char x)))
    :hints
    (("goal"
      :in-theory (enable down-alpha-p)))))


(define downcase-char ((x :type character))
  :returns (char characterp :rule-classes :type-prescription)
  :parents (cases acl2::char-downcase)
  :short "Convert a character to lower-case."

  :long "<p>@(call downcase-char) converts upper-case characters into their
lower-case equivalents, and returns other characters unchanged.</p>

<p>ACL2 has a built-in alternative to this function, @(see
acl2::char-downcase), but it is irritating to use because it has @(see
standard-char-p) guards.  In contrast, @('downcase-char') works on arbitrary
characters.</p>"
  :inline t
  (b* (((the (unsigned-byte 8) code) (char-code x)))
    (if (and (<= (big-a) code)
             (<= code (big-z)))
        (code-char (the (unsigned-byte 8) (+ code (case-delta))))
      (mbe :logic (char-fix x) :exec x)))
  ///
  (defcong chareqv equal (downcase-char x) 1)

  (defthm downcase-char-does-nothing-unless-up-alpha-p
    (implies (not (up-alpha-p x))
             (equal (downcase-char x)
                    (char-fix x)))
    :hints(("Goal" :in-theory (enable up-alpha-p))))

  (defthm downcase-char-of-downcase-char
    (equal (downcase-char (downcase-char x))
           (downcase-char x)))

  (defthm downcase-char-of-upcase-char
    (equal (downcase-char (upcase-char x))
           (downcase-char x))
    :hints(("Goal" :in-theory (enable upcase-char
                                      char-fix))))

  (defthm upcase-char-of-downcase-char
    (equal (upcase-char (downcase-char x))
           (upcase-char x))
    :hints(("Goal" :in-theory (enable upcase-char
                                      char-fix))))

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
           (downcase-char (double-rewrite x)))))



(define upcase-char-str ((c characterp))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (cases)
  :short "Convert a character into an upper-case one-element string."
  :long "<p>@(call upcase-char-str) is logically equal to:</p>

@({
 (implode (list (upcase-char c)))
})

<p>But we store these strings in a table so that they don't have to be
recomputed.  This is mainly useful to reduce the creation of temporary strings
during @(see upcase-first).</p>"
  :enabled t
  :inline t

  (mbe :logic (implode (list (upcase-char c)))
       :exec (aref1 '*upcase-first-strtbl* *upcase-first-strtbl*
                    (char-code c)))

  :prepwork
  ((defun make-upcase-first-strtbl (n)
     (declare (xargs :guard (and (natp n)
                                 (<= n 255))
                     :ruler-extenders :all))
     (cons (cons n (implode (list (upcase-char (code-char n)))))
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
                        (implode (list (upcase-char (code-char n)))))
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
                            (implode (list (upcase-char (code-char i))))))
            :hints(("Goal" :induct (test n)))))

   (local (defthm l1
            (implies (and (natp i)
                          (<= i 255))
                     (equal (aref1 '*upcase-first-strtbl* *upcase-first-strtbl* i)
                            (implode (list (upcase-char (code-char i))))))
            :hints(("Goal" :use ((:instance l0 (n 255)))))))))



(define downcase-char-str ((c :type character))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (cases)
  :short "Convert a character into a lower-case one-element string."
  :long "<p>@(call downcase-char-str) is logically equal to:</p>

@({
 (implode (downcase-char c))
})

<p>But we store these strings in a table so that they don't have to be
recomputed.  This is mainly useful to reduce the creation of temporary strings
during @(see downcase-first).</p>"
  :enabled t
  :inline t

  (mbe :logic (implode (list (downcase-char c)))
       :exec (aref1 '*downcase-first-strtbl* *downcase-first-strtbl*
                    (char-code c)))

  :prepwork
  ((defun make-downcase-first-strtbl (n)
     (declare (xargs :guard (and (natp n)
                                 (<= n 255))
                     :ruler-extenders :all))
     (cons (cons n (implode (list (downcase-char (code-char n)))))
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
                        (implode (list (downcase-char (code-char n)))))
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
                            (implode (list (downcase-char (code-char i))))))
            :hints(("Goal" :induct (test n)))))

   (local (defthm l1
            (implies (and (natp i)
                          (<= i 255))
                     (equal (aref1 '*downcase-first-strtbl* *downcase-first-strtbl* i)
                            (implode (list (downcase-char (code-char i))))))
            :hints(("Goal" :use ((:instance l0 (n 255)))))))))
