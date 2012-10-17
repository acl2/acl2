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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")
(include-book "xdoc/top" :dir :system)
(include-book "misc/definline" :dir :system)
(local (include-book "arithmetic"))
(local (include-book "unicode/take" :dir :system))


(defsection cat
  :parents (concatenation)
  :short "Concatenate strings."

  :long "<p><tt>(str::cat x y z ...)</tt> is like <tt>(@(see concatenate)
'string x y z ...)</tt>, but is less to type.</p>

<p>Warning: concatenating strings is fundamentally slow.  This is because
Common Lisp strings are just arrays of characters, but there is not really any
mechanism that allows you to efficiently splice arrays together.  In other
words, any kind of string concatenation minimally requires creating a
completely new array and copying all of the input characters into it.</p>

<p>This makes it especially slow to repeatedly use <tt>cat</tt> to build up a
string.  If that's your goal, you might instead consider using the approach
outlined in @(see revappend-chars).</p>

<p>In some Lisps, using <tt>(concatenate 'string ...)</tt> to join strings can
be even worse than just the cost of creating and initializing a new array.  The
<tt>concatenate</tt> function is quite flexible and can handle many types of
input, and this flexibility can cause some overhead if the Lisp does not
optimize for the <tt>'string</tt> case.</p>

<p>So, if you are willing to accept a trust tag, then you may <b>optionally</b>
load the book:</p>

<code>
  (include-book \"str/fast-cat\" :dir :system)
</code>

<p>which may improve the performance of <tt>str::cat</tt>.  How does this work?
Basically <tt>str::cat</tt> calls one of <tt>fast-string-append</tt> or
<tt>fast-string-append-lst</tt>, depending on how many arguments it is given.
By default, these functions are aliases for ACL2's @(see string-append) and
<tt>string-append-lst</tt> functions.  But if you load the <tt>fast-cat</tt>
book, these functions will be redefined to use raw Lisp array operations, and
the result may be faster.</p>"

  (defun fast-string-append (str1 str2)
    "May be redefined under-the-hood in str/fast-cat.lisp"
    ;; We don't inline this because you might want to develop books without
    ;; fast-cat (for fewer ttags), but then include fast-cat later for more
    ;; performance.
    (declare (xargs :guard (and (stringp str1)
                                (stringp str2))))
    (string-append str1 str2))

  (defun fast-string-append-lst (x)
    "May be redefined under-the-hood in str/fast-cat.lisp"
    ;; We don't inline this because you might want to develop books without
    ;; fast-cat (for fewer ttags), but then include fast-cat later for more
    ;; performance.
    (declare (xargs :guard (string-listp x)))
    (string-append-lst x))

  (defmacro fast-concatenate (result-type &rest sequences)
    (declare (xargs :guard (member-equal result-type '('string 'list))))
    (cond ((equal result-type ''string)
           (cond ((and sequences
                       (cdr sequences)
                       (null (cddr sequences)))
                  (list 'fast-string-append
                        (car sequences)
                        (cadr sequences)))
                 (t
                  (list 'fast-string-append-lst
                        (cons 'list sequences)))))
          (t
           `(append (list . ,sequences)))))

  (defmacro cat (&rest args)
    `(fast-concatenate 'string . ,args)))


(defsection append-chars
  :parents (concatenation)
  :short "Append a string's characters onto a list."

  :long "<p>@(call append-chars) takes the characters from the string
<tt>x</tt> and appends them onto <tt>y</tt>.</p>

<p>Its logical definition is nothing more than <tt>(append (coerce x 'list)
y)</tt>.</p>

<p>In the execution, we traverse the string <tt>x</tt> using @(see char) to
avoid the overhead of @(see coerce)-ing it into a character list before
performing the @(see append).  This reduces the overhead from <tt>2n</tt>
conses to <tt>n</tt> conses, where <tt>n</tt> is the length of <tt>x</tt>.</p>"

  (defund append-chars-aux (x n y)
    "Appends the characters from x[0:n] onto y"
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (< n (length x))))
             (type string x)
             (type integer n))
    (if (zp n)
        (cons (char x 0) y)
      (append-chars-aux x (- n 1) (cons (char x n) y))))

  (local (defthm lemma
           (implies (and (not (zp n))
                         (<= n (len x)))
                    (equal (append (simpler-take (- n 1) x) (cons (nth (- n 1) x) y))
                           (append (simpler-take n x) y)))
           :hints(("goal"
                   :in-theory (enable simpler-take)
                   :induct (simpler-take n x)))))

  (defthm append-chars-aux-correct
    (implies (and (stringp x)
                  (natp n)
                  (< n (length x)))
             (equal (append-chars-aux x n y)
                    (append (take (+ 1 n) (coerce x 'list)) y)))
    :hints(("Goal"
            :in-theory (enable append-chars-aux)
            :induct (append-chars-aux x n y))))

  (local (in-theory (disable append-chars-aux-correct)))

  (local (defthm append-chars-aux-correct-better
           (implies (and (stringp x)
                         (natp n)
                         (< n (length x)))
                    (equal (append-chars-aux x n y)
                           (append (simpler-take (+ 1 n) (coerce x 'list)) y)))
           :hints(("Goal" :use ((:instance append-chars-aux-correct))))))

  (definlined append-chars (x y)
    (declare (xargs :guard (stringp x))
             (type string x))
    (mbe :logic (append (coerce x 'list) y)
         :exec (if (equal x "")
                   y
                 (append-chars-aux x (1- (length x)) y))))

  (local (in-theory (enable append-chars)))

  (defthm character-listp-of-append-chars
    (equal (character-listp (append-chars x y))
           (character-listp y))))


(defsection revappend-chars
  :parents (concatenation)
  :short "Append a string's characters onto a list, in reverse order."

  :long "<p>@(call revappend-chars) takes the characters from the string
<tt>x</tt>, reverses them, and appends the result onto <tt>y</tt>.</p>

<p>Its logical definition is nothing more than <tt>(revappend (coerce x 'list)
y)</tt>.</p>

<p>In the execution, we traverse the string <tt>x</tt> using @(see char) to
avoid the overhead of @(see coerce)-ing it into a character list before
performing the @(see revappend).  This reduces the overhead from <tt>2n</tt>
conses to <tt>n</tt> conses, where <tt>n</tt> is the length of <tt>x</tt>.</p>

<p>This function may seem strange at first glance, but it provides a convenient
way to efficiently, incrementally build a string out of small parts.  For
instance, a sequence such as:</p>

<code>
 (let* ((acc nil)
        (acc (str::revappend-chars \"Hello, \" acc))
        (acc (str::revappend-chars \"World!\" acc))
        (acc ...))
    (reverse (coerce acc 'string)))
</code>

<p>Is essentially the same as:</p>

<code>
 (let* ((acc \"\")
        (acc (str::cat acc \"Hello, \"))
        (acc (str::cat acc \"World!\"))
        (acc ...))
   acc)
</code>

<p>But it is comparably much more efficient because it avoids the creation of
the intermediate strings.  See the performance discussion in @(see str::cat)
for more details.</p>"

  (defund revappend-chars-aux (x n xl y)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (<= n xl)
                                (equal xl (length x)))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (int= n xl))
        y
      (revappend-chars-aux x (+ 1 (lnfix n)) xl (cons (char x n) y))))

  (defthm revappend-chars-aux-correct
    (implies (and (stringp x)
                  (natp n)
                  (natp xl)
                  (<= n xl)
                  (equal xl (length x)))
             (equal (revappend-chars-aux x n xl y)
                    (revappend (nthcdr n (coerce x 'list)) y)))
    :hints(("Goal"
            :in-theory (enable revappend-chars-aux)
            :induct (revappend-chars-aux x n xl y))))

  (definlined revappend-chars (x y)
    (declare (xargs :guard (stringp x))
             (type string x))
    (mbe :logic (revappend (coerce x 'list) y)
         :exec (revappend-chars-aux x 0 (length x) y)))

  (local (in-theory (enable revappend-chars)))

  (defthm character-listp-of-revappend-chars
    (equal (character-listp (revappend-chars x y))
           (character-listp y))))



#||

(include-book ;; newline to fool dependency scanner
 "cat")

;; Simple experiments on fv-1:

(defparameter *str* "Hello, world!")

;; 3.84 seconds, 2.08 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (revappend (coerce *str* 'list) nil))))

;; 2.88 seconds, 1.04 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (STR::revappend-chars *str* nil))))


;; 4.38 seconds, 2.08 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (append (coerce *str* 'list) nil))))

;; 3.00 seconds, 1.04 GB allocated
(progn
  (gc$)
  (time (loop for i fixnum from 1 to 5000000
              do
              (STR::append-chars *str* nil))))

||#



(defsection prefix-strings
  :parents (concatenation)
  :short "Concatenates a prefix onto every string in a list of strings."

  :long "<p>@(call prefix-strings) produces a new string list by concatenating
<tt>prefix</tt> onto every member of <tt>x</tt>.</p>"

  (defund prefix-strings (prefix x)
    (declare (xargs :guard (and (stringp prefix)
                                (string-listp x))))
    (if (atom x)
        nil
      (cons (cat prefix (car x))
            (prefix-strings prefix (cdr x)))))

  (local (in-theory (enable prefix-strings)))

  (defthm prefix-strings-when-atom
    (implies (atom x)
             (equal (prefix-strings prefix x)
                    nil)))

  (defthm prefix-strings-of-cons
    (equal (prefix-strings prefix (cons a x))
           (cons (cat prefix a)
                 (prefix-strings prefix x))))

  (defthm string-listp-of-prefix-strings
    (string-listp (prefix-strings prefix x)))

  (defthm len-of-prefix-strings
    (equal (len (prefix-strings prefix x))
           (len x))))
