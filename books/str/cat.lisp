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
(local (include-book "std/lists/take" :dir :system))


(defsection cat
  :parents (concatenation)
  :short "Concatenate strings."

  :long "<p>@('(str::cat x y z ...)') is like @('(concatenate 'string x y z
...)'), but is less to type.</p>

<p>Warning: concatenating strings is fundamentally slow.  This is because
Common Lisp strings are just arrays of characters, but there is not really any
mechanism that allows you to efficiently splice arrays together.  In other
words, any kind of string concatenation minimally requires creating a
completely new array and copying all of the input characters into it.</p>

<p>This makes it especially slow to repeatedly use @('cat') to build up a
string.  If that's your goal, you might instead consider using the approach
outlined in @(see revappend-chars).</p>

<p>In some Lisps, using @('(concatenate 'string ...)') to join strings can be
even worse than just the cost of creating and initializing a new array.  The
@(see concatenate) function is quite flexible and can handle many types of
input, and this flexibility can cause some overhead if the Lisp does not
optimize for the @(''string') case.</p>

<p>So, if you are willing to accept a trust tag, then you may <b>optionally</b>
load the book:</p>

@({
  (include-book \"str/fast-cat\" :dir :system)
})

<p>which may improve the performance of @('str::cat').  How does this work?
Basically @('str::cat') calls one of @('fast-string-append') or
@('fast-string-append-lst'), depending on how many arguments it is given.  By
default, these functions are aliases for ACL2's @(see string-append) and
@('string-append-lst') functions.  But if you load the @('fast-cat') book,
these functions will be redefined to use raw Lisp array operations, and the
result may be faster.</p>"

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

  :long "<p>@(call append-chars) takes the characters from the string @('x')
and appends them onto @('y').</p>

<p>Its logical definition is nothing more than @('(append (coerce x 'list)
y)').</p>

<p>In the execution, we traverse the string @('x') using @(see char) to avoid
the overhead of @(see coerce)-ing it into a character list before performing
the @(see append).  This reduces the overhead from @('2n') conses to @('n')
conses, where @('n') is the length of @('x').</p>"

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
                    (equal (append (take (- n 1) x) (cons (nth (- n 1) x) y))
                           (append (take n x) y)))
           :hints(("goal"
                   :in-theory (enable acl2::take-redefinition)
                   :induct (take n x)))))

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
                           (append (take (+ 1 n) (coerce x 'list)) y)))
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
@('x'), reverses them, and appends the result onto @('y').</p>

<p>Its logical definition is nothing more than @('(revappend (coerce x 'list)
y)').</p>

<p>In the execution, we traverse the string @('x') using @(see char) to avoid
the overhead of @(see coerce)-ing it into a character list before performing
the @(see revappend).  This reduces the overhead from @('2n') conses to @('n')
conses, where @('n') is the length of @('x').</p>

<p>This function may seem strange at first glance, but it provides a convenient
way to efficiently, incrementally build a string out of small parts.  For
instance, a sequence such as:</p>

@({
 (let* ((acc nil)
        (acc (str::revappend-chars \"Hello, \" acc))
        (acc (str::revappend-chars \"World!\" acc))
        (acc ...))
    (reverse (coerce acc 'string)))
})

<p>Is essentially the same as:</p>

@({
 (let* ((acc \"\")
        (acc (str::cat acc \"Hello, \"))
        (acc (str::cat acc \"World!\"))
        (acc ...))
   acc)
})

<p>But it is comparably much more efficient because it avoids the creation of
the intermediate strings.  See the performance discussion in @(see str::cat)
for more details.  Also see @(see rchars-to-string), which is a potentially
more efficient way to do the final @(see reverse)/@(see coerce) steps.</p>"

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
@('prefix') onto every member of @('x').</p>"

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




(defsection rchars-to-string
  :parents (concatenation)
  :short "Possibly optimized way to reverse a character list and coerce it to a
string."

  :long "<p>@(call rchars-to-string) is logically equal to</p>

@({
   (reverse (coerce rchars 'string))
})

<p>We leave it enabled and would not expect to ever reason about it.  This
operation is useful as the final step in a string-building strategy where
characters are accumulated onto a list in reverse order; see for instance @(see
revappend-chars).</p>

<p>When you just load books like @('str/top') or @('str/cat'), this logical
definition is exactly what gets executed.  This definition is not too bad, and
doing the @(see coerce) first means that the @(see reverse) is done on a
string (i.e., an array) instead of a list, which is generally efficient.</p>

<p>But if you are willing to accept a trust tag, then you may <b>optionally</b>
load the book:</p>

@({
  (include-book \"str/fast-cat\" :dir :system)
})

<p>This may improve the performance of @('rchars-to-string') by replacing the
@(see reverse) call with a call of @('nreverse').  We can \"obviously\" see
that this is safe since the string produced by the @('coerce') is not visible
to any other part of the program.</p>"

  (defun rchars-to-string (rchars)
    "May be redefined under-the-hood in str/fast-cat.lisp"
    ;; We don't inline this because you might want to develop books without
    ;; fast-cat (for fewer ttags), but then include fast-cat later for more
    ;; performance.
    (declare (xargs :guard (character-listp rchars)))
    (the string
      (reverse
       (the string (coerce (the list rchars) 'string))))))




(defsection join
  :parents (concatenation)
  :short "Concatenate a list of strings with some separator between."

  :long "<p>@(call join) joins together the list of strings @('x'), inserting
the string @('separator') between the members.  For example:</p>

@({
 (join '(\"a\" \"b\" \"c\") \".\") = \"a.b.c\"
 (join '(\"a\" \"b\" \"c\") \"->\") = \"a->b->c\"
})

<p>We always return a string; an empty @('x') results in the empty string, and
any empty strings within @('x') just implicitly don't contribute to the
result.</p>

<p>Any sort of string concatenation is slow, but @('join') is reasonably
efficient: it creates a single character list for the result (in reverse order)
without any use of @(see coerce), then uses @(see rchars-to-string) to build
and reverse the result string.</p>"

  (defund join-aux (x separator acc)
    (declare (xargs :guard (and (string-listp x)
                                (stringp separator))))
    (cond ((atom x)
           acc)
          ((atom (cdr x))
           (revappend-chars (car x) acc))
          (t
           (let* ((acc (revappend-chars (car x) acc))
                  (acc (revappend-chars separator acc)))
             (join-aux (cdr x) separator acc)))))

  (defund join (x separator)
    (declare (xargs :guard (and (string-listp x)
                                (stringp separator))
                    :verify-guards nil))
    (mbe :logic
         (cond ((atom x)
                "")
               ((atom (cdr x))
                (if (stringp (car x))
                    (car x)
                  ""))
               (t
                (cat (car x) separator (join (cdr x) separator))))
         :exec
         (rchars-to-string (join-aux x separator nil))))

  (local (in-theory (enable join join-aux)))

  (local (include-book "std/lists/rev" :dir :system))

  (local (defthm l1
           (equal (append (append x y) z)
                  (append x (append y z)))))

  (defthm join-aux-removal
    (implies (and (string-listp x)
                  (stringp separator))
             (equal (join-aux x separator acc)
                    (revappend (coerce (join x separator) 'list)
                               acc)))
    :hints(("Goal"
            :induct (join-aux x separator acc)
            :in-theory (enable revappend-chars))))

  (verify-guards join)

  (defthm stringp-of-join
    (stringp (join x separator))
    :rule-classes :type-prescription))

