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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")

(include-book "std/basic/defs" :dir :system)


(defsection cat
  :parents (concatenation concatenate)
  :short "Alternative to @(see concatenate) that has a shorter name and may in
some cases be more efficient."

  :long "<p>Concatenating strings is a fundamentally slow operation in Common
Lisp; see @(see concatenation).</p>

<p>In some Lisps, using @('(concatenate 'string ...)') can be even worse than
the necessary cost of creating and initializing a new array.  This is because
the @(see concatenate) function is quite flexible and can handle many types of
input (e.g., lists and vectors).  This flexibility can cause some overhead if
the Lisp does not optimize for the @(''string') case.</p>

<p>If you are willing to accept a trust tag, then you may <b>optionally</b>
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
    (declare (type string str1 str2))
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

(defsection rchars-to-string
  :parents (concatenation)
  :short "Possibly optimized way to reverse a character list and coerce it to a
string."

  :long "<p>@(call rchars-to-string) is logically equal to</p>

@({
   (reverse (implode rchars))
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
    (declare (xargs :guard (character-listp rchars)))
    (reverse
     (the string (coerce rchars 'string)))))



(defsection revappend-chars
  :parents (concatenation)
  :short "Append a string's characters onto a list, in reverse order."

  :long "<p>@(call revappend-chars) takes the characters from the string
@('x'), reverses them, and appends the result onto @('y').</p>

<p>Its logical definition is nothing more than @('(revappend (explode x) y)').</p>

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
    (reverse (implode acc)))
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
     (declare (type string x)
              (type (integer 0 *) n xl)
              (xargs :guard (and (<= n xl)
                                 (equal xl (length x)))
                     :measure (nfix (- (nfix xl) (nfix n)))))
     (if (mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (eql n xl))
         y
       (revappend-chars-aux x
                            (the (integer 0 *)
                              (+ 1 (the (integer 0 *) (lnfix n))))
                            xl
                            (cons (char x n) y))))

  (local (defthm nthcdr-of-nil
           (equal (nthcdr n nil) nil)))

  (local (defthm consp-nthcdr
           (iff (consp (nthcdr n x))
                (< (nfix n) (len x)))))

  (local (defthm cdr-of-nthcdr
           (equal (cdr (nthcdr n x))
                  (nthcdr n (cdr x)))))

  (local (defthm car-of-nthcdr
           (equal (car (nthcdr n x))
                  (nth n x))))

  (defthm revappend-chars-aux-correct
     (implies (and (stringp x)
                   (natp n)
                   (<= n xl)
                   (equal xl (length x)))
              (equal (revappend-chars-aux x n xl y)
                     (revappend (nthcdr n (coerce x 'list)) y)))
     :hints(("Goal"
             :in-theory (e/d (revappend-chars-aux))
             :induct (revappend-chars-aux x n xl y)
             :expand ((revappend (nthcdr n (coerce x 'list)) y)))))

  (defund-inline revappend-chars (x y)
    (declare (type string x))
    (mbe :logic (revappend (coerce x 'list) y)
         :exec (revappend-chars-aux x 0 (length x) y)))

  (defthm character-listp-of-revappend-chars
    (equal (character-listp (revappend-chars x y))
           (character-listp y))
    :hints(("Goal" :in-theory (enable revappend-chars)))))
