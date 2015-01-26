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
(include-book "ieqv")
(include-book "std/util/bstar" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(include-book "std/basic/defs" :dir :system)
(local (include-book "arithmetic"))
(local (include-book "std/lists/equiv" :dir :system))

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


(define append-chars ((x :type string) y)
  :parents (concatenation)
  :short "Append a string's characters onto a list."

  :long "<p>@(call append-chars) takes the characters from the string @('x')
and appends them onto @('y').</p>

<p>Its logical definition is nothing more than @('(append (explode x) y)').</p>

<p>In the execution, we traverse the string @('x') using @(see char) to avoid
the overhead of @(see coerce)-ing it into a character list before performing
the @(see append).  This reduces the overhead from @('2n') conses to @('n')
conses, where @('n') is the length of @('x').</p>"
  :inline t
  (mbe :logic (append (explode x) y)
       :exec (b* (((the (integer 0 *) xl) (length x))
                  ((when (eql xl 0))
                   y)
                  ((the (integer 0 *) n) (- xl 1)))
               (append-chars-aux x n y)))

  :prepwork
  ((defund append-chars-aux (x n y)
     "Appends the characters from x[0:n] onto y"
     (declare (type string x)
              (type (integer 0 *) n)
              (xargs :guard (< n (length x))))
     (if (zp n)
         (cons (char x 0) y)
       (append-chars-aux x
                         (the (integer 0 *) (- n 1))
                         (cons (char x n) y))))

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
                    (append (take (+ 1 n) (explode x)) y)))
    :hints(("Goal"
            :in-theory (enable append-chars-aux)
            :induct (append-chars-aux x n y)))))
  ///
  (defthm character-listp-of-append-chars
    (equal (character-listp (append-chars x y))
           (character-listp y)))

  (defcong streqv equal (append-chars x y) 1)
  (defcong istreqv icharlisteqv (append-chars x y) 1)
  (defcong list-equiv list-equiv (append-chars x y) 2)
  (defcong charlisteqv charlisteqv (append-chars x y) 2)
  (defcong icharlisteqv icharlisteqv (append-chars x y) 2))



(define revappend-chars ((x :type string) y)
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
  :inline t

  (mbe :logic (revappend (explode x) y)
       :exec (revappend-chars-aux x 0 (length x) y))

  :prepwork
  ((defund revappend-chars-aux (x n xl y)
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

   (defthm revappend-chars-aux-correct
     (implies (and (stringp x)
                   (natp n)
                   (natp xl)
                   (<= n xl)
                   (equal xl (length x)))
              (equal (revappend-chars-aux x n xl y)
                     (revappend (nthcdr n (explode x)) y)))
     :hints(("Goal"
             :in-theory (e/d (revappend-chars-aux)
                             (acl2::revappend-removal))
             :induct (revappend-chars-aux x n xl y)))))

  ///
  (defthm character-listp-of-revappend-chars
    (equal (character-listp (revappend-chars x y))
           (character-listp y)))

  (defcong streqv equal (revappend-chars x y) 1)
  (defcong istreqv icharlisteqv (revappend-chars x y) 1)
  (defcong list-equiv list-equiv (revappend-chars x y) 2)
  (defcong charlisteqv charlisteqv (revappend-chars x y) 2)
  (defcong icharlisteqv icharlisteqv (revappend-chars x y) 2))


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


(define prefix-strings ((prefix stringp)
                        (x      string-listp))
  :parents (concatenation)
  :short "Concatenates a prefix onto every string in a list of strings."

  :long "<p>@(call prefix-strings) produces a new string list by concatenating
@('prefix') onto every member of @('x').</p>"
  (if (atom x)
      nil
    (cons (cat prefix (car x))
          (prefix-strings prefix (cdr x))))
  ///
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
           (len x)))

  (defcong streqv equal (prefix-strings prefix x) 1)

  (local (defthmd l0
           (equal (prefix-strings prefix (list-fix x))
                  (prefix-strings prefix x))))

  (defcong list-equiv equal (prefix-strings prefix x) 2
    :hints(("Goal" :in-theory (enable list-equiv)
            :use ((:instance l0 (x x))
                  (:instance l0 (x acl2::x-equiv)))))))


(define rchars-to-string ((rchars character-listp))
  :returns (str stringp :rule-classes :type-prescription)
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
  :enabled t

  ;; We don't inline this because you might want to develop books without
  ;; fast-cat (for fewer ttags), but then include fast-cat later for more
  ;; performance.
  (the string
    (reverse
     (the string (implode rchars)))))


(define join ((x string-listp)
              (separator :type string))
  :returns (joined stringp :rule-classes :type-prescription)
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

  :prepwork
  ((defund join-aux (x separator acc)
     (declare (xargs :guard (string-listp x))
              (type string separator))
     (cond ((atom x)
            acc)
           ((atom (cdr x))
            (revappend-chars (car x) acc))
           (t
            (let* ((acc (revappend-chars (car x) acc))
                   (acc (revappend-chars separator acc)))
              (join-aux (cdr x) separator acc))))))

  :inline t
  :verify-guards nil
  (mbe :logic
       (cond ((atom x)
              "")
             ((atom (cdr x))
              (str-fix (car x)))
             (t
              (cat (car x) separator (join (cdr x) separator))))
       :exec
       (rchars-to-string (join-aux x separator nil)))
  ///
  (local (in-theory (enable join-aux)))

  (defthm join-aux-removal
    (implies (and (string-listp x)
                  (stringp separator))
             (equal (join-aux x separator acc)
                    (revappend (coerce (join x separator) 'list)
                               acc)))
    :hints(("Goal"
            :induct (join-aux x separator acc)
            :in-theory (enable revappend-chars))))

  (verify-guards join$inline
    :hints(("Goal" :in-theory (enable join join-aux))))

  (local (defthmd l0
           (equal (join (list-fix x) separator)
                  (join x separator))))

  (defcong list-equiv equal (join x separator) 1
    :hints(("Goal" :in-theory (enable list-equiv)
            :use ((:instance l0 (x x))
                  (:instance l0 (x acl2::x-equiv))))))

  (defcong streqv equal (join x separator) 2)
  (defcong istreqv istreqv (join x separator) 2))


