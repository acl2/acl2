; Std/basic - Basic definitions
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(local (xdoc::set-default-parents std/basic))

(defsection bfix
  :parents (std/basic logops-definitions bitp)
  :short "Bit fix.  @('(bfix b)') is a fixing function for @(see bitp)s.  It
 coerces any object to a bit (0 or 1) by coercing non-1 objects to 0."
  :long "<p>See also @(see lbfix).</p>"

  (defun-inline bfix (b)
    (declare (xargs :guard t))
    (if (eql b 1)
        1
      0))

  (defthm bitp-bfix
    (bitp (bfix b)))

  (defthm bfix-bitp
    (implies (bitp b)
             (equal (bfix b) b))))

(defsection lbfix
  :parents (std/basic logops-definitions bitp)
  :short "Logical bit fix.  @('(lbfix b)') is logically identical to @('(bfix
b)') but executes as the identity.  It requires @('(bitp b)') as a guard, and
expands to just @('b')."
  :long "@(def lbfix)"

  (defmacro lbfix (x)
    `(mbe :logic (bfix ,x) :exec ,x)))

(defsection maybe-bitp
  :parents (std/basic bitp)
  :short "Recognizer for bits and @('nil')."
  :long "<p>This is like an <a
href='https://en.wikipedia.org/wiki/Option_type'>option type</a>; when @('x')
satisfies @('maybe-bitp'), then either it is a @(see bitp) or nothing.</p>"

  (defund-inline maybe-bitp (x)
    (declare (xargs :guard t))
    (or (not x)
        (bitp x)))

  (local (in-theory (enable maybe-bitp)))

  (defthm maybe-bitp-compound-recognizer
    (implies (maybe-bitp x)
             (or (not x)
                 (bitp x)))
    :rule-classes :compound-recognizer))

(defsection lnfix
  :short "@(call lnfix) is logically identical to @('(nfix x)'), but its guard
requires that @('x') is a natural number and, in the execution, it is just a
no-op that returns @('x')."

  :long "<p>@(call lnfix) is an inlined, enabled function that just expands into</p>

@({
     (mbe :logic (nfix x) :exec x)
})

<p>Why would you want this?  When you defining a function whose @(see guard)
assumes @('(natp n)'), it is often a good idea to write the function so that it
logically treats non-naturals as 0.  You might generally accomplish this by
rewriting, e.g.,:</p>

@({
    (defun my-function (n ...)
      (declare (xargs :guard (natp n)))
      <body>)

    --->

    (defun my-function (n ...)
      (declare (xargs :guard (natp n)))
      (let ((n (nfix n)))
        <body>))
})

<p>This leads to a nice @(see nat-equiv) @(see congruence) rule.  But since
@(see nfix) has to check whether its argument is a natural number, and that
has some performance cost.</p>

<p>By using @(see lnfix) in place of @('nfix') here, you can get the same
logical definition without this overhead.</p>"

  (defun-inline lnfix (x)
    (declare (xargs :guard (natp x)))
    (mbe :logic (nfix x) :exec x)))


(defsection lifix
  :short "@(call lifix) is logically identical to @('(ifix x)'), but its guard
requires that @('x') is an integer and, in the execution, it is just a no-op
that returns @('x')."

  :long "<p>@(call lifix) is an inlined, enabled function that just expands into</p>

@({
     (mbe :logic (ifix x) :exec x)
})

<p>To understand why you might want this, see the analogous discussion about
@(see lnfix).</p>"

  (defun-inline lifix (x)
    (declare (xargs :guard (integerp x)))
    (mbe :logic (ifix x) :exec x)))


(defsection true
  :short "A function that always just returns the constant @('t')."
  :long "<p>This is occasionally useful for @(see defattach), etc.</p>"

  (defun true ()
    (declare (xargs :guard t))
    t))


(defsection false
  :short "A function that just returns the constant @('nil')."
  :long "<p>This is occasionally useful for @(see defattach), etc.</p>"

  (defun false ()
    (declare (xargs :guard t))
    nil))


(defsection maybe-natp
  :short "Recognizer for naturals and @('nil')."
  :long "<p>This is like an <a
href='https://en.wikipedia.org/wiki/Option_type'>option type</a>; when @('x')
satisfies @('maybe-natp'), then either it is a natural number or nothing.</p>"

  (defund-inline maybe-natp (x)
    (declare (xargs :guard t))
    (or (not x)
        (natp x)))

  (local (in-theory (enable maybe-natp)))

  (defthm maybe-natp-compound-recognizer
    (equal (maybe-natp x)
           (or (not x)
               (and (integerp x)
                    (<= 0 x))))
    :rule-classes :compound-recognizer))


(defsection maybe-integerp
  :short "Recognizer for integers and @('nil')."
  :long "<p>This is like an <a
href='https://en.wikipedia.org/wiki/Option_type'>option type</a>; when @('x')
satisfies @('maybe-integerp'), then either it is a integer or nothing.</p>"

  (defund-inline maybe-integerp (x)
    (declare (xargs :guard t))
    (or (not x)
        (integerp x)))

  (local (in-theory (enable maybe-integerp)))

  (defthm maybe-integerp-compound-recognizer
    (equal (maybe-integerp x)
           (or (integerp x)
               (not x)))
    :rule-classes :compound-recognizer))


(defsection maybe-posp
  :short "Recognizer for positive naturals and @('nil')."
  :long "<p>This is like an <a
href='https://en.wikipedia.org/wiki/Option_type'>option type</a>; when @('x')
satisfies @('maybe-posp'), then either it is a positive, natural number or
nothing.</p>"

  (defund-inline maybe-posp (x)
    (declare (xargs :guard t))
    (or (not x)
        (posp x)))

  (local (in-theory (enable maybe-posp)))

  (defthm maybe-posp-compound-recognizer
    (equal (maybe-posp x)
           (or (and (integerp x)
                    (< 0 x))
               (not x)))
    :rule-classes :compound-recognizer))


(defsection maybe-stringp
  :short "Recognizer for strings and @('nil')."
  :long "<p>This is like an <a
href='https://en.wikipedia.org/wiki/Option_type'>option type</a>; when @('x')
satisfies @('maybe-stringp'), then either it is a string or nothing.</p>"

  (defund-inline maybe-stringp (x)
    (declare (xargs :guard t))
    (or (not x)
        (stringp x)))

  (local (in-theory (enable maybe-stringp)))

  (defthm maybe-stringp-compound-recognizer
    (equal (maybe-stringp x)
           (or (not x)
               (stringp x)))
    :rule-classes :compound-recognizer))


(defsection char-fix
  :parents (std/basic str::equivalences)
  :short "Coerce to a character."

  :long "<p>@(call char-fix) is the identity on @(see acl2::characters), and
returns the NUL character (i.e., the character whose code is 0) for any
non-character.</p>

<p>This is similar to other fixing functions like @(see fix) and @(see nfix).
See also @(see chareqv).</p>"

  (defund-inline char-fix (x)
    (declare (xargs :guard t))
    (if (characterp x)
        x
      (code-char 0)))

  (local (in-theory (enable char-fix)))

  (defthm characterp-of-char-fix
    (characterp (char-fix x))
    :rule-classes :type-prescription)

  (defthm char-fix-default
    (implies (not (characterp x))
             (equal (char-fix x)
                    (code-char 0))))

  (defthm char-fix-when-characterp
    (implies (characterp x)
             (equal (char-fix x)
                    x))))


(defsection chareqv
  :parents (std/basic str::equivalences)
  :short "Case-sensitive character equivalence test."

  :long "<p>@(call chareqv) determines if @('x') and @('y') are equivalent when
interpreted as characters.  That is, non-characters are first coerced to be the
NUL character (via @(see char-fix)), then we see if these coerced arguments are
equal.</p>

<p>See also @(see str::ichareqv) for a case-insensitive alternative.</p>"

  (defund-inline chareqv (x y)
    (declare (xargs :guard t))
    (eql (char-fix x) (char-fix y)))

  (local (in-theory (enable char-fix char< chareqv)))

  (defequiv chareqv)

  (defthm chareqv-of-char-fix
    (chareqv (char-fix x) x))

  (defcong chareqv equal (char-fix x) 1)
  (defcong chareqv equal (char-code x) 1)
  (defcong chareqv equal (char< x y) 1)
  (defcong chareqv equal (char< x y) 2))


(defsection str-fix
  :parents (std/basic str::equivalences)
  :short "Coerce to a string."
  :long "<p>@(call str-fix) is the identity on @(see acl2::stringp)s, or
returns the empty string, @('\"\"'), for any non-string.</p>

<p>This is similar to other fixing functions like @(see fix) and @(see nfix).
See also @(see streqv).</p>"

  (defund-inline str-fix (x)
    (declare (xargs :guard t))
    (if (stringp x)
        x
      ""))

  (local (in-theory (enable str-fix)))

  (defthm stringp-of-str-fix
    (stringp (str-fix x))
    :rule-classes :type-prescription)

  (defthm str-fix-default
    (implies (not (stringp x))
             (equal (str-fix x)
                    "")))

  (defthm str-fix-when-stringp
    (implies (stringp x)
             (equal (str-fix x)
                    x))))


(defsection streqv
  :parents (std/basic str::equivalences)
  :short "Case-sensitive string equivalence test."

  :long "<p>@(call streqv) determines if @('x') and @('y') are equivalent when
interpreted as strings.  That is, non-strings are first coerced to be the empty
string (via @(see str-fix)), then we see if these coerced arguments are
equal.</p>

<p>See also @(see str::istreqv) for a case-insensitive alternative.</p>"

  (defund-inline streqv (x y)
    (declare (xargs :guard t))
    (equal (str-fix x) (str-fix y)))

  (local (in-theory (enable str-fix streqv)))

  (defequiv streqv)

  (defthm streqv-of-str-fix
    (streqv (str-fix x) x))

  (defcong streqv equal (str-fix x) 1)
  (defcong streqv equal (char x n) 1)
  (defcong streqv equal (string-append x y) 1)
  (defcong streqv equal (string-append x y) 2))


(defsection tuplep
  :parents (std/basic)
  :short "Recognizers for true-lists of some particular length."
  :long "<p>@(call tuplep) recognizes @('n')-tuples.  For instance:</p>

@({
    (tuplep 3 '(1 2 3))     --> t
    (tuplep 3 '(1 2))       --> nil (not long enough)
    (tuplep 3 '(1 2 3 . 4)) --> nil (not a true-listp)
})

<p>We generally just leave this enabled.</p>"

  (defun tuplep (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (and (true-listp x)
                     (equal (len x) n))
         :exec (and (true-listp x)
                    (eql (length x) n)))))


(defsection impossible
  :parents (std/basic)
  :short "Prove that some case is unreachable using @(see guard)s."

  :long "<p>Logically, @('(impossible)') just returns @('nil'), and
@('(impossible x)') just returns @('x').</p>

<p>But @('impossible') has a guard of @('nil'), so whenever you use it in a
function, you will be obliged to prove that it cannot be executed when the
guard holds.</p>

<p>What good is this?  One use is to make sure that every possible case in a
sum type has been covered.  For instance, you can write:</p>

@({
 (define f ((x whatever-p))
   (case (type-of x)
     (:foo (handle-foo ...))
     (:bar (handle-bar ...))
     (otherwise (impossible))))
})

<p>This is a nice style in that, if we later extend @('x') so that its type can
also be @(':baz'), then the guard verification will fail and remind us that we
need to extend @('f') to handle @(':baz') types as well.</p>

<p>The optional argument to @('impossible') can be used to design your code in
a more convenient way.  Suppose that in the example of the function @('f')
above, both @('handle-foo') and @('handle-bar') are functions that always
return integers.  Then by changing @('(impossible)') to, say, @('(impossible
0)') in the definition of @('f'), you can now prove that @('f') always returns
an integer.  With the original definition of @('f'), you would require the
additional hypothesis @('(whatever-p x)'), and as part of the proof of the
theorem, ACL2 would have to re-prove that the @('otherwise') case is
unreachable.</p>

<p>If somehow @('(impossible)') is ever executed &mdash; e.g., due to program
mode code that is violating guards, or because @(see guard-checking) has been
set to @('nil') or @(':none') &mdash; it just causes a hard error.</p>"

  "<p>@(def impossible)</p>"

  (defun impossible-fn ()
    (declare (xargs :guard nil))
    (er hard 'impossible
        "Reached code that is provably impossible to reach without violating ~
         guards somewhere (see :DOC GUARD).  This could have happened because ~
         you are running code that is in program mode (see :DOC DEFUN-MODE), ~
         or because you have guard checking set to NIL or :NONE (see :DOC ~
         SET-GUARD-CHECKING)."))

  (defmacro impossible (&optional retval)
    ;; We make this a macro because if retval is an mv or involves stobjs or
    ;; something it could get hairy if `impossible' were a function.
    (if retval `(prog2$ (impossible-fn) ,retval) '(impossible-fn)))
  (add-macro-alias impossible impossible-fn))


(defsection impliez

  ;; Added by Alessandro Coglio (coglio@kestrel.edu), Kestrel Institute.

  :parents (std/basic)

  :short "Logical implication defined via @(tsee if)."

  :long
  "<p>Since @(tsee implies) is a function, guards in the consequent must be
verified without assuming the antecedent.  @('impliez') is a macro that expands
to an @(tsee if), so guards in the consequent can be verified assuming the
antecedent.</p>"

  "<p>@(def impliez)</p>"

  (defmacro impliez (p q)
    `(if ,p ,q t)))
