; Centaur Lexer Library
; Copyright (C) 2013 Centaur Technology
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

(in-package "CLEX")
(include-book "sin")
(local (include-book "arithmetic"))
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defsection matching-functions
  :parents (clex)
  :short "Functions for matching text from the start of the input stream."

  :long "<p>Matching functions are the main way of processing a string input
stream @(see sin).  Each matching function can recognize and extract some
particular kind of input from the start of the input stream.  We say that some
matchers are strong and some are weak:</p>

<dl>
<dt>Strong Matcher</dt>
<dd>On success, always matches at least some text.</dd>
<dd>Signature: @('(match-foo ... sin)') &rarr; @('(mv match sin)')</dd>
<dd>Examples: @(see sin-match-lit), @(see sin-match-charset*), ...</dd>

<dt>Weak Matcher</dt>
<dd>May succeed even without matching any text.</dd>
<dd>Signature: @('(match-foo ... sin)') &rarr; @('(mv okp match sin)')</dd>
<dd>Example: @(see sin-match-until-lit)</dd>
</dl>

<p>In either case, the @('match') returned is either</p>

<ul>
<li>@('nil'), to indicate that no text is matched, or</li>
<li>a non-empty string with text extracted from the start of the stream,</li>
</ul>

<p>and the resulting @('sin') is the updated input stream: when no text was
matched, @('sin') is unchanged; otherwise it is advanced just past whatever
text was matched.</p>

<p>Matching functions generally satisfy several basic properties that are
described in @(see def-match-thms).</p>")


(defsection def-match-thms
  :parents (matching-functions)
  :short "Prove basic properties about a matching function."

  :long "<p>The macro @('def-match-thms') can be used to prove some basic
theorems about a new matching function.</p>

<p>Note: typically, you should only want to use this macro if you are defining
a new matching function.  If you are just using existing matching functions
like @(see sin-match-lit) to write your own lexer, this isn't what you
want.</p>

<p>Form: @(call def-match-thms)</p>

<p>This expands into a @(see make-event).  The @('name') you give should be the
name of some newly defined matching function.  We look up the signature of
@('name') from the world and try to prove the matching function satisfies the
following properties.</p>

<p><b>Well-Typed.</b> The match is either a non-empty string or nil.  Note that
there is generally no reason to prove anything about the well-formedness of
@('sin'), itself.</p>

<p><b>Progress.</b> The length of the input stream's contents never increases,
and always decreases when text is matched.</p>

<p><b>Reconstruction.</b> Appending the matched text onto the new input
stream's contents yields the original input stream's contents.  In other words,
the matcher properly matches text from the front of the stream.</p>

<p><b>Graceful Failure.</b> If there is no match, the stream is
unchanged.</p>

<p><b>Match-Free Failure.</b> (weak matchers only) If the weak matcher
fails (i.e., it signals that @('okp') is @('nil')), then the @('match') it
returns is also @('nil').</p>"
  :autodoc nil

  (defun def-match-thms-fn (name world)
    (declare (xargs :mode :program))
    (b* ((__function__ 'def-match-thms)
         (name-s  (symbol-name name))
         (formals (std::look-up-formals name world))
         (returns (std::look-up-return-vals name world))
         ((unless (member 'sin formals))
          (raise "~x0 does not take ~x1 as an argument." name 'sin))
         ((unless (or (equal returns '(nil sin))
                      (equal returns '(nil nil sin))))
          (raise "~x0 does not return (MV MATCH SIN) or (MV OKP MATCH SIN)."
                 name))
         (strong-p (equal returns '(nil sin)))
         (return-names (if strong-p
                           '(?match ?new-sin)
                         '(?okp ?match ?new-sin))))
      `(progn

         (local (in-theory (enable ,name)))

         (defthm ,(intern-in-package-of-symbol (cat "STRINGP-OF-" name-s ".MATCH")
                                               name)
           (b* (((mv . ,return-names) (,name . ,formals)))
             (equal (stringp match)
                    (if match t nil))))

         (defthm ,(intern-in-package-of-symbol (cat "NON-EMPTY-OF-" name-s ".MATCH")
                                               name)
           (b* (((mv . ,return-names) (,name . ,formals)))
             (equal (equal match "")
                    nil)))

         (defthm ,(intern-in-package-of-symbol (cat name-s "-PROGRESS-WEAK")
                                               name)
           (b* (((mv . ,return-names) (,name . ,formals)))
             (<= (len (strin-left new-sin))
                 (len (strin-left sin))))
           :rule-classes ((:rewrite) (:linear)))

         (defthm ,(intern-in-package-of-symbol (cat name-s "-PROGRESS-STRONG")
                                               name)
           (b* (((mv . ,return-names) (,name . ,formals)))
             (implies match
                      (< (len (strin-left new-sin))
                         (len (strin-left sin)))))
           :rule-classes ((:rewrite) (:linear)))

         (defthm ,(intern-in-package-of-symbol (cat name-s "-RECONSTRUCTION")
                                               name)
           (b* (((mv . ,return-names) (,name . ,formals)))
             ;; This very nicely takes advantage of the fact that (COERCE NIL
             ;; 'LIST) happens to be NIL, so we don't even need to check for a
             ;; match.
             (equal (append (explode match) (strin-left new-sin))
                    (strin-left sin))))

         (defthm ,(intern-in-package-of-symbol (cat name-s "-GRACEFUL-FAILURE")
                                               name)
           (b* (((mv . ,return-names) (,name . ,formals)))
             (implies (not match)
                      (equal new-sin sin))))

         ,@(and (not strong-p)
                `((defthm ,(intern-in-package-of-symbol
                            (cat name-s "-MATCH-FREE-FAILURE")
                            name)
                    (b* (((mv . ,return-names) (,name . ,formals)))
                      (implies (not okp)
                               (not match))))))
         )))

  (defmacro def-match-thms (name)
    `(make-event
      (b* ((world (w state))
           (event (def-match-thms-fn ',name world)))
        (acl2::value event)))))

(local (defthm append-of-take-and-nthcdr-free
         (implies (and (equal take (take n x))
                       (force (<= n (len x))))
                  (equal (append take (nthcdr n x))
                         x))))


(define sin-match-everything
  :parents (matching-functions)
  :short "Match everything that remains, no matter what it is."
  ((sin "The @(see sin) stobj."))
  :returns (mv (match "The entire remaining contents of the input stream, as
                       a string, or @('nil') if we're already at the end of
                       the input stream."
                      (or (stringp match)
                          (not match))
                      :rule-classes :type-prescription)
               (sin   "The remainder of the input stream, which will now be
                       empty.  (The only reason you might care about it is to
                       get the final line/column numbers.)"))
  :long "<p>Examples:</p>
@({
 (sin-match-everything [apple])
    -->
 (\"apple\" [])

 (sin-match-everything [])
   -->
 (nil [])
})"

  (b* ((len   (sin-len sin))
       ((when (zp len))
        (mv nil sin))
       (match (sin-firstn len sin))
       (sin   (sin-nthcdr len sin)))
    (mv match sin))
  ///
  ;; This matcher is a bit unusual, so we deal with it by hand instead of using
  ;; def-match-thms.  This lets us take advantage of its stronger progress
  ;; property, etc.
  (defthm str-match-everything.match-under-iff
    (b* (((mv ?match ?new-sin) (sin-match-everything sin)))
      (iff match
           (consp (strin-left sin)))))

  (defthm stringp-of-sin-match-everything.match
    (b* (((mv ?match ?new-sin) (sin-match-everything sin)))
      (equal (stringp match)
             (consp (strin-left sin)))))

  (defthm non-empty-of-sin-match-everything.match
    (b* (((mv ?match ?new-sin) (sin-match-everything sin)))
      (iff (consp (explode match))
           (consp (strin-left sin)))))

  (defthm sin-match-everything-progress
    (b* (((mv ?match new-sin) (sin-match-everything sin)))
      (equal (len (strin-left new-sin))
             0)))

  (defthm sin-match-everything-reconstruction
    (b* (((mv match new-sin) (sin-match-everything sin)))
      (equal (append (explode match) (strin-left new-sin))
             (strin-left sin)))))


(define sin-match-lit
  :parents (matching-functions)
  :short "Match exactly some particular string literal."
  ((lit stringp "The literal string to search for.")
   (sin         "The @(see sin) stobj."))
  :returns (mv (match "@('nil') if no text was matched, or the matched text,
                       i.e., @('lit') itself."
                      (or (stringp match)
                          (not match))
                      :rule-classes :type-prescription)
               (sin "The remainder of the input stream after removing the
                     matched text, if applicable."))

  :long "<p>Examples:</p>

@({
    (sin-match-lit \"apple\" [applesauce])
      -->
    (\"apple\" [sauce])

    (sin-match-lit \"apple\" [candyapple])
      -->
    (nil [candyapple])
})

<p>Corner case: when @('lit') is the empty string we always just fail.
Matching the empty string would be quite degenerate, and failing in this case
we can fit @('sin-match-lit') into the ordinary @(see matching-functions)
paradigm of progress, etc.</p>"

; Historic note.  On 2013-04-25 this function revealed a soundness bug in ACL2.
; I had been debating whether or not LIT should be required to be non-empty in
; the guard.  The MBE below was therefore, for a short time:
;
;       (mbe :logic (or (not (stringp lit))
;                       (equal lit ""))
;            :exec nil)
;
; When I eventually decided to remove the non-emptiness requirement from the
; guard, ACL2 still accepted the now-unjustified MBE, due to a soundness bug
; that was apparently provoked by the combination of DEFABSSTOBJ and TAU!

  (b* (((when (or (mbe :logic (not (stringp lit))
                       :exec nil)
                  (equal lit "")))
        ;; Just fail unless we're given a decent literal to look for.
        (mv nil sin))
       ((unless (sin-matches-p lit sin))
        ;; Not a match, nothing changes.
        (mv nil sin))
       ;; Else have a match.
       ;;  - Match is what we matched, in this case it's exactly lit.
       ;;  - Sin needs to be advanced the appropriate amount.
       (sin (sin-nthcdr (length lit) sin)))
    (mv lit sin))
  ///
  (def-match-thms sin-match-lit)

  (defthmd sin-match-lit.match-when-ok
    (b* (((mv ?match ?new-sin) (sin-match-lit lit sin)))
      (implies match
               (equal match lit))))

  (defthm equal-of-sin-match-lit-and-lit
    ;; We could prove something much stronger, e.g., we could fully
    ;; characterize exactly what match will be, or we could even do a rewrite
    ;; like (implies match (equal match lit)).  But those kinds of rules tend
    ;; to interfere with progress/reconstruction theorems.  So, let's not try
    ;; to rewrite match away.
    (b* (((mv ?match ?new-sin) (sin-match-lit lit sin)))
      (equal (equal match lit)
             (if match
                 (and (stringp lit)
                      (consp (explode lit)))
               (not lit))))))


(define sin-match-some-lit
  :parents (matching-functions)
  :short "Match any one of several string literals."
  ((lits string-listp "The literals to search for, in order.")
   (sin               "The @(see sin) stobj."))
  :returns (mv (match "The first literal in @('lits') that is found at the
                       start of the input stream; @('nil') if none are found."
                      (or (stringp match)
                          (not match))
                      :rule-classes :type-prescription)
               (sin   "The remainder of the input stream, with the @('match')
                       removed, if applicable."))

  :long "<p>Since the @('lits') are searched in order, it is often useful to
search for longer literals first, e.g., when lexing C operators you might want
to search for @('\"++\"') before @('\"+\"').</p>

<p>Corner case: like @(see sin-match-lit), we will always fail to match the
empty string.</p>

<p>Examples:</p>

@({
    (sin-match-some-lit '(\"applesauce\" \"apple\" \"snake\")
                        [applesnake])
     -->
    (\"apple\" [snake])

    (sin-match-some-lit '(\"applesauce\" \"apple\" \"snake\")
                        [applesaucesnake])
     -->
    (\"applesauce\" [snake])

    (sin-match-some-lit '(\"applesauce\" \"apple\" \"snake\")
                        [serpent])
     -->
    (nil [serpent])
})"

  (b* (((when (atom lits))
        (mv nil sin))
       ((mv match1 sin)
        (sin-match-lit (car lits) sin))
       ((when match1)
        (mv match1 sin)))
    (sin-match-some-lit (cdr lits) sin))
  ///
  (def-match-thms sin-match-some-lit)

  (defthm member-of-sin-match-some-lit
    (b* (((mv match ?new-sin) (sin-match-some-lit lits sin)))
      (implies match
               (member match lits)))
    :hints(("Goal" :in-theory (enable sin-match-lit.match-when-ok
                                      member)))))



(define sin-match-charset*
  :parents (matching-functions)
  :short "Match all leading characters in some @(see charset-p)."
  ((set charset-p "Set of characters that should be matched.")
   (sin           "The @(see sin) stobj."))
  :returns (mv (match "The largest prefix of the input stream consisting
                       entirely of matching characters, or @('nil') if there
                       are no matching characters."
                      (or (stringp match)
                          (not match))
                      :rule-classes :type-prescription)
               (sin   "The remainder of the input stream, with the @('match')
                       removed, if applicable."))

  :long "<p>Examples:</p>

@({
    (defcharset num (str::digitp x))

    (sin-match-charset* (num-chars) [apple123])
      -->
    (nil [apple123])

    (sin-match-charset* (num-chars) [123apple])
      -->
    (\"123\" [apple])
})"

  (b* ((num-matches (sin-count-charset set sin))
       ((when (zp num-matches))
        (mv nil sin))
       (match1 (sin-firstn num-matches sin))
       (sin    (sin-nthcdr num-matches sin)))
    (mv match1 sin))
  ///
  (def-match-thms sin-match-charset*)

  (defthm sin-match-charset*-reconstruction-free
    ;; Very weird rule to helps in proving reconstruction theorems in special
    ;; cases like example.lisp:lex-id/keyword, where you are explicitly
    ;; checking whether the match is one thing or another.
    (b* (((mv ?match ?new-sin)
          (sin-match-charset* set sin)))
      (implies (equal chars (explode match))
               (equal (append chars (strin-left new-sin))
                      (strin-left sin)))))

  (defthm sin-match-charset*.match-succeeds
    (b* (((mv ?match ?new-sin) (sin-match-charset* set sin)))
      ;; Originally I wrote this as
      ;;   (iff match (char-in-charset-p (sin-car sin) set))
      ;; But that seems too strong, and ruins, e.g., the progress
      ;; lemmas, where we expect match to stick around.
      (implies (char-in-charset-p (sin-car sin) set)
               match)))

  (defthm chars-in-charset-p-of-sin-match-charset*.match
    (b* (((mv ?match ?new-sin) (sin-match-charset* set sin)))
      ;; Nicely abusing that NIL coerces to NIL...
      (chars-in-charset-p (explode match) set))))


; Matt K. mod, 8/16/2018: After the fix after v8-0 to the tau-system soundness
; bug, the lemma sin-match-until-lit-progress-strong -- which is generated by
; sin-match-until-lit -- failed.  The following two events are a hack to fix
; that problem.  Others are of course welcome to come up with a nicer fix.
(local (in-theory (disable acl2::integerp-of-listpos acl2::natp-of-listpos)))
(add-default-hints
 '((and stable-under-simplificationp
	'(:in-theory (enable ACL2::INTEGERP-OF-LISTPOS)))))


(define sin-match-until-lit
  :parents (matching-functions)
  :short "Match anything that occurs up until the first occurrence of a
particular string literal."
  ((lit stringp "The literal to search for.")
   (sin         "The @(see sin) stobj."))
  :returns (mv (foundp "Was @('lit') found anywhere in the input stream?"
                        booleanp :rule-classes :type-prescription)
               (match "@('nil') when no text is matched, or a non-empty string
                       containing the matched text."
                      (or (stringp match)
                          (not match))
                      :rule-classes :type-prescription)
               (sin   "The remainder of the input stream, with the @('match')
                       removed, if applicable."))

  :long "<p>Note: it is possible for @('match') to be @('nil') even when
@('lit') is @('foundp').  In particular, this happens if @('lit') occurs
immediately at the start of the input stream.</p>

<p>Examples:</p>

@({
    (sin-match-until-lit \"apple\" [snake])
      -->
    (nil nil [snake])

    (sin-match-until-lit \"apple\" [snakeapple])
      -->
    (t \"snake\" [apple])

    (sin-match-until-lit \"apple\" [applesnake])
      -->
    (t nil [applesnake])
})

<p>Corner case: as in @(see sin-match-lit), when @('lit') is the empty string
we always fail.</p>"

  (b* (((when (or (mbe :logic (not (stringp lit))
                       :exec nil)
                  (equal lit "")))
        (mv nil nil sin))
       (pos (sin-find lit sin))
       ((unless pos)
        (mv nil nil sin))
       ((when (eql pos 0))
        (mv t nil sin))
       (match1 (sin-firstn pos sin))
       (sin    (sin-nthcdr pos sin)))
    (mv t match1 sin))
  ///
  (def-match-thms sin-match-until-lit))


(define sin-match-through-lit
  :parents (matching-functions)
  :short "Match anything that occurs up to, and including, the first occurrence
of a particular string literal."
  ((lit stringp "The literal to search for.")
   (sin         "The @(see sin) stobj."))
  :returns (mv (match "@('nil') when no text is matched, or a non-empty string
                       containing the matched text."
                      (or (stringp match)
                          (not match))
                      :rule-classes :type-prescription)
               (sin   "The remainder of the input stream, with the @('match')
                       removed, if applicable."))

  :long "<p>You could use this, for instance, after reading @('/*'), to match
everything until and through @('*/').</p>

<p>Examples:</p>

@({
    (sin-match-through-lit \"apple\" [snake])
      -->
    (nil [snake])

    (sin-match-through-lit \"apple\" [snakeapplesauce])
      -->
    (\"snakeapple\" [sauce])
})

<p>Corner case: as in @(see sin-match-lit), when @('lit') is the empty string
we always fail.</p>"

  (b* (((when (or (mbe :logic (not (stringp lit))
                       :exec nil)
                  (equal lit "")))
        (mv nil sin))
       (pos (sin-find lit sin))
       ((unless pos)
        (mv nil sin))
       (stop   (+ pos (length lit)))
       (match1 (sin-firstn stop sin))
       (sin    (sin-nthcdr stop sin)))
    (mv match1 sin))
  ///
  (def-match-thms sin-match-through-lit))

