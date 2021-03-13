; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This tool was created in response to a suggestion from Eric McCarthy, who we
; thank along with Eric Smith and Alessandro Coglio for helpful feedback.

; For examples see add-io-pairs-tests.lisp.

; Possible future enhancements:

; - Consider allowing state and stobj inputs (but still, not outputs) provided
;   we prove that they don't affect the answer (so, they would only be for side
;   effect).

; - Consider reporting redundancy when a proposed I/O pair already exists.
;   Such reporting could be a bit awkward if some proposed I/O pairs already
;   exist, but not all.  Also, care would need to be taken if :debug t was
;   supplied previously but not now, or vice-versa; currently, one gets a
;   redefinition error in that case.

; - Change or extend remove-io-pairs to allow removal of specific pairs.  In
;   that case, it would be a good idea to check whether any I/O pairs remain
;   for a given function, and if not, then print a message saying so and
;   unmemoize it, and document this behavior.

; - Support add-io-pair(s) with a function introduced by defun-nx.  This would
;   require removing the xargs declaration of :non-executable t.

; - Put some functions in this file into guard-verified :logic mode.

; - Replace add-io-pairs-tests.lisp by a version that uses run-script so that
;   the log, including output for some failures, can be checked.

; - Loosen the requirement for guard verification to just being in :logic mode,
;   not necessarily guard-verified, even though memoization will then only take
;   place when using a :program-mode wrapper to slip into raw Lisp.  This is
;   probably easiliy done by adding an :ideal-okp that is passed to memoize,
;   though some documentation would need updating below and some testing would
;   of course be necessary.

; - Allow :debug to be an evisc-tuple used during cw printing.  This should be
;   quite easy to implement, but be sure to check that the supplied evisc-tuple
;   is valid, perhaps using standard-evisc-tuplep.

; - Consider adding an option that allows recursive calls to re-invoke the new
;   function, thus allowing recursive calls to look up I/O pairs.  This would
;   likely involve making a corresponding enhancement to memoize for its
;   :invoke option.  As noted by the "Essay on the :INVOKE option of Memoize"
;   in ACL2 source file other-events.lisp, "There is serious danger of looping
;   unless we are careful."

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(set-state-ok t)
(program)

(defxdoc add-io-pair
  :parents (add-io-pairs)
  :short "Speed up a function using a verified input-output pair"
  :long "<p>@('Add-io-pair') is just a convenient abbreviation for @(tsee
 add-io-pairs) in the case of a single input-output pair.  See @(see
 add-io-pairs).</p>

 @({
 Examples:
 (add-io-pair (f 3) '(3 . 3))

 (add-io-pair (g 3 4) (mv 30 40))

 (add-io-pair
  (rtl::primep (primes::bn-254-group-prime)) t
  :test eql
  :hints ((\"Goal\"
           :in-theory
           (enable primes::primep-of-bn-254-group-prime-constant))))

 General Form:
 (add-io-pair fn input output &key hints test debug verbose)
 })

 <p>where @('fn') is a @(see guard)-verified function symbol whose arguments do
 not include @(tsee state) or any user-defined @(tsee stobj).  The arguments to
 the macro are not evaluated.</p>

 <p>@('Add-io-pair') is merely a convenient way to invoke the utility @(see
 add-io-pairs) when there is a single input/output pair; see @(see
 add-io-pairs) for further documentation, including discussion of the
 keywords (which are optional).</p>")

(defxdoc add-io-pairs
  :parents (std/util)
  :short "Speed up a function using verified input-output pairs"
  :long "<p>For examples, see the book @('std/util/add-io-pairs-tests.lisp') in
 @(see community-books).  Also see @(see add-io-pair) for an equivalent utility
 with slightly simpler syntax that can add a single input-output pair.</p>

 <p><b>Summary</b>.  This utility provides a way to redefine a function so that
 it can quickly look up a function call @('(fn i1 ... ik)') to produce its
 output, @('val'), thus avoiding its usual computation.  We call such a pair
 @('((fn i1 ... ik) val)') an ``I/O pair'' (for @('fn')).  Each I/O pair is
 ``verified'': a proof obligation has been met showing that the input list is
 indeed mapped to the corresponding output.  The (verified) I/O pairs are
 stored efficiently in a @(see table).  See @(tsee show-io-pairs) for how to
 print the current I/O pairs.  The present utility, @('add-io-pairs'), extends
 the table by adding the specified I/O pairs and also redefines the specified
 function to take advantage of the updated table.</p>

 @({
 Examples (see std/util/add-io-pairs-tests.lisp):

 (add-io-pairs (((f 3) '(3 . 3))))

 (add-io-pairs (((g 3 6) (mv (* 3 10) (* 6 10)))
                ((g (/ 40 10) (/ 50 10)) (mv 40 50))))

 (add-io-pairs
  (((rtl::primep (primes::secp256k1-field-prime)) t)
   ((rtl::primep (primes::bn-254-group-prime)) t)
   ((rtl::primep (primes::baby-jubjub-subgroup-prime)) t))
  :debug t
  :hints ((\"Goal\"
           :in-theory
           (enable primes::primep-of-baby-jubjub-subgroup-prime-constant
                   primes::primep-of-bn-254-group-prime-constant
                   primes::primep-of-secp256k1-field-prime-constant))))

 General Form:
 (add-io-pairs tuples &key hints debug test verbose)
 })

 <p>where the arguments, which are not evaluated, are described below and the
 keyword arguments are optional.</p>

 <ul>

 <li>@('Tuples') is a list of I/O pairs, each of the form @('((fn i_1 ... i_k)
 val)') where @('fn') is a @(see guard)-verified function symbol, each @('i_n')
 is a term, and @('val') is a term.  (The @(see term)s need not be translated.)
 @('Fn') must be the same in each of these I/O pairs, and must not take @(see
 state) or any user-defined @(see stobj) as an argument.  All @('i_n') and
 @('val') are evaluated to produce values used as inputs and corresponding
 output; therefore, these terms should not contain any free variables.</li>

 <li>@('Hints') (optional, default @('nil')), when non-@('nil'), is used as the
 @(':')@(tsee hints) argument for the theorem discussed below.</li>

 <li>@('Test') (optional, default @('equal')) is the equality variant &mdash;
 @(tsee eq), @(tsee eql), or @(tsee equal) &mdash; used for testing equality of
 each input of @('fn') to a corresponding input of an I/O pair; or, @('test')
 can be a true-list of such equality variants, as described in the concluding
 remarks below.</li>

 <li>@('Debug') (optional, default @('nil')), when non-@('nil'), causes @(tsee
 cw) to print a message to the terminal when an I/O pair is being used during
 evaluation (thus avoiding the usual computation for @('fn')).</li>

 <li>@('Verbose') (optional, default @('nil')), when non-@('nil'), avoids
 suppressing output (other than what is currently globally suppressed; see
 @(see set-inhibit-output-lst)).  This argument may be particularly useful when
 the proof fails for the theorem, described below, that equates @('fn') to the
 corresponding new function (that looks up inputs from a table of all verified
 I/O pairs).</li>

 </ul>

 <p>If @('tuples') is @('nil') then the call of @('add-io-pairs') is a no-op.
 Otherwise, as noted above, the function symbol (@('fn'), above) must be the
 same for each I/O pair.</p>

 <p>This event defines a new function, denoted @('new-fn') below (the actual
 name is generated automatically), to compute as follows.  First, the inputs
 @('i_n') and corresponding output @('val') of an I/O pair @('((fn i_1 ... i_k)
 val)') are evaluated to produce a corresponding ``evaluated I/O pair'' @('((fn
 j_1 ... j_k) v)'), where the values of @('i_n') and @('val') are @('j_n') and
 @('v'), respectively.  Then @('new-fn') is defined so that @('(fn j_1
 ... j_k)') is computed by finding that evaluated I/O pair and returning
 @('v'), thus avoiding the usual computation for @('fn').  That is: a call of
 @('new-fn') considers every evaluated I/O pair @('((fn j_1 ... j_k) val)'),
 whether added by this call of @('add-io-pairs') or a previous such call,
 searching for one whose inputs @('(j_1 ... j_k)') equal that call's actual
 parameters, and returning the corresponding output @('v') in that case; if no
 such evaluated I/O pair is found, then @('new-fn') just calls @('fn').  This
 description is accurate if @('fn') returns a single value; otherwise, if
 @('fn') returns @('n') values where @('n') is greater than 1, @('val') should
 evaluate to multiple values @('(mv v_1 .... v_n)'), in which case the multiple
 values returned by @('new-fn') are @('v_1') through @('v_n').  The definition
 of @('new-fn') thus has roughly the following form, where: @('IO-LOOKUP')
 denotes a lookup utility that searches for the given inputs among evaluated
 I/O pairs, returning the one-element list containing the value associated with
 those inputs, if found; @('TEST') is the value for @(':test') discussed
 above (defaulting to @('equal')); and @('IO-PAIRS') is the extension of the
 existing evaluated I/O pairs for @('fn') by the current call of
 @('add-io-pairs'), as described above.</p>

 @({
 (defun new-fn (x1 ... xk) ; same formals as for fn
   (declare (xargs :guard t)) ; ensure guard-verified
   <declare_forms> ; same declare forms as for fn
   (let ((pair <<IO-LOOKUP (x1 ... xk) in 'IO-PAIRS using 'TEST>>))
     (if pair
         (car pair)
       (fn x))))
 })

 <p>The event displayed above is approximate.  One can see the precise
 definition produced by evaluating a call of @('add-io-pairs') and using
 @(':')@(tsee pcb!)@(' :x') to see what has been generated.  Alternatively, run
 @('add-io-pairs') using option @(':verbose t') and peruse the log.</p>

 <p>In the underlying Common Lisp, @('fn') is redefined to be @('new-fn'), but
 with a twist: once control passes from @('fn') to @('new-fn'), all recursive
 calls of @('fn') will be calls of the old version of @('fn'), without
 re-entering @('new-fn').  Note that when @('new-fn') is called on an input
 list that has an associated I/O pair, the corresponding output is returned
 immediately without calling @('fn') (which of course is the point of this
 tool); thus, in particular, side effects from @('fn') such as printing with
 @(tsee cw) will not take place for such an input list.</p>

 <p>A generated proof obligation has the following form, where @('HINTS') below
 is the non-@('nil') @(':hints') keyword if supplied by @('add-io-pairs');
 otherwise the @(':hints') keyword below is omitted.</p>

 @({
 (defthm <generated_name>
   (equal (fn x1 ... xk)
          (new-fn x1 ... xk))
   :hints HINTS ; omitted if the given :hints is nil or omitted
   :rule-classes nil)
 })

 <p>We conclude with a few remarks.</p>

 <p>Remark 1.  When the value @(':test') is a non-@('nil') list, its length
 should be the number of inputs of @('fn') and each member should be @('eq'),
 @('eql'), or @('equal'), indicating the test used when comparing an input at
 that position to an input specified in an evaluated I/O pairs for @('fn').</p>

 <p>Remark 2.  Evaluation of input and output terms in an I/O pair is performed
 with guard-checking set to @('nil') (see @(see set-guard-checking)) and
 attachments allowed (see @(see defattach)).</p>

 <p>Remark 3.  Although @('fn') is required to be @(see guard)-verified, one
 may be able to avoid most of the effort of guard verification by using @(tsee
 ec-call).  Here is a trivial example that illustrates the technique.</p>

 @({
 ACL2 !>(defun h (x)
          (declare (xargs :guard t))
          (ec-call (car x)))

 Since H is non-recursive, its admission is trivial.  We could deduce
 no constraints on the type of H.

 Computing the guard conjecture for H....

 The guard conjecture for H is trivial to prove.  H is compliant with
 Common Lisp.

 Summary
 Form:  ( DEFUN H ...)
 Rules: NIL
 Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
  H
 ACL2 !>(add-io-pairs (((h 3) nil) ((h '(a b c)) 'a)) :debug t)
  H
 ACL2 !>(h 3)
 ; DEBUG: Found io-pair for input list (3).
 NIL
 ACL2 !>(h '(a b c))
 ; DEBUG: Found io-pair for input list ((A B C)).
 A
 ACL2 !>(h '(e f))
 E
 ACL2 !>(h 7)


 ACL2 Error in TOP-LEVEL:  The guard for the function call (CAR X),
 which is (OR (CONSP X) (EQUAL X NIL)), is violated by the arguments
 in the call (CAR 7).
 See :DOC set-guard-checking for information about suppressing this
 check with (set-guard-checking :none), as recommended for new users.
 To debug see :DOC print-gv, see :DOC trace, and see :DOC wet.

 ACL2 !>(add-io-pair (h 7) nil)
  H
 ACL2 !>(h 7)
 NIL
 ACL2 !>(h '(a b c))
 A
 ACL2 !>
 })

 <p>Note that there is no debug printing in the final two calls.  This isn't
 surprising for @('(h 7)'), since the call of @('add-io-pair') for @('(h 7)')
 did not specify keyword argument @(':debug').  It may be more surprising that
 debug printing no longer occurs for @('(h '(a b c))').  The reason is that
 each invocation of @('add-io-pair') or @('add-io-pairs') defines a new
 replacement function (denoted @('new-fn') in the discussions above), which is
 based on the updated table of evaluated I/O pairs and the @(':debug') option
 provided to the new invocation.</p>

 <p>Remark 4.  A more general utility, which allows the substitution of one
 function for another during execution, is available with the @(':invoke')
 argument of @(tsee memoize).  Indeed, @('add-io-pairs') actually works by
 invoking @('(memoize 'fn :invoke 'new-fn)'), where @('new-fn') is as above.
 Note that this memoization does not perform @('memoize')'s usual function of
 saving computational results.</p>

 <p>Remark 5.  If you include a book with an @('add-io-pairs') form for a
 function symbol, @('fn'), to which you have already added I/O pairs in the
 current session, then by default an error will occur.  The key relevant
 observation is that during book certification, when @('add-io-pairs') defines
 @('new-fn') as discussed above, that definition is saved in the book's @(see
 certificate).  (Technical note: This is a consequence of the use of @(tsee
 make-event) in the implementation of @('add-io-pairs').)  Without an error,
 ACL2 would simply use that saved definition of @('new-fn'), discarding the I/O
 pairs previously added in the current session.</p>

 <p>The error message explains how to allow the @(tsee include-book) to
 complete without error, merging in all I/O pairs from the current session and
 included books by wrapping it in a call of the macro, @(tsee merge-io-pairs),
 whose first argument is @('fn').  So a sequence of events might look like
 this.</p>

 @({
 (defun f (x)
   (declare (xargs :guard t))
   (cons x x))
 (include-book \"book1\") ; has calls of add-io-pair(s) for f
 (merge-io-pairs
   f
   (include-book \"book2\") ; has calls of add-io-pair(s) for f
   )
 })

 <p>An analogous problem occurs with @(tsee encapsulate), when there are @(see
 local) calls of @('add-io-pairs') followed by non-local calls.  Much as
 @('certify-book') saves the definition of @('new-fn') in the book's
 certificate, ACL2 saves such a definition from the first pass of the
 @('encapsulate') and detects missing I/O pairs (the local ones) in the second
 pass.  We expect local calls of @('add-io-pairs') inside @('encapsulate') to
 be rare, so we do not discuss them further.</p>

 <p>Although the discussion above and the error message should suffice, you can
 get more understanding by looking at examples in the section ``Including a
 book'' in @(see community-book) @('std/util/add-io-pairs-tests.lisp').  For
 technical details (probably not necessary), you are also welcome to see @(see
 add-io-pairs-details).</p>")

(defxdoc add-io-pairs-details
  :parents (add-io-pairs)
  :short "Details about @(tsee add-io-pairs)"
  :long "<p>This rather technical topic is intended for those who have read the
 documentation for @(tsee add-io-pairs) and related topics but would like a
 more complete understanding of how @(tsee add-io-pairs) works.  Our hope is
 that very few will have any reason to read the present topic!</p>

 <p>A key aspect of the implementation of @('add-io-pairs') is the use of a
 @(see table), @('io-pairs-table'), to store all I/O pairs.  Indeed, the
 utilities @(tsee show-io-pairs) and @(tsee get-io-pairs) retrieve I/O pairs
 from this table.  When @('add-io-pairs') is invoked on I/O pairs for a
 function symbol, @('fn'), it extends that table with those I/O pairs and then
 generates a @(tsee defun) event for a new function.  The documentation topic
 @(see add-io-pairs) explains that this new function, @('new-fn'), computes by
 looking up the inputs in the available I/O pairs to get the result immediately
 if possible, otherwise calling @('fn').  Finally, it uses a special form of
 @(see memoization) to compute calls of @('fn') by calling @('new-fn').</p>

 <p>The following log fleshes out the explanation above.  It shows that
 @('add-io-pairs') generates a call of @(tsee make-event), which we expand
 below to see the events created by that @('make-event') invocation.  Comments
 have been inserted in lower case into the final output below.</p>

 @({
 ACL2 !>(defun f (x)
          (declare (xargs :guard t))
          (cons x x))
 [[.. output elided ..]]
  F
 ACL2 !>:trans1 (add-io-pair (f 3) (cons 3 (/ 6 2)))
  (ADD-IO-PAIRS (((F 3) (CONS 3 (/ 6 2)))))
 ACL2 !>:trans1 (add-io-pairs (((f 3) (cons 3 (/ 6 2)))))
  (WITH-OUTPUT
   :OFF :ALL :ON ERROR :GAG-MODE NIL
   (MAKE-EVENT
     (B* ((TUPLES '(((F 3) (CONS 3 (/ 6 2)))))
          (HINTS 'NIL)
          (DEBUG 'NIL)
          (TEST 'EQUAL)
          (WRLD (W STATE))
          ((WHEN (NULL TUPLES))
           (VALUE '(VALUE-TRIPLE :EMPTY-IO-PAIRS)))
          (CTX 'ADD-IO-PAIRS)
          ((ER IO-DOUBLET-LST)
           (ADD-IO-PAIRS-TRANSLATE-TUPLES TUPLES CTX WRLD STATE))
          (FN (CAAR (CAR TUPLES)))
          (EVENTS (ADD-IO-PAIRS-EVENTS FN
                                       IO-DOUBLET-LST HINTS DEBUG TEST WRLD)))
         (VALUE (CONS 'PROGN EVENTS)))
     :ON-BEHALF-OF :QUIET!))
 ACL2 !>(b* ((tuples '(((f 3) (cons 3 (/ 6 2)))))
             (hints 'nil)
             (debug 'nil)
             (test 'equal)
             (wrld (w state))
             ((when (null tuples))
              (value '(value-triple :empty-io-pairs)))
             (ctx 'add-io-pairs)
             ((er io-doublet-lst)
              (add-io-pairs-translate-tuples tuples ctx wrld state))
             (fn (caar (car tuples)))
             (events (add-io-pairs-events fn io-doublet-lst hints debug
                                          test wrld)))
          (value (cons 'progn events)))
  (PROGN

  ; Cause an error when including a book or running the second pass of an
  ; encapsulate, if the I/O pairs for F in the io-pairs table do not match
  ; those in the table from a previous invocation -- unless we are in the
  ; scope of merge-io-pairs for F.
   (CHECK-IO-PAIRS-LENIENCE F NIL ADD-IO-PAIRS)

  ; Update the I/O pairs for F in the io-pairs-table.
   (TABLE
       IO-PAIRS-TABLE 'F
       (LET ((OLD-ENTRY (CDR (ASSOC-EQ 'F
                                       (TABLE-ALIST 'IO-PAIRS-TABLE WORLD)))))
            (UPDATE-IO-LOOKUP-LST '(((3) (3 . 3)))
                                  OLD-ENTRY)))

  ; Define the new-fn for F.
   (DEFUN F29623679 (X)
          (DECLARE (XARGS :VERIFY-GUARDS T))
          (DECLARE (XARGS :GUARD T))
          (LET* ((IO-LOOKUP-VAR0 '((3 (3 . 3))))
                 (IO-LOOKUP-VAR0 (IO-LOOKUP IO-LOOKUP-VAR0 EQUAL X)))
                (IF IO-LOOKUP-VAR0 (CAR IO-LOOKUP-VAR0)
                    (F X))))

  ; Prove that F equals its new-fn, as required by the memoize call below.
   (DEFTHM F52318143 (EQUAL (F X) (F29623679 X))
           :RULE-CLASSES NIL)

  ; Remove any existing memoization of F (redundant if F is not memoized).
   (UNMEMOIZE 'F)

  ; Arrange for F to call its new-fn.
   (MEMOIZE 'F :INVOKE 'F29623679))
 ACL2 !>
 })

 <p>It is also instructive to look at the implementation of @(tsee
 merge-io-pairs).  We can see what is going on by using single-step
 macroexpansion, below: first, @('push-io-pairs-lenience') removes any
 @('check-io-pairs-lenience') checks discussed above for the indicated function
 symbols; next, the books are included; then, @(tsee install-io-pairs) merges
 all I/O pairs for each function (as discussed below); and finally, the
 @('pop-io-pairs-lenience') call undoes the effect of the
 @('push-io-pairs-lenience') call.</p>

 @({
 ACL2 !>:trans1 (merge-io-pairs (f g h)
                                (include-book \"book1\")
                                (include-book \"book2\"))
  (PROGN (PUSH-IO-PAIRS-LENIENCE F G H)
         (INCLUDE-BOOK \"book1\")
         (INCLUDE-BOOK \"book2\")
         (INSTALL-IO-PAIRS F)
         (INSTALL-IO-PAIRS G)
         (INSTALL-IO-PAIRS H)
         (POP-IO-PAIRS-LENIENCE F G H))
 ACL2 !>
 })

 <p>The discussion above leads us to look at the implementation of @(tsee
 install-io-pairs), again using a log (below).  Notice that the events are
 essentially the same as for @('add-io-pairs'), except that the table is not
 changed.  In particular, there is still a call of
 @('check-io-pairs-lenience'), for essentially the same reason: imagine if
 @('(install-io-pairs f)') is in a certified book that is included after having
 added I/O pairs for @('f') in the current session.</p>

 @({
 ACL2 !>:trans1 (install-io-pairs f)
  (WITH-OUTPUT
   :OFF :ALL :ON ERROR :GAG-MODE NIL
   (MAKE-EVENT
     (B* ((FN 'F)
          (HINTS 'NIL)
          (DEBUG 'NIL)
          (TEST 'EQUAL)
          (WRLD (W STATE))
          (IO-DOUBLET-LST :SKIP)
          (EVENTS (ADD-IO-PAIRS-EVENTS FN
                                       IO-DOUBLET-LST HINTS DEBUG TEST WRLD)))
         (VALUE (CONS 'PROGN EVENTS)))
     :ON-BEHALF-OF :QUIET!))
 ACL2 !>(b* ((fn 'f)
             (hints 'nil)
             (debug 'nil)
             (test 'equal)
             (wrld (w state))
             (io-doublet-lst :skip)
             (events (add-io-pairs-events fn io-doublet-lst hints debug
                                          test wrld)))
          (value (cons 'progn events)))
  (PROGN (CHECK-IO-PAIRS-LENIENCE F NIL INSTALL-IO-PAIRS)
         (DEFUN F1824557376 (X)
                (DECLARE (XARGS :VERIFY-GUARDS T))
                (DECLARE (XARGS :GUARD T))
                (LET* ((IO-LOOKUP-VAR0 'NIL)
                       (IO-LOOKUP-VAR0 (IO-LOOKUP IO-LOOKUP-VAR0 EQUAL X)))
                      (IF IO-LOOKUP-VAR0 (CAR IO-LOOKUP-VAR0)
                          (F X))))
         (DEFTHM F1847247744
                 (EQUAL (F X) (F1824557376 X))
                 :RULE-CLASSES NIL)
         (UNMEMOIZE 'F)
         (MEMOIZE 'F :INVOKE 'F1824557376))
 ACL2 !>
 })

 <p>We conclude by noting that @(tsee remove-io-pairs) not only removes all I/O
 pairs for the indicated function symbols from the @('io-pairs-table'), but
 also unmemoizes those function symbols.  By contrast, @(tsee
 deinstall-io-pairs) leaves the @('io-pairs-table') unchanged, merely
 unmemoizing the indicated function.</p>")

(defxdoc merge-io-pairs
  :parents (add-io-pairs)
  :short "Incorporate I/O pairs from different sources"
  :long "@({
 General Forms:
 (merge-io-pairs fn event_1 ... event_n)
 (merge-io-pairs (fn_1 ... fn_k) event_1 ... event_n)
 })

 <p>where @('fn') and each @('fn_i') are symbols and each @('event_i') is an
 @(see event) form.</p>

 @({
 Example Forms:
 (merge-io-pairs f (include-book \"my-book\"))
 (merge-io-pairs (f g h) (include-book \"book1\") (include-book \"book2\"))
 })

 <p>The second General Form above, @('(merge-io-pairs (fn_1 ... fn_k) event_1
 ... event_n)'), has an effect equivalent to iterating the first general form
 as follows.</p>

 @({
 (merge-io-pairs fn_1
  (merge-io-pairs fn_2
   ...
   (merge-io-pairs fn_{k-1}
    (merge-io-pairs fn_k event_1 ... event_n))))
 })

 <p>So we focus below on the first General Form.</p>

 <p>Normally you will use @('merge-io-pairs') when an error occurs in
 @('add-io-pairs') while including a book; see Remark 5 of the documentation
 for @(see add-io-pairs) for explanation.  In short: by wrapping
 @('(merge-io-pairs fn ...)') around one or more @(tsee include-book) events,
 as illustrated in the Example Forms above, you allow all @('add-io-pairs')
 forms in the books to complete in a manner that merges together all the I/O
 pairs for @('fn').</p>")

(defxdoc remove-io-pairs
  :parents (add-io-pairs)
  :short "Remove input-output pairs"
  :long "<p>For relevant background, see @(see add-io-pairs), which modifies a
 function by looking up the result for specified input-output pairs.  The
 utility @('remove-io-pairs') removes all such pairs for the specified function
 symbols.</p>

 @({
 General Forms:
 (remove-io-pairs fn1 ... fnk)
 (remove-io-pairs :all)
 })

 <p>where the arguments are not evaluated.  The use of @(':all') specifies that
 all I/O pairs are to be removed for all function symbols; otherwise, all I/O
 pairs are removed only for the specified function symbols.  A warning is
 printed for each input @('fni') that does not currently have any I/O
 pairs.</p>

 <p>Remark.  As @(tsee add-io-pairs) actually memoizes functions,
 @('remove-io-pairs') unmemoizes the specified functions.  For a utility that
 unmemoizes while preserving I/O pairs for possible re-installation later, see
 @(see deinstall-io-pairs).</p>")

(defxdoc get-io-pairs
  :parents (add-io-pairs)
  :short "Return a list of verified input-output pairs"
  :long "<p>See @(see show-io-pairs) for a more user-friendly display of the
 current I/O pairs.  See @(see add-io-pairs) for relevant background.</p>

 <p>@('Get-io-pairs') returns all evaluated I/O pairs for the specified
 function symbols.</p>

 @({
 General Form:
 (get-io-pairs :all)
 (get-io-pairs fn1 ... fnk)
 })

 <p>where the arguments are not evaluated.  The use of @(':all') specifies that
 all I/O pairs are to be returned; otherwise, all I/O pairs are returned only
 for the specified functions, and a warning is printed for those that do not
 currently have any I/O pairs.</p>

 <p>A single value is returned, which is a list representing all evaluated I/O
 pairs for the indicated function symbols.  Each member of the list has the
 form @('((fn j_1 ... j_k) v)'), where @('v') results from the application of
 @('fn') to the input list @('(j_1 ... j_k)') &mdash; where in the case that
 @('fn') returns multiple values @('v_1'), ..., @('v_n'), then @('v') is
 actually the list @('(mv v_1 .. v_n)'), and otherwise @('v') is just the
 result.</p>

 <p>A warning is printed for each @('fni') that has no associated I/O
 pairs.</p>

 <p>Note that unlike @(tsee show-io-pairs), the form @('(get-io-pairs)') simply
 returns @('nil'), i.e., @(':all') is not implicit when no arguments are
 supplied.  The reason is that @('get-io-pairs') is intended primarily for use
 in programs, where the list of function symbols might be computed.</p>")

(defxdoc show-io-pairs
  :parents (add-io-pairs)
  :short "Display verified input-output pairs"
  :long "<p>See @(see add-io-pairs) for relevant background.
 @('Show-io-pairs') prints I/O pairs in a pleasant format, each starting on a
 new line.  It is evaluated only for its side effect of printing.  See @(see
 get-io-pairs) for a related utility, which returns a list of evaluated I/O
 pairs.</p>

 <p>@('Show-io-pairs') displays all (verified) I/O pairs for the specified
 function symbols.  Normally printing goes to the terminal, but more generally
 it goes to @(tsee standard-co).</p>

 @({
 General Forms:
 (show-io-pairs :all)
 (show-io-pairs) ; same as above
 (show-io-pairs fn1 ... fnk) ; k > 0
 })

 <p>where the arguments are not evaluated.  If no arguments are supplied, or
 equivalently there is a single argument, @(':all'), then all I/O pairs are to
 be printed; otherwise, all I/O pairs are printed only for the specified
 function symbols.</p>

 <p>Each I/O pair is printed in the format expected as input to @(tsee
 add-io-pairs), that is, the inputs and result are terms.  In other words,
 @('add-io-pairs') prints I/O pairs, not evaluated I/O pairs (again, see @(see
 add-io-pairs) for relevant background).  Moreover, @('show-io-pairs') displays
 the inputs and result as quoted terms, such as @(''abc'), even when they
 result from a call of @('add-io-pairs') in which the terms were not all
 quoted, e.g., @('(car '(abc def))').</p>

 <p>A warning is printed for each @('fni') that has no associated I/O
 pairs.</p>")

(defxdoc install-io-pairs
  :parents (add-io-pairs)
  :short "Install input-output pairs"
  :long "@({
 General Form:
 (install-io-pairs fn &key hints debug (test 'equal) verbose)
 })

 <p>where the keywords have the same function as for @(tsee add-io-pairs).</p>

 <p>For relevant background, see @(see add-io-pairs).  Evaluate
 @('(install-io-pairs fn)') to undo the effect of @(tsee
 deinstall-io-pairs).</p>")

(defxdoc deinstall-io-pairs
  :parents (add-io-pairs)
  :short "Deinstall input-output pairs"
  :long " @({
 General Form:
 (deinstall-io-pairs fn)
 })

 <p>For relevant background, see @(see add-io-pairs).  This is just an alias
 for @(tsee unmemoize), thus causing evaluation to use the original definition
 of the given function symbol, @('fn').  The I/O pairs for @('fn') are still
 stored, unlike @(tsee remove-io-pairs); thus, you can later evaluate
 @('(install-io-pairs fn)') to restore the use of I/O pairs in the evaluation
 of @('fn').</p>")

(defmacro add-io-pair (fn/input output &key hints debug test verbose)
  `(add-io-pairs ((,fn/input ,output))
                 ,@(and hints `(:hints ,hints))
                 ,@(and debug `(:debug ,debug))
                 ,@(and test `(:test ,test))
                 ,@(and verbose `(:verbose ,verbose))))

(table io-pairs-table nil nil

; In this table, each key, fn, is a function symbol that is associated with an
; N-io-lookup data structure, where N is the input arity of the key.  Such a
; structure is intended to represent I/O pairs, which can be converted to a
; list of I/O pairs with function io-lookup-entry-to-io-pairs.

; The function io-lookup-fn is used to look up a list of actual parameters of a
; function call.  Here is how that works.  If N is 0 then an N-io-lookup data
; structure is arbitrary in general; but for the key, fn, it is a one-element
; list.  If the arity of fn is 0, then the unique element of that list is the
; value of (fn).  Otherwise N > 0, and an N-io-lookup data structure is an
; alist each of whose cdrs is a list of {N-1}-io-lookup data structures.  For
; the key, fn, we look up an argument list (a1 ... an) in its value, D0, by
; following the path down the N-io-lookup data structure where N is the arity
; of fn: first we look up a1 to get an {N-1}-io-lookup data structure D1, then
; we look up a2 to get an {N-1}-io-lookup data structure D2, and so on, until
; finally we look up an to get a 0-io-lookup data structure, which is a
; singleton list containing the value of fn applied to (a1 ... an).

; We avoid bothering to establish a reaoonably complete guard for this table,
; instead assuming that add-io-pairs will do the necessary checking.  We do not
; feel obligated to protect against bad entries that could arise from direct
; writing to this table that avoids the approved interfaces (add-io-pairs and
; remove-io-pairs).  We do however require that the key be a function symbol,
; just to be extra safe that the use of local doesn't somehow break
; get-io-pairs, which relies on the keys being function symbols.

       :guard (function-symbolp key world))

(table io-pairs-lenience-table nil nil

; Note that we do not require the key to be a function symbol.  We want to be
; able to set the lenience (typically by way of merge-io-pairs) before we have
; introduced the function of interest (which may be defined in a book we want
; to include).

; Each value in the table is typically a list of nils.  The empty list
; signifies that lenience is being checked; see push-io-pairs-lenience and
; pop-io-pairs-lenience.

       :guard (and (symbolp key)
                   (true-listp val)))

(defun update-io-lookup-init (args val)

; See io-pairs-table for a discussion of io-lookup tables.

  (declare (xargs :guard (true-listp args)))
  (cond ((endp args)
         val)
        (t
         (acons (car args)
                (update-io-lookup-init (cdr args) val)
                nil))))

(defun update-io-lookup (keys val x)

; See io-pairs-table for a discussion of io-lookup tables.

; Examples:

;   ACL2 !>(update-io-lookup '(a b c) 18 '((A (B (C . 17)))))
;   ((A (B (C . 18))))
;   ACL2 !>(update-io-lookup '(a b d) 18 '((A (B (C . 17)))))
;   ((A (B (D . 18) (C . 17))))
;   ACL2 !>(update-io-lookup '(a b c) 20 '((A (B (D . 18) (C . 17)))))
;   ((A (B (D . 18) (C . 20))))
;   ACL2 !>(update-io-lookup '(a e c) 20 '((A (B (D . 18) (C . 17)))))
;   ((A (E (C . 20)) (B (D . 18) (C . 17))))
;   ACL2 !>

  (cond ((endp keys) val)
        (t (let ((pair (assoc-equal (car keys) x)))
             (cond (pair (put-assoc-equal (car keys)
                                          (update-io-lookup (cdr keys)
                                                            val
                                                            (cdr pair))
                                          x))
                   (t (acons (car keys)
                             (update-io-lookup-init (cdr keys) val)
                             x)))))))

(defun update-io-lookup-lst (lst x)
  (cond ((endp lst) x)
        (t (update-io-lookup-lst (cdr lst)
                                 (let* ((pair (car lst))
                                        (keys (car pair))
                                        (val (cdr pair)))
                                   (update-io-lookup keys val x))))))

(defun io-lookup-fn (var keys tests)

; The variable, var, initially represents the value associated with a function
; symbol, fn, in the io-pairs table.  That value is an io-lookup table, where
; keys is intended to be the list of values of the actual parameters of a call
; of fn.  (See io-pairs-table for a discussion of io-lookup tables.)  As we
; work our way through keys, var represents the result of working our way
; correspondingly through that io-lookup table.

  (declare (xargs :guard (true-listp keys)))
  (cond ((endp keys) var)
        (t `(let ((,var (cdr (assoc ,(car keys) ,var :test ',(car tests)))))
              ,(io-lookup-fn var (cdr keys) (cdr tests))))))

(defmacro io-lookup (var tests &rest keys)

; This is a convenient interface to io-lookup-fn.

  (declare (xargs :guard (or (member-eq tests '(equal eq eql))
                             (and (true-listp tests)
                                  (equal (length tests) (length keys))
                                  (subsetp-eq tests '(equal eq eql))))))
  (io-lookup-fn var
                keys
                (if (atom tests)
                    (make-list (length keys) :initial-element tests)
                  tests)))

(defun io-pairs-add-input (input lst)
  (cond ((endp lst) nil)
        (t (b* (((cons (list inputs result) rest)
                 lst))
             (cons (list (cons input inputs) result)
                   (io-pairs-add-input input rest))))))

(mutual-recursion

(defun get-io-pairs-fn2-lst (formals lst mvp)
  (cond ((endp lst) nil)
        (t (append (get-io-pairs-fn2 formals (car lst) mvp)
                   (get-io-pairs-fn2-lst formals (cdr lst) mvp)))))

(defun get-io-pairs-fn2 (formals x mvp)

; See io-pairs-table for a discussion of io-lookup tables.

; X is an io-lookup table entry, which is just a result if formals is nil and
; otherwise is an input consed onto a list of entries.  We return a list of
; io-doublets.

  (cond ((null formals) (list (list nil (if mvp (cons 'mv x) x))))
        (t (io-pairs-add-input
            (car x)
            (get-io-pairs-fn2-lst (cdr formals) (cdr x) mvp)))))
)

(defun get-io-pairs-fn1 (fns tbl wrld)
  (cond ((endp fns) nil)
        (t (append (let ((fn (car fns)))
                     (io-pairs-add-input fn
                                         (get-io-pairs-fn2-lst
                                          (formals fn wrld)
                                          (cdr (assoc-eq fn tbl))
                                          (consp (cdr (stobjs-out fn wrld))))))
                   (get-io-pairs-fn1 (cdr fns) tbl wrld)))))

(defun get-io-pairs-fn (fns wrld warnp)

; To see how this works, see the comment in get-io-pairs-fn2 and try running
; get-io-pairs after evaluating the following.

; (trace$ get-io-pairs-fn2 get-io-pairs-fn2-lst get-io-pairs-fn1)

  (b* ((tbl (table-alist 'io-pairs-table wrld))
       (tbl-fns (strip-cars tbl))
       (allp (equal fns '(:all)))
       (bad (and (not allp)
                 (set-difference-eq fns tbl-fns)))
       (fns (cond (allp tbl-fns)
                  (bad (intersection-eq fns tbl-fns))
                  (t fns)))
       (- (and bad
               warnp
               (warning$-cw 'get-io-pairs
                            "There ~#0~[is no I/O pair for the symbol~/are no ~
                             I/O pairs for the symbols~] ~&0."
                            bad))))
    (get-io-pairs-fn1 fns tbl wrld)))

(defmacro get-io-pairs (&rest fns)
  (declare (xargs :guard (symbol-listp fns)))
  (if (and (member-eq :all fns)
           (not (equal fns '(:all))))
      '(er soft 'get-io-pairs
           "It is illegal to use :ALL with ~x0 except in the form ~x1."
           'get-io-pairs
           '(get-io-pairs :all))
    `(get-io-pairs-fn ',fns (w state) t)))

(defun maybe-kwote-lst (x)
  (declare (xargs :guard (true-listp x) :mode :logic))
  (cond ((endp x) nil)
        (t (cons (maybe-kwote (car x))
                 (maybe-kwote-lst (cdr x))))))

(defun show-io-pairs-lst (pairs chan wrld state)
  (cond ((endp pairs) (newline chan state))
        (t (pprogn (b* ((pair (car pairs))
                        (fn/inputs (car pair))
                        (fn (car fn/inputs))
                        (inputs (cdr fn/inputs))
                        (result (cadr pair))
                        (mvp (cdr (stobjs-out fn wrld)))
                        (qinputs (maybe-kwote-lst inputs))
                        (qresult
                         (if mvp
                             (assert$
                              (eq (car result) 'mv)
                              (cons 'mv (maybe-kwote-lst (cdr result))))
                           (maybe-kwote result)))
                        (io-pair `((,fn ,@qinputs) ,qresult)))
                     (fms "~x0" (list (cons #\0 io-pair)) chan state nil))
                   (show-io-pairs-lst (cdr pairs) chan wrld state)))))

(defun show-io-pairs-fn (fns state)
  (b* (((when (and (member-eq :all fns)
                   (not (equal fns '(:all)))))
        (er soft 'show-io-pairs
            "It is illegal to use :ALL with ~x0 except in the form ~x1."
            'show-io-pairs
            '(show-io-pairs :all)))
       (wrld (w state))
       (chan (standard-co state))
       (allp (equal fns '(:all)))
       (pairs (get-io-pairs-fn (or fns '(:all)) wrld nil)))
    (pprogn
     (cond
      ((null pairs)
       (fms "There are no verified I/O pairs to display~#0~[~/ for the symbol ~
             ~v1~/ for any of the symbols ~v1~].~|"
            (list (cons #\0 (zero-one-or-more (and (not allp) fns)))
                  (cons #\1 (and (not allp) fns)))
            chan state nil))
      (t (pprogn (fms "Verified I/O pairs ((fn arg1 .. argn) result):~|"
                      nil chan state nil)
                 (show-io-pairs-lst pairs chan wrld state))))
     (value :invisible))))

(defmacro show-io-pairs (&rest fns)
  (declare (xargs :guard (symbol-listp fns)))
  `(show-io-pairs-fn ',fns state))

(defun simple-trans-eval-lst (lst i call ctx wrld state)
  (b* (((when (endp lst)) (value nil))
       (term (car lst))
       ((er (cons ?tterm val))
        (simple-translate-and-eval term
                                   nil ; alist
                                   nil ; ok-stobj-names
                                   (msg "The ~n0 argument of the call ~x1"
                                        (list i) call)
                                   ctx wrld state t))
       ((er rest)
        (simple-trans-eval-lst (cdr lst) (1+ i) call ctx wrld state)))
    (value (cons val rest))))

(defun add-io-pairs-translate-tuples-1 (tuples fn arity-in stobjs-out
                                               ctx wrld state)

; In the non-error case, the value of the returned error triple is a list of
; io-doublet pairs for fn, each of the form (inputs output), where the length
; of inputs is the input arity of fn, arity-in, and if fn returns multiple
; values then output is a true-list of non-stobjs values whose length is the
; length of stobjs-out.

  (b* (((when (null tuples))
        (value nil))
       (tuple (car tuples))
       ((when (not (and (consp tuple)
                        (consp (car tuple))
                        (consp (cdr tuple))
                        (null (cddr tuple)))))
        (er soft ctx
            "An I/O tuple must be of the form ((fn x1 ... xk) result), but ~
             the following is not of that form:~|~x0"
            tuple))
       ((list (cons fn2 actuals) result) tuple)
       ((when (not (eq fn2 fn)))
        (er soft ctx
            "It is illegal to specify more than one function symbol in a call ~
             of add-io-pairs, but both ~x0 and ~x1 were specified."
            fn fn2))
       ((when (not (= (length actuals) arity-in)))
        (er soft ctx
            "The I/O pair ~x0 specifies ~x1 inputs, but the function symbol ~
             ~x2 expects ~x3 inputs."
            tuple (length actuals) fn arity-in))
       ((er inputs)
        (simple-trans-eval-lst actuals 1 (cons fn actuals) ctx wrld state))
       ((er -)

; We translate result before evaluating (even though trans-eval will translate
; it again), to check that state and user-defined stobjs will not be modified
; by its evaluation.  (This could be overkill, but it seems reasonable to
; prevent users from causing a state change even upon failure when calling
; add-io-pairs.)  We translate just as trans-eval does.

        (b* (((mv erp ?trans bindings state)
              (translate1 result
                          :stobjs-out '((:stobjs-out . :stobjs-out))
                          t
                          ctx wrld state))
             ((when erp) ; error msg presumably has already been printed
              (silent-error state))
             (result-stobjs-out (translate-deref :stobjs-out bindings))
             ((when (not (equal stobjs-out result-stobjs-out)))
              (er soft ctx
                  "The I/O pair ~x0 specifies a return of ~x1 value~#2~[~/s~] ~
                   but the function ~x3 returns ~x4 value~#5~[~/s~]."
                  tuple
                  (length result-stobjs-out)
                  result-stobjs-out
                  fn
                  (length stobjs-out)
                  stobjs-out)))
          (value nil)))
       ((er (cons ? output)) (trans-eval result ctx state t))
       (io-doublet (list inputs output))
       ((er io-doublet-lst)
        (add-io-pairs-translate-tuples-1 (cdr tuples) fn arity-in stobjs-out
                                         ctx wrld state)))
    (value (cons io-doublet io-doublet-lst))))

(defun add-io-pairs-translate-tuples (tuples ctx wrld state)
  (declare (xargs :guard tuples)) ; not nil
  (cond
   ((not (and (alistp tuples)
              (alistp (strip-cars tuples))))
    (er soft ctx
        "The first argument of add-io-pairs must be a true list of pairs of ~
         the form ((fn arg1 ... argk) result).  The argument ~x0 is thus ~
         illegal."
        tuples))
   ((mbt (consp tuples))
    (b* ((tuple (car tuples))
         (fn (caar tuple))
         ((when (not (and (symbolp fn)
                          (function-symbolp fn wrld)
                          (eq (symbol-class fn wrld)
                              :common-lisp-compliant))))
          (er soft ctx "Not a guard-verified function symbol: ~x0" fn))
         (stobjs-in (stobjs-in fn wrld))
         (arity-in (length stobjs-in))
         ((when (member-eq fn *stobjs-out-invalid*))
          (er soft ctx
              "It is illegal to add I/O pairs for the function symbol ~x0."
              fn))
         (stobjs-out (stobjs-out fn wrld))
         (stobjs (union-eq (remove-eq nil stobjs-in)
                           (remove-eq nil stobjs-out)))
         ((when stobjs)
          (er soft ctx
              "It is illegal to call add-io-pairs for the function symbol ~
               ~x0, because it traffics in the stobj~#1~[~/s~] ~x1."
              fn
              stobjs)))
      (with-guard-checking-error-triple
       nil ; reflects in the loop the guard-checking done during certify-book
       (add-io-pairs-translate-tuples-1 tuples fn arity-in stobjs-out
                                        ctx wrld state))))
   (t ; presumably unreachable; see the mbt call above
    (prog2$ (er hard ctx
                "Implementation error: Impossible case!")
            (value nil)))))

(defun add-io-pairs-dcls (fn wrld)

; Much of this code is based on that of ACL2 source function
; guard-raw.

  (declare (xargs :mode :program))
  (cons '(declare (xargs :verify-guards t))
        (let* ((ev (get-event fn wrld))
               (def ; strip off leading defun
                (case (car ev)
                  (defun (cdr ev))
                  (mutual-recursion (assoc-eq fn (strip-cdrs (cdr ev))))
                  (verify-termination-boot-strap
; For some functions, like apply$, we wind up in this case.
                   (cdr (cltl-def-from-name fn wrld)))
                  (otherwise ; surprising case; just declare the guard
                   `(declare (xargs :guard ,(guard fn nil wrld)))))))
          (butlast (cddr def) 1))))

(defun formal-mv (n expr i vars bindings)

; Turn an expression that represents a list of length n into a corresponding mv
; expression, in linear time.  I, vars, and bindings are accumulators that are
; initially 0, nil, and nil, respectively.  For example, the value of
; (formal-mv 3 ''(a b c) 0 nil nil) is:

;   (let* ((x0 '(a b c))
;          (a0 (car x0))
;          (x1 (cdr x0))
;          (a1 (car x1))
;          (x2 (cdr x1))
;          (a2 (car x2)))
;         (mv a0 a1 a2))

  (cond ((zp n)
         (list 'let* (reverse bindings) `(mv ,@(reverse vars))))
        (t (let* ((xi (packn (list 'x i)))
                  (xi-binding (list xi expr))
                  (ai (packn (list 'a i)))
                  (ai-binding (list ai (list 'car xi)))
                  (next-expr (list 'cdr xi)))
             (formal-mv (1- n) next-expr (1+ i)
                        (cons ai vars)
                        (list* ai-binding xi-binding bindings))))))

(defun push-io-pairs-lenience-fn (fns)
  (cond
   ((endp fns) nil)
   (t
    (cons `(table io-pairs-lenience-table
                  ',(car fns)
                  (cons nil
                        (cdr (assoc-eq ',(car fns)
                                       (table-alist 'io-pairs-lenience-table
                                                    world)))))
          (push-io-pairs-lenience-fn (cdr fns))))))

(defmacro push-io-pairs-lenience (&rest fns)
  (cons 'progn (push-io-pairs-lenience-fn fns)))

(defun pop-io-pairs-lenience-fn (fns)
  (cond
   ((endp fns) nil)
   (t
    (cons `(table io-pairs-lenience-table
                  ',(car fns)
                  (cdr (cdr (assoc-eq ',(car fns)
                                      (table-alist 'io-pairs-lenience-table
                                                   world)))))
          (pop-io-pairs-lenience-fn (cdr fns))))))

(defmacro pop-io-pairs-lenience (&rest fns)
  (cons 'progn (pop-io-pairs-lenience-fn fns)))

(defun check-io-pairs-lenience-fn (fn old-entry caller state)
  (b* ((wrld (w state))
       (lenience (cdr (assoc-eq fn (table-alist 'io-pairs-lenience-table
                                                wrld))))
       ((when lenience)
        (value '(value-triple :invisible)))
       (current-entry
        (cdr (assoc-eq fn (table-alist 'io-pairs-table wrld))))
       (ctx caller)
       ((when (not (equal old-entry current-entry)))
        (b* ((book (car (global-val 'include-book-path wrld)))
             (str  "ACL2 is encountering a call of ~x0 on function symbol ~
                    ~#2~[~x1 while attempting to include the book ~
                    ~x3.~|~/~x1.  ~]But the existing list of I/O pairs for ~
                    ~x1 is different from ~@4.  See :DOC merge-io-pairs for ~
                    how to avoid this ~@5.")
             (num2 (if book 0 1))
             (str4 (if book
                       "when that book was being certified"
                     "what it was previously at that point (perhaps during ~
                      the first pass of an encapsulate event)")))
          (with-output!
            :on error
            (er soft ctx str
                caller
                fn
                num2
                book
                str4
                "error")))))
    (value '(value-triple :invisible))))

(defmacro check-io-pairs-lenience (fn old-entry caller)
  `(make-event
    (check-io-pairs-lenience-fn ',fn ',old-entry ',caller state)
    :check-expansion t
    :on-behalf-of :quiet!))

(defun add-io-pairs-events (fn io-doublet-lst hints debug test wrld)

; Fn is a guard-verified function symbol in wrld that does not traffic in state
; or stobjs.  Io-doublet-lst is a list of pairs (inputs . output) as returned by
; add-io-pairs-translate-tuples, and hence respects the signature of fn: inputs
; has the same length as the stobjs-in of fn, and if the stobjs-out of fn is
; other than (nil) then it has the same length as output.

; The calls of check-sum-obj create suffices that we hope are unique, thus
; avoiding name conflicts from repeated calls of add-io-pairs.  To see why we
; use the max-absolute-event-number in the checksums, see the example in
; community book books/std/util/add-io-pairs-tests.lisp that includes a comment
; about "absolute-event-number".

; We allow io-doublet-lst to be :skip, in which case the table event is skipped
; and we use the existing table entry -- thus supporting install-io-pairs.

  (b* ((old-entry (cdr (assoc-eq fn (table-alist 'io-pairs-table wrld))))
       (new-entry (if (eq io-doublet-lst :skip) ; for install-io-pairs
                      old-entry
                    (update-io-lookup-lst io-doublet-lst old-entry)))
       (sum (check-sum-obj new-entry))
       (max (max-absolute-event-number wrld))
       (suffix1 (check-sum-obj (list* 'defthm fn sum max)))
       (thm-name (add-suffix fn (coerce (explode-atom suffix1 10) 'string)))
       (suffix2 (check-sum-obj (list* 'defun fn sum max)))
       (new-fn (add-suffix fn (coerce (explode-atom suffix2 10) 'string)))
       (formals (formals fn wrld))
       (io-lookup-var (genvar fn "IO-LOOKUP-VAR" 0 formals))
       (lookup-result0 `(car ,io-lookup-var))
       (stobjs-out (stobjs-out fn wrld))
       (lookup-result (if (cdr stobjs-out)
                          (formal-mv (length stobjs-out)
                                     lookup-result0
                                     0 nil nil)
                        lookup-result0)))
    `((check-io-pairs-lenience ,fn
                               ,old-entry
                               ,(if (eq io-doublet-lst :skip)
                                    'install-io-pairs
                                  'add-io-pairs))
      ,@(and (not (eq io-doublet-lst :skip))
             `((table io-pairs-table ',fn
                      (let ((old-entry
                             (cdr (assoc-eq ',fn (table-alist 'io-pairs-table
                                                              world)))))
                        (update-io-lookup-lst ',io-doublet-lst old-entry)))))
      (defun ,new-fn ,formals
        ,@(add-io-pairs-dcls fn wrld)
        (let* ((,io-lookup-var ',new-entry)
               (,io-lookup-var (io-lookup ,io-lookup-var ,test ,@formals)))
          (if ,io-lookup-var
              ,(if debug
                   `(prog2$
                     (cw "; DEBUG: Found io-pair for input list ~x0.~|"
                         (list ,@formals))
                     ,lookup-result)
                 lookup-result)
            (,fn ,@formals))))
      (defthm ,thm-name
        (equal (,fn ,@formals)
               (,new-fn ,@formals))
        ,@(and hints `(:hints ,hints))
        :rule-classes nil)
      (unmemoize ',fn)
      (memoize ',fn :invoke ',new-fn))))

(defmacro add-io-pairs (tuples &key hints debug (test 'equal) verbose)

; Keep this in sync with install-io-pairs.

  (let ((form `(b* ((tuples ',tuples)
                    (hints ',hints)
                    (debug ',debug)
                    (test ',test)
                    (wrld (w state))
                    ((when (null tuples))
                     (value '(value-triple :empty-io-pairs)))
                    (ctx 'add-io-pairs)
                    ((er io-doublet-lst)
                     (add-io-pairs-translate-tuples tuples ctx wrld state))
                    (fn (caar (car tuples)))
                    (events (add-io-pairs-events fn io-doublet-lst
                                                 hints debug test wrld)))
                 (value (cons 'progn events)))))
    (cond (verbose `(make-event ,form))
          (t `(with-output :off :all :on error :gag-mode nil
                (make-event ,form
                            :on-behalf-of :quiet!))))))
                
(defun remove-assoc-eq-lst (lst alist)
  (declare (xargs :guard (if (symbol-listp lst)
                             (alistp alist)
                           (symbol-alistp alist))))
  (if (atom lst)
      alist
    (remove-assoc-eq-lst (cdr lst)
                         (remove-assoc-eq (car lst) alist))))

(defun remove-io-pairs-event (fns ctx state)
  (b* (((when (null fns))
        (er soft ctx
            "~x0 requires at least one argument.  Perhaps you intended ~x1."
            'remove-io-pairs
            '(remove-io-pairs :all)))
       ((when (and (member-eq :all fns)
                   (not (equal fns '(:all)))))
        (er soft 'show-io-pairs
            "It is illegal to use :ALL with ~x0 except in the form ~x1."
            'remove-io-pairs
            '(remove-io-pairs :all)))
       (wrld (w state))
       (tbl (table-alist 'io-pairs-table wrld))
       (tbl-fns (strip-cars tbl))
       (allp (equal fns '(:all)))
       (bad (and (not allp)
                 (set-difference-eq fns tbl-fns)))
       (fns (cond (allp tbl-fns)
                  (bad (intersection-eq fns tbl-fns))
                  (t fns)))
       ((er -) (if bad
                   (with-output!
                     :stack :pop
                     (pprogn
                      (warning$ ctx "Add-io-pairs"
                                "There ~#0~[is no I/O pair for the ~
                                 symbol~/are no I/O pairs for the symbols~] ~
                                 ~&0."
                                bad)
                      (value nil)))
                 (value nil))))
    (value `(progn ,@(pairlis-x1 'unmemoize (pairlis$ (kwote-lst fns) nil))
                   (table io-pairs-table nil
                          (remove-assoc-eq-lst ',fns
                                               (table-alist 'io-pairs-table
                                                            world))
                          :clear)))))

(defmacro remove-io-pairs (&rest fns)
  (declare (xargs :guard (symbol-listp fns)))
  `(with-output
     :stack :push ; for warning$-cw call in remove-io-pairs-event
     :off :all :on error :gag-mode nil
     (make-event (remove-io-pairs-event ',fns 'remove-io-pairs state)
                 :on-behalf-of :quiet!)))

(defmacro install-io-pairs (fn &key hints debug (test 'equal) verbose)

; Keep this in sync with add-io-pairs.

  (let ((form `(b* ((fn ',fn)
                    (hints ',hints)
                    (debug ',debug)
                    (test ',test)
                    (wrld (w state))
                    (io-doublet-lst :skip)
                    (events (add-io-pairs-events fn io-doublet-lst
                                                 hints debug test wrld)))
                 (value (cons 'progn events)))))
    (cond (verbose `(make-event ,form))
          (t `(with-output :off :all :on error :gag-mode nil
                (make-event ,form
                            :on-behalf-of :quiet!))))))

(defmacro deinstall-io-pairs (fn)
  `(unmemoize ',fn))

(defun merge-io-pairs-fn (fns events)
  (declare (xargs :guard (and (symbol-listp fns)
                              (true-listp events))))
  `(progn (push-io-pairs-lenience ,@fns)
          ,@events
          ,@(pairlis-x1 'install-io-pairs
                        (pairlis-x2 fns nil))
          (pop-io-pairs-lenience ,@fns)))

(defmacro merge-io-pairs (x &rest events)
  (declare (xargs :guard (or (symbolp x)
                             (and (symbol-listp x)
                                  (no-duplicatesp-eq x)))))
  (merge-io-pairs-fn (if (symbolp x) (list x) x) events))
