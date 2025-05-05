; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann and J Strother Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc whats-new-in-acl2-2025
  :parents (note-8-6 note-8-7)
  :short "Notes for &ldquo;What's New in ACL2&rdquo; at ACL2 Workshop 5/12/2025"
  :long "<p>These release notes are derived from documentation topics @(see
 note-8-6) and @(see note-8-7) that were added between the November 2023 and
 May 2025 ACL2 Workshops.  Each release note included below is included in its
 entirety, with <color rgb='#0090f0'>this color</color> providing emphasis and
 <color rgb='#ff00ff'>this color</color> used for text that has been added.</p>

 <h3>Part 1 (Matt Kaufmann)</h3>

 <color rgb='#0090f0'>
 <p>In @(see gag-mode) (which is on by default), when the prover notes that a
 forcing round is pending, it now lists the names of the rules that are
 responsible.</p>
 </color>

 <color rgb='#ff00ff'><p>Example:</p></color>
 @({
 Forcing Round 1 is pending (caused first by applying ACL2P-IS-ACL2
 and ZMIRROR-IS-MIRROR to Goal).
 })

 <p><color rgb='#0090f0'>ACL2 versions of Lisp &lsquo;fixnum&rsquo; notions have been made more
 generous.</color>  Specifically, the value of @('*fixnum-bits*') has been increased
 from 30 to 61, which has increased the value of @('(fixnum-bound)') from
 2^29-1 to 2^60-1.  Thanks to Eric Smith for requesting an increase.  One
 effect of this change is to increase the value of @('*default-step-limit*')
 accordingly, so that the steps computed by @(see with-prover-step-limit) will
 no longer be limited to fewer than 2^29.

 <blockquote>

 <b>NOTE</b>.  The previous such &ldquo;fixnum&rdquo; behavior can be obtained
 by building ACL2 with environment variable @('ACL2_SMALL_FIXNUMS') set to a
 non-empty value.  In fact, such a setting is necessary for a 32-bit Lisp such
 as CMUCL.  However, such ACL2 builds are not as fully tested as the usual
 builds and thus may be less reliable, and they are not guaranteed to work
 compatibly with ordinary ACL2 builds on the same set of books.

 </blockquote></p>

 <p><color rgb='#ff00ff'>Similarly increased the maximum lengths of
 arrays:</color></p>

 <p>Changed the bound @('*maximum-positive-32-bit-integer*') that was used for
 array lengths (and eliminated that constant), replacing it by the larger value
 from macro call @('(array-maximum-length-bound)'), which is the same as
 @('(fixnum-bound)'), i.e., @(`(fixnum-bound)`).  Thanks to Eric Smith for
 suggesting that we consider such a change and for updating books under
 @('books/kestrel/').  Note: For CMUCL (or any 32-bit Lisp) the bound has
 actually decreased, since @('(fixnum-bound)') is @('2^30-1') in that case.</p>

 <color rgb='#0090f0'>
 <p>The @(see guard)s for functions that operate on characters or strings
 sometimes insisted that the inputs contain only standard characters.  That
 restriction has been lifted, and the definitions of @(tsee alpha-char-p),
 @(tsee upper-case-p), @(tsee lower-case-p), @(tsee char-downcase), and @(tsee
 char-upcase) have been adjusted to handle non-standard characters.</p>
 </color>

 <p><color rgb='#0090f0'>The message for evaluation failures during proofs has been modified
 slightly</color>, clarifying the case of substitution and, especially, suggesting
 :DOC @(see comment) for explanations (which has been updated accordingly).
 Thanks to David Russinoff for an acl2-help list query leading to this
 improvement.</p>

 <color rgb='#ff00ff'><p>Example:</p></color>
 @({
 (defstub f (x) t)
 (defund g (x) (f x))
 (thm (equal (g 3) y))

 *** Key checkpoint at the top level: ***

 Goal'
 (EQUAL
  (HIDE
    (COMMENT \"Failed attempt to call constrained function F;
 see :DOC comment\"
             (G 3)))
  Y)
 })

 <p><color rgb='#0090f0'>ACL2 now supports floating-point operations.  See @(see df).</color>  Regarding
 this new feature: Release was approved by DARPA with &ldquo;DISTRIBUTION
 STATEMENT A. Approved for public release. Distribution is unlimited.&rdquo;
 Note for system programmers: the new <i>df expressions</i> affect translation
 as well as stobjs-in and stobjs-out; see @(see system-utilities), specifically
 discussion mentioning &ldquo;df&rdquo;.  Thanks to Warren Hunt for his
 encouragement and support in this effort, towards ACL2 usage in scientific
 computations.</p>

 <color rgb='#ff00ff'><p>The next item supports <tt>:element-type
 t</tt>.</p></color>
 @({
 (defstobj st1
   (ar1 :type (array double-float (*ar-size*))
        :element-type t ; possibly faster execution but more space
        :initially 0)
   ;; optional:
   :inline t)
 })

 <p>A new @(see stobj) field keyword, @(':element-type'), is legal for an array
 field.  It specifies the raw Lisp element type of the array.  Its value can be
 the element type specified by the value of the @(':type') for that array
 field.  That is the default value, and the other legal value is @('t'), but
 these may change in the future.  See @(see defstobj) and see @(see
 defstobj-element-type).</p>

 <p><color rgb='#0090f0'>Now @(tsee defabsstobj) accepts the @(':non-executable') keyword, in
 analogy to support for that keyword by defstobj.</color>  Thanks to Yahya Sohail and
 Warren Hunt for discussions leading to this enhancement.</p>

 <p><color rgb='#0090f0'>New functions @(tsee add-global-stobj) and @(tsee remove-global-stobj)
 change whether there is a global (&ldquo;live&rdquo;) stobj for a given stobj
 name, thus modifying the effect of the keyword @(':non-executable') of events
 @(tsee defstobj) and @(tsee defabsstobj).</color>  Thanks to Yahya Sohail and Warren
 Hunt for discussions leading to the addition of these utilities.</p>

 <p><color rgb='#0090f0'>A new @(tsee defabsstobj) keyword, @(':attachable'), allows a single
 abstract @(see stobj) to have more than one foundation and associated
 functions for execution, without the need to recertify the book that
 introduces the stobj.</color>  See @(tsee attach-stobj).  Thanks to Warren Hunt and
 Yahya Sohail for requesting this feature.  We thank Sol Swords, Warren, and
 especially Yahya for helpful input on its high-level design.</p>

 <color rgb='#ff00ff'>
 <p>The next item mentions @(see defattach-system).  We may look at that topic
 and follow links from it to @(see system-attachments) and @(see
 efficiency).</p>
 </color>

 <p>The ACL2 @(see type-reasoning) mechanism has been strengthened slightly for
 an @('if') expression being assumed true or false, when that expression has a
 subterm of the form @('(equal term 'c)'), or @('(equal 'c term)') and @('c')
 is @('0'), @('1'), @('t'), or @('nil').  Thanks to Warren Hunt for sending an
 example involving @(see forward-chaining) that led to this improvement.
 <b>IMPORTANT NOTE:</b> If this change causes a proof to fail that formerly
 succeeded, you can fix it by preceding it with the following (implicitly @(see
 local)) event.</p>

 @({
 (defattach-system use-enhanced-recognizer constant-nil-function-arity-0)
 })

 <color rgb='#ff00ff'>
 <p>The next item is quite technical but can be important
 for efficiency.  It's an example of the maturation of ACL2 for
 industrial-strength usage.</p>
 </color>

 <p><color rgb='#0090f0'>For a book's event of the form @('(defconst *NAME* (quote VAL))') that
 results from @(tsee make-event) expansion, @('VAL') is no longer duplicated
 between that book's @(see certificate) file and its compiled file.</color>  Thanks to
 Sol Swords for requesting this enhancement.  This lack of duplication also
 applies to any such @('defconst') event in a book that is in the scope of a
 @(tsee progn) or @(tsee encapsulate) event when there is at most one
 @('make-event') call in that scope; similarly for such @('defconst') events
 within calls of @(tsee skip-proofs), @(tsee with-output), @(tsee
 with-guard-checking), or @(tsee with-prover-step-limit).</p>

 <p><color rgb='#0090f0'>Modifications have been made that allow ACL2 to be hosted on GCL Version
 2.7.0 and presumably later @(see GCL) versions; previously only GCL versions
 before 2.7.0 could host ACL2.</color>  Essentially the only user-visible change (other
 than error prevention) is the introduction of @(tsee list$), a macro
 equivalent to @(tsee list) that can be used without a GCL 2.7.0 restriction on
 the number of arguments.  The most sweeping implementation-level change is the
 replacement of an array in support of so-called <i>static honses</i>, the
 <i>sbits array</i>, by a structure that avoids a reduced bound on array
 dimensions imposed by GCL 2.7.0.  Details may be found in a Lisp comment in
 the form @('(defxdoc note-8-7 ...)') in @(see community-books) file
 @('books/system/doc/acl2-doc.lisp').  Thanks to Camm Maguire for his help with
 this project, including (but by no means limited to) his contribution of a new
 sbits implementation.</p>

 <h3>Part 2 (J Moore)</h3>

 <p><color rgb='#0090f0'>The @(see break-rewrite) facility will now cause an interactive break on a
 monitored rewrite rule if the rule's equivalence relation fails to refine any
 of the equivalence relations known to be permitted while rewriting the target.</color>
 See @(see geneqv) for a discussion of how @(see congruence) rules are used to
 compute permitted equivalence relations and @(see refinement-failure) for
 advice about how to investigate and fix refinement failures during
 rewriting.</p>

 <p><color rgb='#0090f0'>The new documentation topic, @(see induction-coarse-v-fine-grained),
 discusses how appropriately setting ruler-extenders can sometimes improve the
 induction scheme suggested by a recursive function, especially one involving
 @(tsee let) and @(tsee let*) bindings containing conditional recursive calls.</color>
 For that new topic, new related books <color rgb='#0090f0'><tt>books/demos/ppr1-experiments.lisp</tt></color>
 and @('books/demos/ppr1-experiments-thm-1-ppr1.lisp'), and related edits of
 existing :DOC topics (@(see advanced-features), @(see definductor), @(see
 defun), @(see induction), @(see rulers), @(see verify-termination), and @(see
 xargs)): Release was approved by DARPA with &ldquo;DISTRIBUTION STATEMENT
 A. Approved for public release. Distribution is unlimited.&rdquo;</p>

 <color rgb='#ff00ff'><p>Example: The @('ppr1-experiments.lisp') mentioned
 above summarizes coarse and fine schemes generated for the system function
 ppr1.</p></color>
 @({
 (assert-event ; proof time: 2165.19 seconds
  (equal (about-imach 'coarse-induction-scheme (w state))
         '(76       ;; 76 cases in the induction scheme
           (0 . 6)  ;; no induction hyps in 6 cases, i.e., Base Cases
           (1 . 8)  ;; 1 induction hyp in 8 cases
           (2 . 2)  ;; 2 induction hyps in 2 cases
           (3 . 16) ;; ...
           (4 . 32)
           (8 . 4)
           (9 . 8)  ;; 9 induction hyps in 8 cases
           )))

 (assert-event ; proof time: 65.00 seconds
  (equal (about-imach 'fine-induction-scheme (w state))
         '(256      ;; 256 cases in the induction scheme
           (0 . 6)  ;; no induction hyps in 6 cases, i.e., Base Cases
           (1 . 8)  ;; 1 induction hyp in 8 cases
           (2 . 82) ;; 2 induction hyps in 82 cases
           (3 . 80) ;; 3 induction hyps in 80 cases
           (4 . 80) ;; 4 induction hyps in 80 cases
           )))
 })

 <color rgb='#0090f0'>
 <p>A new @('brr') command, @(':')@(tsee explain-near-miss), when issued in a
 break caused by a near miss, will try to pinpoint how the rule's pattern
 failed to match the current target.</p>
 </color>

 <color rgb='#0090f0'>
 <p>A new utility, @(tsee compare-objects), highlights the differences between
 two @('cons')-trees.</p>
 </color>

 <color rgb='#ff00ff'><p>Example:</p></color>
 @({
 ACL2 !>(compare-objects '(f x y (g x '(a b c)))
                         '(f y x (g x '(a b c . d))))
 ((:OBJ (F :|<s1>|
           :|<s2>|
           (G X '(A B C . :|<s3>|))))
  (:LEGEND ((:|<s1>| X Y)
            (:|<s2>| Y X)
            (:|<s3>| NIL D))))
 })

 <color rgb='#0090f0'>
 <p>A new documentation topic and its subtopics describe uses of ACL2 and its
 predecessor, Nqthm, in modeling state machines.  See @(see
 operational-semantics), which notes that others are welcome to add to these
 topics; see the discussion of &ldquo;Request for Suggestions from ACL2
 Users&rdquo;.  The new topic incorporates an annotated bibliography pointing
 to more than 40 topics in a new @('\"BIB\"') package.</p>
 </color>

 <color rgb='#ff00ff'><p>This is a massive new topic, comprising about 100 kB
 of text in about 2,300 lines.  We wrote it to &ldquo;put our stake in the
 ground&rdquo; regarding the mechanization of operational semantics.  It
 includes an annotated bibliography that lists papers by many ACL2 users.  If
 you think a paper is missing, please add it or <a
 href='mailto:jstrothermoore@gmail.com'>email me</a>!</p></color>

 <color rgb='#ff00ff'><p>There were several tweaks to @(tsee do$).  If you use
 @('DO') @('loop$') (see @(see do-loop$)) or if you have lemmas that explicitly
 mention @('do$') and you experience translation errors, you'll want to pay
 attention to the revised documentation.</p></color>

 <p>The fifth formal of @(tsee do$) now represents the values returned rather
 than a default value.  This change supports a bug fix; see the item below
 regarding &ldquo;About a bug in DO$ in ACL2 Version  8.5&rdquo;.</p>

 <p>The sixth and seventh arguments of @(tsee do$) have been combined into a
 record that also contains a list of the names of all the @(tsee stobj)s in the
 @('DO') @('loop$').  In the new record, the measure term is stored in
 untranslated form.  The record is only used in the hard error produced when
 the evaluation of a @('DO$') term fails to terminate and is not relevant to
 the logical value of the @('DO$') term.</p>

 <p>Fixed a bug in handling of @(tsee do-loop$) expressions that return
 multiple values, when encountered during proofs.  An example labeled with
 &ldquo;Version 8.5&rdquo; is near the end of @(see community-book)
 @('projects/apply/loop-tests.lisp').</p>

 <p>A bug in @(tsee do$), hence in @(tsee do-loop$) expressions, was that
 single-threadedness (for @(see stobj)-based computations) can be violated when
 a loop terminates prematurely because the measure fails to decrease.  The bug,
 which has been fixed, is explained in detail in a comment in ACL2 source file
 @('apply.lisp'), entitled &ldquo;About a bug in DO$ in ACL2
 Version  8.5&rdquo;.</p>

 <p>Fixed a bug that could cause an implementation error during a proof, when
 printing a term with a @(tsee do$) call.  (The bug was in untranslating
 certain applications of @(tsee nth), @(tsee update-nth), or @(tsee
 update-nth-array) during a proof.)</p>

 ")
