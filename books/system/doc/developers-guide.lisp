; ACL2 Developer's Guide
; Copyright (C) 2018, Regents of the University of Texas
; Initial version written by Matt Kaufmann and J Strother Moore

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc developers-guide
  :parents (programming)
  :short "Guide for ACL2 developers"
  :long "<p>This guide is <b>NOT</b> intended for the full ACL2 user community.
 Rather, it is intended for <i>experienced</i> ACL2 users who may wish to
 become ACL2 <i>developers</i>, that is, to contribute to the maintenance and
 enhancement of the ACL2 source code.  Don't waste your time here unless you're
 an ACL2 developer, or intending to become one!</p>

 <p>ACL2 is maintained solely by Matt Kaufmann and J Moore, although for some
 time they have occasionally vetted code written by others, ultimately
 incorporating it into the system.  Although this is anticipated to remain the
 case for some time, a process is underway towards gradually turning
 maintenance over to some other small group of trusted, reliable, responsible
 people.  This guide was motivated by the desire to begin to support the
 eventual development of such a group.</p>

 <p>(Of course, given the permissive license of ACL2, anyone is allowed to
 modify a copy of its source code.  Here we are talking about what is generally
 called ``ACL2'', which is distributed from github and from the University of
 Texas at Austin.)</p>

 <p>The first step towards contributing to ACL2 development is to join the
 @('acl2-devel') mailing list by <a
 href='mailto:kaufmann@cs.utexas.edu'>emailing Matt Kaufmann</a> with a request
 to be added.</p>

 <p>The website for the (first) Developer's Workshop has quite a bit of useful
 information.  It is at: <code><a
 href='http://www.cs.utexas.edu/users/moore/acl2/workshop-devel-2017/'>http://www.cs.utexas.edu/users/moore/acl2/workshop-devel-2017/</a></code></p>

 <p>Note that for the second Developer's Workshop, some colors were added to
 this Guide to help guide the discussion.  (Colors show up in the web version
 but not in the @(see acl2-doc) browser.)  This <color rgb='#c00000'>red
 color</color> highlights passages that were to be given some emphasis.  Also,
 in some cases there is a note of the following form, for use in the
 workshop:</p>

 <color rgb='#800080'><p>[...SOME NOTE FOR THE WORKSHOP...]</p></color>

 <color rgb='#c00000'>
 <p>For a small list of potential ACL2 development tasks, see community books
 file <a
 href='https://github.com/acl2/acl2/blob/master/books/system/to-do.txt'>@('books/system/to-do.txt')</a>.
 If you decide to work on one of these tasks, please make a note (just below
 the one-line header at the top of the tasks's item) saying that you are doing
 so.  Before you start, ask Matt Kaufmann to commit to incorporating your
 changes; without a commitment from Matt, he reserves the right not to consider
 doing so.</p> </color>

 <p>The subtopics listed below are sometimes referred to as ``chapters'' of
 this (Developer's) Guide.  They can be read in any order, but on a first read,
 you may find it helpful to read them in the order in which they appear
 below.</p>

 <p>NEXT SECTION: @(see developers-guide-introduction)</p>")

(defxdoc developers-guide-introduction
  :parents (developers-guide)
  :short "Introduction"
  :long "<p>This <see topic='@(url developers-guide)'>Developer's Guide</see>
 is intended to provide an overview of how to maintain the ACL2 source
 code.</p>

 <p>There are several points we want to make at the outset.</p>

 <h3>Experienced users only, please</h3>

 <p>Without a sense of how to use ACL2, there is significant risk that an
 attempt to modify its source code could be truly misguided.</p>

 <h3>This guide is highly incomplete!</h3>

 <p>There are at least the following reasons for its incompleteness.</p>

 <ul>

 <li>Comments in the source code may already suffice for a given topic.</li>

 <li>The source code is large and complex; this guide is, ideally,
 manageable.</li>

 <li>At the time this manual is being created, many aspects of the system are
 difficult to explain because the writers have forgotten them &mdash; and
 that's OK!

 <ul><li>It is typical to read comments (which are sometimes extensive) when
 modifying the source code, often after reading some user-level documentation,
 to get up to speed.  As we encounter comments that aren't clear (and correct),
 we fix them.</li></ul></li>

 </ul>

 <h3>Where do the definitive sources reside?</h3>

 <p>The ACL2 source code resides on the filesystem of the Computer Science
 Department at the University of Texas.  These files are kept in sync with the
 github sources, of course.  So unless something goes horribly wrong with
 github, the sources may reasonably be said also to reside at <code><a
 href='https://github.com/acl2/acl2'>https://github.com/acl2/acl2</a></code></p>

 <h3>Some longer source code comments are called ``Essays''.</h3>

 <color rgb='#800080'><p>[JUST TOUCH ON THIS SECTION]</p></color>

 <p>These essays can provide very helpful introductions, at a higher level than
 may be found in Lisp comments that are inside definitions.  You can search for
 the string</p>

 @({
 ; Essay on ...
 })

 <p>by using, for example, @('grep') or the Emacs utility @('meta-x
 tags-search').  For example, suppose you are trying to understand @(tsee
 make-event).  Then a first step might be to review its user-level
 documentation (for @(see make-event) and its subtopics); but after that, you
 could search with @('grep'), or with a tags-search, for the following
 string.</p>

 @({
 ; Essay on make-event
 })

 <p>If your search is case-insensitive, then you will find ``; Essay on
 Make-event''.  Such an essay is not necessarily complete, or even close to
 being complete, but it is a good starting point before modifying source code
 that supports @('make-event').</p>

 <color rgb='#c00000'>
 <p>As of this writing there are nearly 100 such essays!  This manual does not
 begin to cover them all; in fact it barely touches on most of them, at best.
 Moreover, some important components of ACL2 have no high-level essay.</p>
 </color>

 <ul><li>For example, there is no essay on induction.  In such cases the
 relevant source comments are generally found inside definitions.  For example,
 in the case of induction one can start with the function, @('induct'), and
 read its comments and code to start exploring the rather complex ACL2
 implementation of induction.</li></ul>

 <h3>Some initiative and hacking are necessary.</h3>

 <p><b>Example 1</b>.  Suppose you encounter the @('pspv') argument in the
 source function @('simplify-clause'), and you don't know what that is.  You
 can then search for @('pspv') and you'll find the following: @('(access
 prove-spec-var pspv :rewrite-constant)').  Now @('access') is a basic
 record-accessing utility that we do cover in this manual; and we'll also talk
 about the use of Emacs to find definitions.  So you'll know to use the Emacs
 command, @('meta-.') , to take you to the definition of the record structure,
 @('prove-spec-var').  There, you'll find a few comments that explain this
 structure; unfortunately, however, not many.  The field names can provide a
 clue.  One of the fields is @('rewrite-constant'), so if you're exploring the
 @('pspv') because of its effect on rewriting, you can guess that this field is
 relevant.  So let's say that you want to know about the @('rewrite-constant')
 field.  Using @('meta-.') once again, you can find the @('rewrite-constant')
 record structure definition; and this time there are many comments.</p>

 <p><b>Example 2</b>.  What is the flow of the ACL2 waterfall?  By using the
 Emacs command, @('meta-.') , we can develop this call graph.</p>

 @({
      waterfall
        waterfall1-lst
          waterfall1
            waterfall0
            waterfall0-with-hint-settings
              waterfall0
                waterfall-step
 })

 <h3>User-level documentation vs. system-level documentation</h3>

 <p>User-level documentation is in community book
 @('books/system/doc/acl2-doc.lisp') and appears in the acl2+books combined
 manual and the ACL2 User's Manual.  (This Guide is an exception, of course; it
 is included in the acl2-books combined manual but it is at the system level,
 not at the user level.)  See @(see developers-guide-build) for how that
 documentation is integrated into ACL2 builds.</p>

 <p>By contrast, system-level documentation is in Lisp comments found in the
 ACL2 sources and in this Guide.  Those comments are geared towards
 implementors; so while they are written with care, they sometimes assume
 implementation-level background.  For example, the word ``primitive'' is
 sometimes used for any built-in function, while other times it might suggest
 the more limited notion implemented by the constant
 @('*primitive-formals-and-guards*'); the context may help in understanding the
 intended meaning (though perhaps, eventually, someone will use ``built-in''
 for all uses of the broader notion).  Sometimes an Essay (see above) may
 provide helpful background; indeed, comments sometimes direct the reader to an
 Essay.</p>

 <color rgb='#c00000'>
 <p>Please read the comments in a definition carefully before you modify it!
 In particular, there are often comments warning you to ``keep in sync'' with
 one or more other definitions, which need to be heeded.</p>
 </color>

 <p>It is often helpful to read user-level documentation before reading
 system-level documentation when preparing to modify ACL2.  Often the
 user-level documentation will be on specific topics, such as @(tsee
 make-event) as described above.  But user-level documentation may also provide
 general background; in particular, the topic @(see programming-with-state) is
 highly recommended for anyone who is considering doing system development.
 However, for most ACL2 system-level documentation, it is best to put it in the
 ACL2 sources as Lisp comments or in this Guide, rather than elsewhere in the
 documentation, to avoid confusing or intimidating typical users.</p>

 <p>The topic @(tsee system-utilities) is a borderline case.  These utilities
 were created for developing the ACL2 system.  However, users increasingly do
 ``systems programming'' in ACL2; so, this topic collects some system-level
 utilities that may benefit such users.</p>

 <h3>This is a living document.</h3>

 <color rgb='#c00000'>
 <p>Feel free to modify this guide!  You can, if you like, run modifications by
 the acl2-devel mailing list before making changes.</p>
 </color>

 <h3>Do not feel obligated to read this guide linearly, cover-to-cover!</h3>

 <p>Exploration of the ACL2 system is perhaps most efficient when
 goal-directed, i.e., when you are trying to understand specific aspects of the
 system.  That said, a quick browse of this entire guide is recommended for
 ACL2 system developers.</p>

 <p>NEXT SECTION: @(see developers-guide-emacs)</p>")

(defxdoc developers-guide-emacs
  :parents (developers-guide)
  :short "Emacs As a Critical Tool for ACL2 Developers"
  :long "<p>Emacs has traditionally been used by ACL2 system developers.  In
 principle, any text editor would suffice.  But as of this writing, we don't
 know how to maintain ACL2 effectively without using Emacs.  It is not the goal
 here to give an Emacs tutorial; but here are some Emacs utilities that are
 particularly useful to ACL2 developers.</p>

 <ul>

 <li>@('meta-.')<br/>Move to the indicated definition in the ACL2 sources (must
 initialize with @('meta-x visit-tags-table')).  This is much faster than
 bringing up the file in an editor and searching for the definition.  Use a
 prefix argument to find the next match if desired.</li>

 <li>@('meta-x tags-apropos')<br/>Bring up all symbols whose definition matches
 the given regular expression.  One can find a suitable such symbol and use
 @('meta-.') to go rapidly to its definition.</li>

 <li>@('meta-x tags-search')<br/>Find an occurrence of a given regular
 expression, using @('meta-,') to find subsequent occurrences.</li>

 <li>@('meta-x tags-query-replace')<br/>Replace occurrences of a given regular
 expression with a given string, with a query each time, using @('meta-,') to
 find subsequent occurrences.</li>

 <li>@('meta-x compare-windows')<br/>After splitting the window in two
 (say, with @('control-x 2')), compare the upper window with the lower.  This
 is particularly useful when comparing two versions of some source code, for
 example, the original version and a modified version.</li>

 </ul>

 <p>The file @('emacs/emacs-acl2.el') has many helpful utilities, so you may
 want to load it in your @('~/.emacs') file.</p>

 <ul>

 <li>For example, it defines @('ctl-t w') as a shortcut for @('meta-x
 compare-windows'), and it defines @('ctl-t q') to do the same thing but
 ignoring whitespace (by providing a prefix argument for @('meta-x
 compare-windows')).</li>

 <li><color rgb='#c00000'>Maintain @('emacs/emacs-acl2.el') with taste: avoid using fancy Emacs Lisp
 code that could be difficult for others to maintain.</color>  If one is competent at
 maintaining the ACL2 sources base, then a little Emacs Lisp competence should
 be sufficient for maintaining @('emacs/emacs-acl2.el') as well.  So avoid
 fancy Emacs features not already found in use in that file.</li>

 </ul>

 <p>NEXT SECTION: @(see developers-guide-background)</p>")

(defxdoc developers-guide-background
  :parents (developers-guide)
  :short "Some Implementation Background"
  :long "<color rgb='#c00000'>
 <p>When background is found to be lacking in this topic, it might be acquired
 by querying the acl2-devel mailing list.  In that case it would probably be
 good to extend this chapter by adding the background that had been
 lacking.</p>
 </color>

 <h3>Source files</h3>

 <p>ACL2 has many source files.  <color rgb='#c00000'>The definitive list of
 source files is the value of the constant @('*acl2-files*') found in source
 file @('acl2.lisp').</color> This list is consistent with the list associated
 with the variable @('\"sources\"') in @('GNUmakefile'), with the exception of
 generated file @('doc.lisp') (which is discussed later in this Guide; see
 @(see developers-guide-build)).  Perhaps surprisingly, @('acl2.lisp') is not
 in either list!  That's due to a traditional ambiguity in the use of the term
 ``source file'' for ACL2.  The files in the list @('*acl2-files*') are all
 written in ACL2 (with the exception of relatively little raw Lisp code, as
 discussed in the section on ``Readtime Conditionals'' below).  A few other
 files support the infrastructure surrounding the ACL2 system.  These may be
 found in the definition of variable @('\"sources_extra\"') in
 @('GNUmakefile'); @('acl2.lisp') is one of those files.</p>

 <p>We may talk of ``earlier'' and ``later'' source files.  Here we reference
 their order in @('*acl2-files*'), which is essentially the order in which they
 are processed via @(tsee ld) when building an ACL2 executable.  Note however
 that files @('*-raw.lisp') are not intended for processing by @(tsee ld)
 during the build, but rather, are simply loaded directly into Common Lisp,
 perhaps after being compiled.</p>

 <p><color rgb='#c00000'>The names of the source files are somewhat suggestive
 of their contents.  However, over time this correspondence has weakened, in
 large part because of the requirement that a function must be defined before
 it is used.</color> For example, function @('find-rules-of-rune') was moved in
 git commit @('5647bd402e') from @('defthm.lisp') to an earlier file,
 @('rewrite.lisp'), in support of a new function,
 @('backchain-limit-enforcers'), which in turn was introduced in support of an
 existing function in @('rewrite.lisp')
 (@('tilde-@-failure-reason-phrase1')) that reports failures in the @(see
 break-rewrite) loop.</p>

 <h3>Source file <tt>axioms.lisp</tt></h3>

 <p>The source file @('axioms.lisp') is the place for defining most @(see
 logic)-mode functions that form the core of the ACL2 programming language, and
 also for some basic axioms and theorems about these functions as well as the
 built-in primitives like @(see car) and @(see unary-/) that have no explicit
 definition.  The theorems are stated as @(tsee defthm) @(see events), while
 the axioms are stated as @(tsee defaxiom) events.  The axioms are intended to
 completely specify the @(see ground-zero) theory.  However, it is less clear
 when to include a @('defthm') event into @('axioms.lisp'), rather than simply
 putting that theorem into a book.</p>

 <p>The section on ``Build-time proofs'' in the topic, @(see
 developers-guide-build), has a discussion of executing ``@('make proofs')'' to
 admit events, including those in @('axioms.lisp').  Some @('defthm') events
 are critical for this purpose, for example, for proving termination or
 verifying guards.  Others are simply very basic: so useful that it seems a
 pity to relegate them to books, rather than to include them in the build.
 Moreover, the specific form of some axioms and theorems is chosen to be useful
 for reasoning; for example, here is a rather critical @(':')@(tsee elim) rule
 in addition to being an important axiom.</p>

 @({
 (defaxiom car-cdr-elim
   (implies (consp x)
            (equal (cons (car x) (cdr x)) x))
   :rule-classes :elim)
 })

 <p>It is good to be careful when considering the addition of @('defthm')
 events to @('axioms.lisp').  If @('defthm') events are to be added in order to
 support termination or @(see guard) verification when doing ``@('make
 proofs')'', you can consider making the events @(tsee local) so that they
 don't make it into the build.  But you might leave some non-local if they seem
 to be extremely useful, for example:</p>

 @({
 (defthm fold-consts-in-+
   (implies (and (syntaxp (quotep x))
                 (syntaxp (quotep y)))
            (equal (+ x (+ y z))
                   (+ (+ x y) z))))
 })

 <p>There is potential controversy here.  One could argue that such theorems
 belong in books, not in the source code.  This can be argued either way:
 putting in the source code is good because ACL2 can do obviously-expected
 things at start-up, and is bad because it's inelegant and narrows user
 choices.  These days, we tend to add @('defthm') events to @('axioms.lisp')
 only sparingly, without removing any.  One could argue endlessly about this
 controversy, but there are probably many more fruitful ways to spend limited
 development resources!</p>

 <h3>The ACL2 state and logical world</h3>

 <p><color rgb='#c00000'>The ACL2 state is represented in the implementation as
 a symbol, which is the value of constant @('*the-live-state*').</color>
 Sometimes we call this the ``<color rgb='#c00000'>live state</color>'', to
 distinguish it from its logical value, which is a list of fields.  See @(see
 state) for relevant background.</p>

 <p><color rgb='#c00000'>It may seem impossible for a fixed symbol to represent
 a changeable state.  But let us consider for example what happens when we
 update a state global variable (see @(see f-put-global)) in raw Lisp.</color>
 In the following example (where we elide code for the case of wormholes) there
 are two cases.  The interesting case is the first one, in which the state is
 the live state.  We see below that there is an associated global (special)
 variable, in a package obtained by prefixing the string @('\"ACL2_GLOBAL_\"')
 to the front of the symbol's package-name: <tt><color
 rgb='#c00000'>ACL2_GLOBAL_</color>ACL2::XYZ</tt>.  The code below updates that
 global.</p>

 @({
 ? (pprint (macroexpand '(f-put-global 'xyz (+ 3 4) state)))

 (LET ((#:G128770 (+ 3 4)) (#:G128771 STATE))
   (COND ((LIVE-STATE-P #:G128771)
          (COND (*WORMHOLEP* ...))
          (LET ()
            (DECLARE (SPECIAL ACL2_GLOBAL_ACL2::XYZ))
            (SETQ ACL2_GLOBAL_ACL2::XYZ #:G128770)
            #:G128771))
         (T (PUT-GLOBAL 'XYZ #:G128770 #:G128771))))
 ?
 })

 <p>To read a state global from the live state, we simply read its associated
 global variable.</p>

 @({
 ? (pprint (macroexpand '(f-get-global 'xyz state)))

 (LET ((#:G128772 STATE))
   (DECLARE (SPECIAL ACL2_GLOBAL_ACL2::XYZ))
   (COND ((LIVE-STATE-P #:G128772) ACL2_GLOBAL_ACL2::XYZ)
         (T (GET-GLOBAL 'XYZ #:G128772))))
 ?
 })

 <p>Note that the ACL2 state can be viewed as a special, built-in case of a
 @(see stobj).  Indeed, we may also speak of ``<color rgb='#c00000'>live
 stobjs</color>'', to distinguish them from their logical, list-based
 representations, and a stobj, @('st'), is represented in the implementation as
 @('*the-live-st*').  These ``live'' constants are illustrated below.</p>

 @({
 ACL2 !>(defstobj st fld)

 Summary
 Form:  ( DEFSTOBJ ST ...)
 Rules: NIL
 Time:  0.01 seconds (prove: 0.00, print: 0.00, other: 0.01)
  ST
 ACL2 !>:q

 Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
 ? *the-live-st*
 #<SIMPLE-VECTOR 1>
 ? *the-live-state*
 ACL2_INVISIBLE::|The Live State Itself|
 ?
 })

 <p>One of the logical fields of the state is the <i>global-table</i>, which is
 an association list mapping symbols, namely state global variables (sometimes
 called ``state globals''), to values.  See also @(see programming-with-state).
 One particular state global, the symbol @('current-acl2-world'), is mapped to
 the current logical @(see world), often just called ``the world''.  Here is
 the logical definition of the function @('(w state)') that returns this world;
 note that it calls the macro @(tsee f-get-global), which, as explained above,
 generates a read of a Lisp global.</p>

 @(def w)

 <p>The current logical world, in turn, is a list of triples of the form
 @('(name property . value)').  The function @(tsee getprop) may be used to
 access the value for a given name and property.  For example, suppose that we
 submit the event @('(defun f (x) (cons x x))').  This actually pushes several
 triples on the world, one of which is the so-called <i>unnormalized body</i>
 of @('f'), accessible via @('getprop') as follows.</p>

 @({
 ACL2 !>(getprop 'f 'unnormalized-body nil 'current-acl2-world (w state))
 (CONS X X)
 ACL2 !>
 })

 <p>It is extremely common for the last three arguments of @('getprop') to be
 as displayed above, so the macro @(tsee getpropc) is often used instead.</p>

 @({
 ACL2 !>(getpropc 'f 'unnormalized-body)
 (CONS X X)
 ACL2 !>
 })

 <p>Also see @(see walkabout) for a tool that can be extremely helpful for
 examining the world.</p>

 <h3>Terms, translate, and untranslate</h3>

 <p>For relevant background on the notion of <i>term</i> in ACL2, see @(see
 term).  The ACL2 source code traffics in what that documentation topic calls
 ``translated terms''.  In any discussion at the implementation level,
 including this guide and source code comments, <color rgb='#c00000'>we just
 say ``term'' to refer to a translated term.  The source code traffics almost
 entirely in terms,</color> though user input is in the form of what the
 documentation for @(see term) calls an ``untranslated term''.  <color
 rgb='#c00000'>The ACL2 functions @(tsee translate) and @(tsee untranslate) map
 from untranslated terms to terms and vice-versa, respectively.</color> These
 both take the @(see world) as a formal parameter, because they need to consult
 the world: for example, @('translate') consults the world to determine, for a
 call @('(f t1 t2 ...)'), whether @('f') is a function symbol, a macro, or (in
 the error case) neither of these; and @('untranslate') consults the world for
 more subtle reasons such as converting a call of @(tsee return-last) to
 something more readable.</p>

 <p>The definition of the function @('untranslate1'), which is the workhorse
 for @('untranslate'), is instructive for how ACL2 processes terms.  <color
 rgb='#c00000'>It has the following form.</color></p>

 @({
 (defun untranslate1 (term iff-flg untrans-tbl preprocess-fn wrld)
   (let ((term (if preprocess-fn ... term)))
     (cond ((variablep term) term)
           ((fquotep term)
            (cond (<basically, not a cons or symbol>
                   (cadr term))
                  (t term)))
           ((flambda-applicationp term)
            <Turn the lambda application into a LET.>)
           ((eq (ffn-symb term) 'if)
            <Many special cases, e.g.,
             (if x1 'nil 't) negates untranslation of x1>
           ...))))
 })

 <color rgb='#c00000'>

 <p>This sort of structure is typical: handle the variable case, then the case
 of @('(quote _)'), then the case of a lambda application, and finally one or
 more cases for the call of a function symbol.  If you peruse the source code
 you will see handy term utilities.  Please strive for consistency by studying
 some of those (e.g., search the source code for @('\"variablep\"') or
 @('\"quotep\"')).  For example, don't build a new term with @('(cons fn
 args)'); use <tt>cons-term</tt> or <tt>fcons-term</tt> instead of
 <tt>cons</tt>.</p>

 </color>

 <h3>The @(tsee defrec) macro</h3>

 <p>We defer to a later chapter (see @(see developers-guide-utilities)) a
 discussion of macros that are commonly used in the ACL2 implementation, with
 one exception: @(tsee defrec).  We cover that macro here because it is so
 crucial for understanding some topics covered below.</p>

 <p>See @(see defrec) for user-level documentation on @('defrec').  This macro
 provides a cheap way to lay out a record structure using @('cons') (since the
 Common Lisp macro @('defstruct') is not supported by ACL2, which does not have
 structures).  Sometimes it is worthwhile to think a bit about expected reads
 and writes of the fields, to help lay them out efficiently.  For example,
 consider the definition of an important record for the prover,
 @('prove-spec-var') (with comments omitted here):</p>

 @({
 (defrec prove-spec-var
   ((rewrite-constant induction-hyp-terms . induction-concl-terms)
    (tag-tree hint-settings . tau-completion-alist)
    (pool . gag-state)
    user-supplied-term displayed-goal orig-hints . otf-flg)
   t)
 })

 <p>Notice above and in the following generated definition that the field,
 @('orig-hints'), is buried deep inside this structure.</p>

 @({
 ACL2 !>:trans (access prove-spec-var some-pspv :orig-hints)

 ((LAMBDA (ORIG-HINTS)
          (CAR (CDR (CDR (CDR (CDR (CDR ORIG-HINTS)))))))
  SOME-PSPV)

 => *

 ACL2 !>
 })

 <p>An Emacs @('tags-search') for ``@(':orig-hints')'' shows that this field is
 used only during initialization of the prover (excluding ACL2(p)), not within
 the waterfall, let alone the rewriter; of course, this is hardly surprising.
 So it seems fine to push this field way back in the record definition.  On the
 other hand, the @('rewrite-constant') field is more rapidly accessible as the
 @(tsee caar), which is reasonable since it is accessed quite frequently within
 the waterfall.</p>

 <p>One can often learn about a record by reading its field names, seeing how
 they are used in the source code (with a tags-search), or reading code
 comments inserted into the @('defrec') form that defines it or near that
 definition.  You could try learning more now about the @('prove-spec-var') and
 @('rewrite-constant'), which are quite important in the prover code.</p>

 <h3>Commands and events</h3>

 <color rgb='#800080'>
 <p>DEMO: USING WALKABOUT TO EXPLORE THE WORLD</p>
 </color>

 <p>Among the triples in the @(see world) are so-called <i>command
 landmarks</i> and <i>event landmarks</i>, which are put there at the
 conclusion of a @(see command) or @(see event), respectively.  What are
 commands and events, and what's the difference between them?</p>

 <p>Let's start with commands.  The (user-level) documentation for @(see
 command)s says that they are ``forms you type at the top-level, but the word
 `command' usually refers to a top-level form whose evaluation produces a new
 logical @(see world).''  At the implementation level, a command is a form read
 and evaluated by @(see ld).  If you follow the source code starting with
 @('ld'), you'll see that it reads and evaluates forms with the function
 @('ld-loop'), which in turn calls @('ld-read-eval-print') on each form.  That
 function, in turn, calls @('ld-read-command') to read the next form and then
 calls a version of @(tsee trans-eval), @('trans-eval-default-warning'), to
 evaluate it.  (See also the section on ``Evaluators'' in the chapter, @(see
 developers-guide-utilities); also see the chapter, @(see
 developers-guide-evaluation).)  When there is no error, the function
 @('maybe-add-command-landmark') is called.  It checks whether the world has
 changed, and if so it pushes a new triple on the new world, a so-called
 <i>command landmark</i>, provided the new world doesn't already have a command
 landmark as the topmost triple.  Let's use the @(tsee walkabout) utility to
 see what a command landmark might look like.</p>

 @({
 ACL2 !>(with-output :off :all (defun foo (x) x)) ; avoid noise just below
  FOO
 ACL2 !>(walkabout (w state) state)

 Commands:
 0, 1, 2, ..., nx, bk, pp, (pp n), (pp lev len), =, (= symb), and q.

 ((COMMAND-LANDMARK GLOBAL-VALUE 7357 ...)
  (EVENT-LANDMARK GLOBAL-VALUE 8625 ...)
  (FOO ABSOLUTE-EVENT-NUMBER . 8625)
  ...)
 :1
 (COMMAND-LANDMARK GLOBAL-VALUE 7357 ...)
 :pp
 (COMMAND-LANDMARK GLOBAL-VALUE 7357
                   (:LOGIC WITH-OUTPUT :OFF
                           :ALL (DEFUN FOO (X) X))
                   \"/share/projects/\")
 :
 })

 <p>The triple just above is, as with every triple in the world, of the form
 @('(sym prop . val)').  We thus interpret the triple above to say that the
 current @('command-landmark') has a @('global-value') property of the form
 @('(7357 (:logic . <form>) <dir> . nil)').  The definition of the record
 structure @('command-tuple') (which is easy to find with the Emacs command,
 @('meta-.')) uses the @(tsee defrec) macro, discussed above.  For now we
 explain the fields in our example as follows; see the Essay on Command Tuples
 and ensuing definitions for more information.</p>

 <ul>

 <li>the <i>absolute command number</i> is 7357.</li>

 <li>The @(tsee defun-mode) is @(':logic').</li>

 <li>The <i>form</i> is @('(with-output :off :all (defun foo (x) x))').</li>

 <li>The @(tsee cbd) is @('\"/share/projects/\"').</li>

 <li>The @('last-make-event-expansion') field is @('nil').</li>

 </ul>

 <p><color rgb='#c00000'>We turn now from commands to @(see events).</color>
 There are primitive events that modify the world such as a call of @(tsee
 defun), @(tsee defthm), and @(tsee table).  See @(see events) and especially
 see @(see embedded-event-form), which explain that events may go in calls of
 @(tsee encapsulate) and @(tsee progn), which themselves are also (compound)
 events, and events may also go in @(see books).  Several other utilities are
 events in the sense that they are allowed in compound events and books, but
 they are really just wrappers of sorts for actual events.  <color
 rgb='#c00000'>Here is a list of event macros, taken from a comment in the
 definition of function @('chk-embedded-event-form'), which is the recognizer
 for (embeddable) events.</color></p>

 <ul>

 <li>@('local')</li>
 <li>@('skip-proofs')</li>
 <li>@('with-guard-checking-event')</li>
 <li>@('with-output')</li>
 <li>@('with-prover-step-limit')</li>
 <li>@('with-prover-time-limit')</li>
 <li>@('make-event')</li>

 </ul>

 <p>Of course, @(tsee make-event) is a complex sort of wrapper, in that it
 serves to <i>generate</i> an event, its <i>expansion</i>.</p>

 <p>Continuing the demo of @('walkabout') started above (when explaining
 commands), we see an <i>event-landmark</i> immediately below the
 command-landmark.</p>

 @({
 :nx
 (EVENT-LANDMARK GLOBAL-VALUE 8625 ...)
 :pp
 (EVENT-LANDMARK GLOBAL-VALUE 8625 ((DEFUN) FOO . :IDEAL)
                 DEFUN FOO (X)
                 X)
 :
 })

 <p>Let's take this opportunity to explore how to make sense of ACL2 data
 structures.  If we use the Emacs command @('meta-x tags-apropos') on
 @('\"event-landmark\"') we find the function @('add-event-landmark'); then
 using the @('meta-.') command on @('add-event-landmark'), we find its
 definition and we see a call of @('make-event-tuple').  That function has
 comments that explain the fields; perhaps more illuminating, accessors for
 event-tuple fields are defined immediately below the definition of
 @('make-event-tuple').  We can apply these accessors to deconstruct the value,
 @('val'), in the triple above, @('(event-landmark global-value . val)').</p>

 @({
 ACL2 !>(let ((val (cddr '(EVENT-LANDMARK GLOBAL-VALUE 8625 ((DEFUN) FOO . :IDEAL)
                                          DEFUN FOO (X)
                                          X))))
          (list :number (access-event-tuple-number val)
                :depth  (access-event-tuple-depth val)
                :type   (access-event-tuple-type val)
                :skipp  (access-event-tuple-skipped-proofs-p val)
                :namex  (access-event-tuple-namex val)
                :form   (access-event-tuple-form val)
                :symcls (access-event-tuple-symbol-class val)))
 (:NUMBER 8625
          :DEPTH 0
          :TYPE DEFUN
          :SKIPP NIL
          :NAMEX FOO
          :FORM (DEFUN FOO (X) X)
          :SYMCLS :IDEAL)
 ACL2 !>
 })

 <color rgb='#c00000'>

 <p>We conclude our discussion of commands and events with a few
 observations.</p>

 <ul>

 <li>Commands can be undone, using @(tsee ubt) and related utilities.  Events
 are not undone (except when they are also commands); only commands are
 undone.</li>

 <li>@(':')@(tsee Puff) is applied to @(see command-descriptor)s, so naturally
 it expands commands, not events.</li>

 <li>Only events can go into books and calls of @(tsee progn) or @(tsee
 encapsulate), not arbitrary commands.</li>

 </ul>

 </color>

 <h3>Exploring the source code with an example: prover flow</h3>

 <p>An important skill for ACL2 code development and maintenance is the ability
 to explore the source code to gain necessary background.  This is really an
 art, developed with experience.  There has been a lot of attention to
 documenting the source code &mdash; as of mid-March 2018, about 30% of the
 source file lines (that is, from @('*.lisp') files not including the generated
 documentation file @('doc.lisp')) consisted entirely of a comment line, and of
 course other lines contained comments as well.  Here we show the raw data.</p>

 @({
 ginger:/projects/acl2/acl2/saved% wc -l *.lisp | grep total
   373606 total
 ginger:/projects/acl2/acl2/saved% wc -l doc.lisp
 121865 doc.lisp
 ginger:/projects/acl2/acl2/saved% grep '^[ ]*;' *.lisp | wc -l
 76588
 ginger:/projects/acl2/acl2/saved% grep '^[ ]*;' doc.lisp | wc -l
 1545
 ginger:/projects/acl2/acl2/saved%
 })

 <p>Unfortunately, 30+% comments is not sufficient!  In a perfect world, more
 ACL2 functions would have extensive documentation, with clear pointers to
 necessary background including high-level algorithm discussion.  This Guide is
 intended to help to fill the gap, but can only do so partially.  The missing
 additional ingredient to absorbing source code &mdash; as practiced for years
 by ACL2 developers as of this writing in March 2018 &mdash; is the ability to
 explore the sources.  Ideally this is a skill that can be learned by
 practicing.</p>

 <p>As a simple example, we show how to explore the source code to get a sense
 of the flow of the theorem prover.  This is very far from getting a sense of
 the ACL2 system in general, which supports much more than the prover (think of
 book certification, @(tsee make-event), @(see invariant-risk), and on and
 on).</p>

 <p>Let's start with @(tsee thm):</p>

 <color rgb='#800080'>

 <p>DEMO: EXPLORE HOW THM ULTIMATELY CALLS THE REWRITER.  But unlike the
 discussion below, I'll go bottom-up.  This may give us some idea of how the
 prover is structured.  One result may be found in the documentation section,
 @(see developers-guide-background-extra).</p>
 </color>

 @(def thm)

 <p>@('Thm-fn') calls @('prove'), which calls @('prove-loop') and so on, as is
 easy to discover using the Emacs command, @('meta-.') .  We thus work our way
 to the waterfall.</p>

 @({
 thm-fn
   prove
     prove-loop
       prove-loop0
         prove-loop1
           prove-loop2
             waterfall
 })

 <p>At this point things get more complicated.  @('Waterfall') calls
 @('waterfall1-lst@par'), which should be thought of as @('waterfall1-lst'), as
 discussed below where we talk about ACL2(p).  We see that @('waterfall1-lst')
 is part of a rather complex @(tsee mutual-recursion).  But a key function
 called in that @('mutual-recursion') is @('waterfall-step'), which is shown as
 calls of @('waterfall-step@par').  Knowing about @('waterfall-step') is one of
 those pieces of background knowledge to learn that makes it easier over time
 to peruse the ACL2 sources.  In the body of that function is a call of
 @('waterfall-step1'), which provides a clue about the main flow of the prover:
 the key subroutine of a function @('foo') often has the name @('foo1'), or
 perhaps @('foo-1'), @('foo-aux'), or @('foo-rec'), or more generally,
 @('foo<something>').  The function @('waterfall-step1') has a nice structure
 showing how it leads to calls of individual waterfall processing functions, in
 particular, the simplifier via the function @('simplify-clause').  We can
 explore the definition of @('simplify-clause') in a similar way, finding
 @('simplify-clause1'), which has these key subroutines.</p>

 @({
 remove-trivial-equivalences
 forward-chain-top
 setup-simplify-clause-pot-lst
 process-equational-polys
 rewrite-clause
 })

 <p>The flow suggests that the first four of these functions are called to set
 things up for the call to @('rewrite-clause').  That function can be similarly
 explored, in particular to find key subroutines that include the
 following.</p>

 @({
 built-in-clausep1
 rewrite-clause-type-alist
 rewrite-atm
 clausify
 rewrite-clause-lst
 })

 <p>The function @('rewrite-atm') does yet a bit more processing, using
 @('known-whether-nil'), before calling @('rewrite').  Feel free to explore
 @('rewrite'), but beware, as it's quite complicated!  Indeed, the usual
 activity of an ACL2 maintainer is not to explore for the sake of general
 background, as we have been doing above, but rather to explore for the sake of
 more specific understanding before making desired modifications or
 additions.</p>

 <h3>Build-time checks</h3>

 <p>There are several checks done near the end of an ACL2 build, as performed
 by (subfunctions of) the function, @('check-acl2-initialization').  There is
 not much that we need to say here, because if one of those tests fails, then
 the error message should make it clear how to proceed.</p>

 <h3>Raw Lisp and readtime conditionals</h3>

 <p>ACL2 is built on top of Common Lisp.  Some knowledge of that programming
 language is occasionally necessary.  The definitive reference is the Common
 Lisp Hyperspec, which can be found easily with a web search.</p>

 <p>Every ACL2 source file is either loaded directly into Common Lisp as part
 of the ACL2 build, or is first compiled into a compiled file before loading
 that compiled file.  (Files @('acl2.lisp') and @('acl2-init.lisp') are never
 subjected to file compilation, as noted in a comment near the top of each
 file.)  Thus, <color rgb='#c00000'>ACL2 macros including @(tsee defun), @(tsee
 defthm), @(tsee table), @(tsee defconst), @(tsee local), and @(tsee
 encapsulate) must be suitable for Common Lisp evaluation.</color> This is
 arranged differently for different macros, as illustrated by the following
 examples.</p>

 <color rgb='#800080'>
 <p>DEMO: RATHER THAN GO THROUGH WHAT'S BELOW, I'LL JUST EXPLORE DEFUN,
 DEFTHM, LOCAL, and QUIT, AND USE THEM TO EXPLAIN *features* AND SPECIFICALLY
 acl2-loop-only.</p>
 </color>

 <p>First consider @('defun').  We have only the following definition of
 @('defun') in the ACL2 source code.</p>

 @({
 #+acl2-loop-only
 (defmacro defun (&whole event-form &rest def)

 ; Warning: See the Important Boot-Strapping Invariants before modifying!

   (list 'defun-fn
         (list 'quote def)
         'state
         (list 'quote event-form)
         #+:non-standard-analysis ; std-p
         nil))
 })

 <p>The notation ``@('#+acl2-loop-only')'' is called a <i>readtime
 conditional</i>.  In this case, it says that the definition of @('defun')
 immediately following that notion is ignored by the reader unless the symbol
 @(':acl2-loop-only') is a member of the Lisp variable, @('*features*').
 Normally, and during loading and (when it occurs) compilation of ACL2 source
 files, @(':acl2-loop-only') is not a member of @('*features*'), so the
 definition above is ignored &mdash; as is appropriate, since @('defun') is
 already defined in Common Lisp.  The function @('initialize-acl2') pushes the
 symbol @(':acl2-loop-only') onto @('*features*') before beginning to @('ld')
 the ACL2 source files; thus, as ACL2 processes its own source files, the
 definition above is read (not ignored) and evaluated; you can evaluate @(':pe
 defun') in the top-level loop to see the definition above.</p>

 <p>Next consider @(tsee defthm).  This time there are two definitions.  One is
 much like the definition above of @('defun'):</p>

 @({
 #+acl2-loop-only
 (defmacro defthm (&whole event-form
                   name term
                        &key (rule-classes '(:REWRITE))
                        instructions
                        hints
                        otf-flg)

 ; Warning: See the Important Boot-Strapping Invariants before modifying!

   (list 'defthm-fn
         (list 'quote name)
         (list 'quote term)
         'state
         (list 'quote rule-classes)
         (list 'quote instructions)
         (list 'quote hints)
         (list 'quote otf-flg)
         (list 'quote event-form)
         #+:non-standard-analysis ; std-p
         nil))
 })

 <p>The other definition occurs in a raw Lisp context, as follows.</p>

 @({
 #-acl2-loop-only
 (progn

 ...

 (defmacro defthm (&rest args)
  (declare (ignore args))
  nil)

 ...)
 })

 <p>Thus, the Common Lisp loader or compiler will see this definition of
 @('defthm'), but the @('ld') of the ACL2 source files will not.  In summary:
 @('defthm') is defined in terms of @('defthm-fn') in the ACL2 loop, but it is
 defined simply to return @('nil') in raw Lisp.</p>

 <p>Interesting cases are @(tsee local) and @(tsee encapsulate).  These have
 rather complex definitions in the ACL2 loop, but let's see
 what happens during macroexpansion in raw Lisp.</p>

 @({
 ? (pprint
    (macroexpand '(encapsulate (((f *) => *))
                    (local (defun f (x) x))
                    (defun g (x) (f x))
                    (local (defthm consp-g
                             (implies (consp x) (consp (g x))))))))

 (PROGN (DEFUN F (X1) (THROW-OR-ATTACH F (X1)))
        (LOCAL (DEFUN F (X) X))
        (DEFUN G (X) (F X))
        (LOCAL (DEFTHM CONSP-G (IMPLIES (CONSP X) (CONSP (G X))))))
 ? (macroexpand '(LOCAL (DEFUN F (X) X)))
 NIL
 T
 ? (macroexpand '(LOCAL (DEFTHM CONSP-G (IMPLIES (CONSP X) (CONSP (G X))))))
 NIL
 T
 ?
 })

 <p>Evidently, @('encapsulate') defines its signature functions simply to cause
 errors, actually like this:</p>

 @({
 ACL2 Error in TOP-LEVEL:  ACL2 cannot ev the call of non-executable
 function F on argument list:

 (3)

 })

 <p>It is also apparent that calls of @('local') in raw Lisp expand simply to
 @('nil').</p>

 <p>To understand such behavior, let's look at the definitions of @('local')
 and @('encapsulate'), eliding comments and some code for brevity.  The elided
 code in the first definition of @('encapsulate') below, which is for raw Lisp,
 defines the functions in the signature to cause errors when called.</p>

 @({
 #-acl2-loop-only
 (progn

 ...

 (defmacro encapsulate (signatures &rest lst)
   `(progn ,@(mapcar <...elided code...> signatures)
           ,@lst))

 ...

 (defmacro local (x)
   (declare (ignore x))
   nil)

 ...)

 #+acl2-loop-only
 (defmacro local (x)
   (list 'if
         '(equal (ld-skip-proofsp state) 'include-book)
         '(mv nil nil state)
         (list 'if
               '(equal (ld-skip-proofsp state) 'initialize-acl2)
               '(mv nil nil state)
               (list 'state-global-let*
                     '((in-local-flg t))
                     (list 'when-logic \"LOCAL\" x)))))

 #+acl2-loop-only
 (defmacro encapsulate (&whole event-form signatures &rest cmd-lst)
   (list 'encapsulate-fn
         (list 'quote signatures)
         (list 'quote cmd-lst)
         'state
         (list 'quote event-form)))
 })

 <p>We see that in raw Lisp, @('encapsulate') generates a suitable @('progn')
 and @('local') is a no-op.</p>

 <p>You may find it instructive to look at the @('#-acl2-loop-only') and
 @('#+acl2-loop-only') definitions of other event macros.</p>

 <h3>Implementation-specific code</h3>

 <p>As of this writing, six Common Lisp implementations support ACL2: Allegro
 Common Lisp (ACL), Clozure CL (CCL), CMU Common Lisp (CMUCL), GNU Common
 Lisp (GCL), LispWorks, and Steel Bank Common Lisp (SBCL).  (Note: As of
 Sept. 2018 there remains a problem with CMUCL that was reported several months
 ago, which the implementor has indicated that he intends to try to fix.)  Some
 ACL2 raw-Lisp code is implementation-specific, that is, depends on which of
 these six Common Lisp implementations is the host lisp.  See for example the
 definitions of @('exit-lisp') and @('getenv$-raw').  Here is an elided version
 of the definition of @('exit-lisp').  Notice the readtime conditional used for
 each of the six supported Lisp implementations and also some that are no
 longer supported, like CLISP.  (Note: Normally we see ``@('gcl')'' for GCL but
 sometimes, as below, we see the somewhat archaic (but still acceptable)
 ``@('akcl')''.)</p>

 @({
 (defun exit-lisp (&optional (status '0 status-p))
   <<code elided>>
   #+clisp
   (if status-p (user::exit status) (user::exit))
   #+lispworks ; Version 4.2.0; older versions have used bye
   (if status-p (lispworks:quit :status status) (lispworks:quit))
   #+akcl
   (if status-p (si::bye status) (si::bye))
   #+lucid
   (lisp::exit) ; don't know how to handle status, but don't support lucid
   #+ccl
   (if status-p (ccl::quit status) (ccl::quit))
   #+cmu
   <<code elided>>
   #+allegro
   (user::exit status :no-unwind t)
   #+(and mcl (not ccl))
   (cl-user::quit) ; mcl support is deprecated, so we don't worry about status
   #+sbcl
   <<code elided>>
   (progn status-p status))
 })

 <h3>ACL2 ``Experimental Versions''</h3>

 <p>Two dissertations have produced modifications of ACL2.</p>

 <ul>

 <li>ACL2(r), courtesy of Ruben Gamboa, extends the rational number data type
 to include irrational numbers.  It is built on a foundation of non-standard
 analysis, which is a logical theory (really, more than one) that makes sense
 of Leibniz's notion of ``infinitesimal'' in place of foundations based on
 limits.</li>

 <li>ACL2(p), courtesy of David Rager, supports both parallel evaluation in
 general and parallelization of the ACL2 waterfall.</li>

 </ul>

 <p>Code that is to be read only when building ACL2(r) has the readtime
 conditional @('#+:non-standard-analysis'), where the leading colon is actually
 optional but is typically used by convention.  Code that is to be read only
 when building ACL2(p) has the readtime conditional @('#+acl2-par').  As of
 this writing, the maintenance of these systems has typically been performed by
 Kaufmann and Moore when reasonably feasible, but sometimes with assistance
 from Gamboa and Rager, especially when there is a major change.</p>

 <p>Note that ACL2(r) changes the logic &mdash; for example, the formula
 @('(not (equal (* x x) 2))') is a theorem of ACL2 but is disprovable in
 ACL2(r) &mdash; but ACL2(p) does not change the logic.  Another difference is
 that ACL2(r) was intended, as a design decision, to be sound; by contrast,
 ACL2(p) was intended to be sound in practice but with a small risk that an
 unsound result could be obtained.</p>

 <p>There is a somewhat elaborate mechanism for incorporating ACL2(p) source
 code into the ACL2 sources.  One part involves the use of feature
 @(':acl2-par'): that is, the use of @('#+acl2-par') to prefix code to be read
 only when building ACL2(p) and of @('#-acl2-par') to prefix code to be read
 only when building ACL2.  But there is also support for function and macro
 names with suffix @('\"@PAR\"').  When considering ACL2 and not ACL2(p), these
 should be read simply by removing that suffix: for example, @('defun@par') is
 to be read as @('defun'), @('er@par') is to be read as @('er'), and so on.
 For information about how to make sense of the @('\"@PAR\"') suffix when
 reading the sources as ACL2(p) sources, see the Essay on Parallelism,
 Parallelism Warts, Parallelism Blemishes, Parallelism No-fixes, Parallelism
 Hazards, and #+ACL2-PAR notes.  Several definitions near the end of
 @('axioms.lisp'), below mention of that essay, implement the handling of
 @('\"@PAR\"') suffixes.</p>

 <p>At one time, the addition of hash-cons, function memoization, and
 fast-alists (see @(see hons-and-memoization)) was considered experimental, and
 resulted in a system called ACL2(h) with a corresponding readtime conditional
 of @('#+hons').  That system, which was originally built on top of ACL2 by Bob
 Boyer and Warren Hunt and was updated by Jared Davis and Sol Swords, with
 contributions by Matt Kaufmann and J Moore, was ultimately updated and
 incorporated into ACL2 by Kaufmann and Moore after an extensive code review.
 Since Kaufmann and Moore now stand behind the resulting system and are
 maintaining it, and with assent from its contributors, what was formerly
 ACL2(h) is now just ACL2.</p>

 <p>NEXT SECTION: @(see developers-guide-extending-knowledge)</p>")

(defxdoc developers-guide-extending-knowledge
  :parents (developers-guide)
  :short "Illustration using tracing, comments and Essays to explore ACL2 behaviors"
  :long "<p>This topic grew out of a discussion on the acl2-devel mailing list
 in which some relevant background had already been presented.  It illustrates
 how one might go about learning about specific features of ACL2, in this case
 aspects of the @(see tau-system).</p>

 <p>First,</p>

 @({
 (include-book ``tau/bounders/elementary-bounders'' :dir :system)
 })

 <p>and</p>

 @({
 (trace$ tau-term)
 })

 <p>and then submit the non-theorem:</p>

 @({
 (thm (implies (and (natp x)(<= 0 x) (<= x 15))
               (equal xxx (+ 3 x))))
 })

 <p>The objective is to see what the tau of @('(+ 3 x)') is, under the
 assumptions @('(and (natp x) (<= 0 x) (<= x 15))').  The idea is to attempt to
 prove a non-theorem that lists the assumptions being made and then to see how
 the ACL2 source function, @('tau-term'), is called on the term in question and
 what @('tau-term') returns.  (We assume here the somehow we know that
 @('tau-term') is relevant, perhaps by querying the acl2-devel mailing list.)
 First let's consider what it returns because that gives us a chance to see a
 tau object.  Then we'll explore how @('tau-term') was called.</p>

 <p>If you search the failed proof for the first call of @('tau-term') on
 @('(binary-+ '3 x)') &mdash; which is the translated form of @('(+ 3 x)') (see
 @(see term)) &mdash; and look at what that call returns, you see:</p>

 @({
   <2 (TAU-TERM ((NIL)
                 (INTEGERP (NIL . 3) NIL . 18)
                 ((166 . FILE-CLOCK-P)
                  (155 . 32-BIT-INTEGERP)
                  (20 . O-FINP)
                  (19 . POSP)
                  (17 . NATP)
                  (9 . EQLABLEP)
                  (5 . RATIONALP)
                  (4 . INTEGERP)
                  (0 . ACL2-NUMBERP))
                 (192 . BAD-ATOM)
                 (182 . ZPF)
                 (176 . WRITABLE-FILE-LISTP1)
                 (173 . READ-FILE-LISTP1)
                 (170 . WRITTEN-FILE)
                 (167 . READABLE-FILE)
                 (163 . OPEN-CHANNEL1)
                 (137 . KEYWORDP)
                 (129 . LOWER-CASE-P)
                 (128 . UPPER-CASE-P)
                 (127 . ALPHA-CHAR-P)
                 (124 . STANDARD-CHAR-P)
                 (118 . IMPROPER-CONSP)
                 (117 . PROPER-CONSP)
                 (104 . WEAK-ABSSTOBJ-INFO-P)
                 (72 . WEAK-CURRENT-LITERAL-P)
                 (34 . WEAK-IO-RECORD-P)
                 (31 . BOOLEANP)
                 (27 . MINUSP)
                 (18 . BITP)
                 (16 . ZIP)
                 (15 . ZP)
                 (7 . SYMBOLP)
                 (6 . STRINGP)
                 (3 . CONSP)
                 (2 . COMPLEX-RATIONALP)
                 (1 . CHARACTERP))
                ...)
 })

 <p>The @('...') above is the second returned value of @('tau-term'), which is
 the ``tau completion alist'', an efficiency hack that we'll ignore here.  The
 first result returned is the tau of @('(+ 3 x)') under our assumptions.</p>

 <p>You can decode it with @('(decode-tau <tau> <term>)') where @('<tau>') is a
 tau and @('<term>') is a term that allegedly has that tau (i.e., has that
 ``type'').</p>

 @({
 (decode-tau '((NIL)
               (INTEGERP (NIL . 3) NIL . 18)
               ((166 . FILE-CLOCK-P)
                (155 . 32-BIT-INTEGERP)
                (20 . O-FINP)
                (19 . POSP)
                (17 . NATP)
                (9 . EQLABLEP)
                (5 . RATIONALP)
                (4 . INTEGERP)
                (0 . ACL2-NUMBERP))
               (192 . BAD-ATOM)
               (182 . ZPF)
               (176 . WRITABLE-FILE-LISTP1)
               (173 . READ-FILE-LISTP1)
               (170 . WRITTEN-FILE)
               (167 . READABLE-FILE)
               (163 . OPEN-CHANNEL1)
               (137 . KEYWORDP)
               (129 . LOWER-CASE-P)
               (128 . UPPER-CASE-P)
               (127 . ALPHA-CHAR-P)
               (124 . STANDARD-CHAR-P)
               (118 . IMPROPER-CONSP)
               (117 . PROPER-CONSP)
               (104 . WEAK-ABSSTOBJ-INFO-P)
               (72 . WEAK-CURRENT-LITERAL-P)
               (34 . WEAK-IO-RECORD-P)
               (31 . BOOLEANP)
               (27 . MINUSP)
               (18 . BITP)
               (16 . ZIP)
               (15 . ZP)
               (7 . SYMBOLP)
               (6 . STRINGP)
               (3 . CONSP)
               (2 . COMPLEX-RATIONALP)
               (1 . CHARACTERP))
             '(binary-+ '3 x))
 })

 <p>If @('(tau-term <term> ...<assumptions>...)') returns @('<tau>'), then
 @('(decode-tau <tau> <term>)') prints out everything the tau system can deduce
 about @('<term>') under those @('<assumptions>').  It's a way of asking ``what
 does this @('<tau>') mean?''  The answer is shown below, where the three
 important facts have been indicated:</p>

 @({
 (AND (ACL2-NUMBERP (BINARY-+ '3 X))
      (INTEGERP (BINARY-+ '3 X))                 ; <---
      (RATIONALP (BINARY-+ '3 X))
      (EQLABLEP (BINARY-+ '3 X))
      (NATP (BINARY-+ '3 X))
      (POSP (BINARY-+ '3 X))
      (O-FINP (BINARY-+ '3 X))
      (32-BIT-INTEGERP (BINARY-+ '3 X))
      (FILE-CLOCK-P (BINARY-+ '3 X))
      (<= 3 (BINARY-+ '3 X))                     ; <---
      (<= (BINARY-+ '3 X) 18)                    ; <---
      (NOT (CHARACTERP (BINARY-+ '3 X)))
      (NOT (COMPLEX-RATIONALP (BINARY-+ '3 X)))
      (NOT (CONSP (BINARY-+ '3 X)))
      (NOT (STRINGP (BINARY-+ '3 X)))
      (NOT (SYMBOLP (BINARY-+ '3 X)))
      (NOT (ZP (BINARY-+ '3 X)))
      (NOT (ZIP (BINARY-+ '3 X)))
      (NOT (BITP (BINARY-+ '3 X)))
      (NOT (MINUSP (BINARY-+ '3 X)))
      (NOT (BOOLEANP (BINARY-+ '3 X)))
      (NOT (WEAK-IO-RECORD-P (BINARY-+ '3 X)))
      (NOT (WEAK-CURRENT-LITERAL-P (BINARY-+ '3 X)))
      (NOT (WEAK-ABSSTOBJ-INFO-P (BINARY-+ '3 X)))
      (NOT (PROPER-CONSP (BINARY-+ '3 X)))
      (NOT (IMPROPER-CONSP (BINARY-+ '3 X)))
      (NOT (STANDARD-CHAR-P (BINARY-+ '3 X)))
      (NOT (ALPHA-CHAR-P (BINARY-+ '3 X)))
      (NOT (UPPER-CASE-P (BINARY-+ '3 X)))
      (NOT (LOWER-CASE-P (BINARY-+ '3 X)))
      (NOT (KEYWORDP (BINARY-+ '3 X)))
      (NOT (OPEN-CHANNEL1 (BINARY-+ '3 X)))
      (NOT (READABLE-FILE (BINARY-+ '3 X)))
      (NOT (WRITTEN-FILE (BINARY-+ '3 X)))
      (NOT (READ-FILE-LISTP1 (BINARY-+ '3 X)))
      (NOT (WRITABLE-FILE-LISTP1 (BINARY-+ '3 X)))
      (NOT (ZPF (BINARY-+ '3 X)))
      (NOT (BAD-ATOM (BINARY-+ '3 X))))
 })

 <p>Another way of thinking about a tau, @('<tau>'), is that it is a reasonably
 fast and compact encoding of a predicate,</p>

 @({
 `(lambda (zzz) ,(decode-tau <tau> 'zzz))
 })

 <p>Of course, a tau is very redundant.  There is no reason to say that
 something's NOT a bad-atom if you say it IS a NATP!  But by encoding
 everything the tau system knows about a term it's easy to answer questions
 about what we know.</p>

 <p>Now, going back to that call of @('tau-term') on @('(binary-+ '3 x)') in
 the trace, it was:</p>

 @({
  (TAU-TERM '(BINARY-+ '3 X)
            <tau-alist>
            '(((EQUAL (BINARY-+ '3 X) XXX)              ; type-alist
               128
               (LEMMA (:FAKE-RUNE-FOR-TYPE-SET NIL)))
              ((< '15 X) 128)
              ((< X '0) 128)
              (X 7)
              (X 23))
            '(((0 (((((X . -1)) NIL) 15 <= T)))         ; linear pot list
               X (((((X . 1)) NIL) 0 <= T))))
            <ens>
            <w>
            <calist>)
 })

 <p>Let's assume that we already know about the @(see type-alist) and the
 linear pot (see @(see linear-arithmetic)); they're set up when
 @('tau-clausep') is called, by assuming all the literals of the clause false
 and doing the initialization of the linear data base.</p>

 <p>The @('<tau-alist>') basically repeats as much of that information as
 possible in terms of tau.  That is, it records the known tau of various terms
 computed so far by @('tau-clause1p').  It starts as @('nil') in
 @('tau-clausep').</p>

 <p>When playing with @('tau-term'), it is OK to just set @('tau-alist') to
 @('nil').  If a term is on the @('tau-alist') and you ask for its tau,
 @('tau-term') just returns the tau in the alist.  But if the term isn't on the
 alist, @('tau-term') computes it.  So generally speaking, the @('tau-alist')
 just saves time.  Since the tau system is complicated it could be that putting
 an entry on the alist that tau can compute will cause @('tau-term') to compute
 a stronger tau for that term, but this is unlikley.  In any case, a good
 approximation and a perfectly sound way to use tau is to just set
 @('tau-alist') to @('nil')!</p>

 <p>It is also acceptable to use @('nil') for @('<calist>') in calls of
 @('tau-term').</p>

 <p>The general lesson here is simple: if you want to try to understand some
 part of the prover, @(tsee trace$) it and give the prover a formula that will
 exercise the part in question and look at how it's called and what it
 returns.</p>

 <p>Of course, you can also read the comments!  There is a good essay on the
 tau system that is well worth reading if you're interested.</p>

 @({
 ; Essay on the Tau System

 ; This essay touches on a wide variety of topics in the design of the tau
 ; system.  It is consequently divided into many subsections with the following
 ; headers.  We recommend scanning this list for subsections of interest; an
 ; introduction to tau is provided by the first six or so, in order.

 ; On Tau-Like Terms
 ; On the Name ``tau''
 ; On Some Basic Ideas
 ; On Tau Recognizers -- Part 1
 ; On the Tau Database and General Design
 ; On Tau Recognizers -- Part 2
 ; On Tau Intervals and < versus <=
 ; On the Tau Data Structure
 ; On the Built-in Tau and the Abuse of Tau Representation
 ; On the Additional Restrictions on Tau Fields
 ; On the Use of ENS by Function Evaluation in the Tau System
 ; On the Most Basic Implications of Being in an Interval
 ; On Firing Signature Rules
 ; On Comparing Bounds
 ; On the Proof of Correctness of upper-bound-<
 ; On the Near-Subset Relation for Intervals
 ; On the Tau Database
 ; On Closing the Database under Conjunctive Rules
 ; On Converting Theorems in the World to Tau Rules
 ; On Tau-Like Terms
 ; On Loops in Relieving Dependent Hyps in Tau Signature Rules
 ; On the Tau Msgp Protocol
 ; On Removal of Ancestor Literals -- The Satriani Hack Prequel
 ; On the Motivation for Tau-Subrs
 ; On the Tau Completion Alist (calist)
 ; On Disjoining Tau
 ; On the Role of Rewriting in Tau
 ; On Tau-Clause -- Using Tau to Prove or Mangle Clauses
 ; On Tau Debugging Features
 })

 <p>NEXT SECTION: @(see developers-guide-build)</p>")

(defxdoc developers-guide-background-extra
  :parents (developers-guide-background)
  :short "Some Implementation Background Extra Information"
  :long "<p>Here is a call tree built bottom-up when exploring how @('thm-fn')
 calls the rewriter, which is an exercise suggested in the section, @(see
 developers-guide-background).  There are a few extra nodes in this tree,
 obtained by looking for callers of @('rewrite') and of @('prove').</p>

 @({
 rewrite
   rewrite-atm
     rewrite-clause, rewrite-clause-lst
       simplify-clause1
         simplify-clause
           waterfall-step1
             waterfall-step
               waterfall0
                 waterfall1
                   waterfall
                     prove-loop2
                       prove-loop1
                         prove-loop0
                           prove-loop
                             prove
                               prove-termination
                               prove-guard-clauses
                               #+:non-standard-analysis verify-valid-std-usage
                               prove-corollaries1
                               defthm-fn1
                                 defthm-fn
                               thm-fn
                               prove-defattach-guards1
                               prove-defattach-constraint
                             pc-prove
   mfc-rw-raw
   pc-rewrite*-1
 })")

(defxdoc developers-guide-build
  :parents (developers-guide)
  :short "Building ACL2 Executables"
  :long "<p>Building an ACL2 executable is easy: one simply submits `@('make')'
 in the top-level ACL2 directory.  Here we say a few words about how that works
 and comment on some variants.</p>

 <h3>Building with `@('make')'</h3>

 <p>The preceding chapter (see @(see developers-guide-background)) notes five
 or six different Lisps on which ACL2 may be built.  <color rgb='#c00000'>There
 have been occasions when an ACL2 bug only showed up with one of those Lisps;
 so, it is a good idea to build ACL2 in each of them from time to time, when
 feasible.</color> Just specify @('LISP') on the command line, typically with
 @('PREFIX') specified as well, which is put on the front of @('saved_acl2').
 For example, to build ACL2 in SBCL, you might issue the following shell
 command to create an SBCL-based ACL2 executable named
 @('sbcl-saved_acl2').</p>

 <color rgb='#c00000'>
 @({
 (make PREFIX=sbcl- LISP=sbcl) >& make-sbcl.log&
 })
 </color>

 <color rgb='#800080'>
 <p>DEMO: make-acl2 [alias].</p>
 </color>

 <p>Check the log to see if the build seems to have completed normally, in
 particular with ``Initialization SUCCEEDED'' printed near the end of the log.
 It is a good idea to do case-insensitive searches for the string,
 \"compiler\", if the Lisp is CCL (you should find four occurrences, all of
 them for SET-COMPILER-ENABLED) and for \"warning:\" for the other Lisp
 implementations (you should find no occurrences except in GCL, pertaining to
 ``trace'').</p>

 <p>Let us now provide some analysis of what the invocation of `@('make')' is
 doing.  If you inspect @('GNUmakefile'), you may see these two lines:</p>

 @({
 # Top (default) target:
 all: large
 })

 <p>Thus, ``@('make')'' is really ``@('make all')'', which is mostly ``@('make
 large')''.  (There was formerly a way to build smaller executables, but no
 longer.)  That target, in turn, is defined as follows.</p>

 @({
 large: acl2r full init
 })

 <p>Let's briefly consider each of the three targets above.  For details, read
 @('GNUmakefile'), which is intended to be comprehensible.</p>

 <ul>

 <li>The @('acl2r') target just generates a file @('acl2r.lisp') that is loaded
 in to Lisp at start up by the other two targets.  It defines features that
 support readtime conditionals during the build process.  For example, by
 default that file contains the form @('(push :hons *features*)'), so that
 forms prefixed by @('#+hons') are read while those prefixed by @('#-hons') are
 ignored.</li>

 <li>The @('full') target compiles source files when compilation is indicated.
 Compilation is skipped for host Lisps CCL and SBCL because those Lisps compile
 on-the-fly, hence there is no clear advantage to compiling the source
 files.</li>

 <li>The @('init') target generates a call of @('initialize-acl2'), which
 constructs the initial @(see world) &mdash; the so-called ``boot-strap world''
 &mdash; by running @(tsee ld) on ACL2 source files.</li>

 </ul>

 <p>Not surprisingly, there are many details that we omit here.  We expect ACL2
 developers to be able to follow the source code and @('GNUmakefile') where
 they lead when it is important to understand details.</p>

 <h3>Debugging a failed build</h3>

 <p>When a build fails using ``@('make')'', you can generally re-create the
 failure in an interactive session as follows, so that you can use the Lisp
 debugger to investigate.  First, look for a file ``@('workxxx')'' in the build
 directory.  It should contain the forms that were executed in Lisp to get to
 the error.  So, start Lisp, and then execute each of those forms until you get
 to the error &mdash; it's as simple as that!  (Of course, the debugging that
 ensues may be simple or complex.)</p>

 <h3>Documentation</h3>

 <color rgb='#800080'>
 <p>DEMO: make-doc [alias] COVERS WHAT'S BELOW.</p>
 </color>

 <p>The generated file @('doc.lisp') can be built in the ACL2 sources directory
 by invoking @('make DOC') or @('make update-doc.lisp').  These each will build
 that file in the ACL2 sources directory, which in turn supports the use of
 @(':doc') at the terminal without the need to include books.  The way that
 works is as follows: @('doc.lisp') is generated from
 @('books/system/doc/acl2-doc.lisp'), and then @('doc.lisp') is processed with
 @(tsee ld) as an ACL2 source file to populate the appropriate documentation
 database.  That database consists of the alist,
 @('*acl2-system-documentation*'), whose keys are the built-in documented
 topics.</p>

 <p>Warning: If there are functions, macros, or constants that are keys of
 @('*acl2-system-documentation*') but do not belong to the constant
 @('*acl2-exports*'), then the community book
 @('books/misc/check-acl2-exports.lisp') will probably fail to certify.  So
 whenever @('doc.lisp') is regenerated, it is a good idea to recertify that
 book after deleting its @('.cert') file.</p>

 <h3>Untouchables etc.</h3>

 <p>Note that during the build, ACL2 does not enforce its usual restrictions
 against using @(see untouchable)s or utilities in the list
 @('*ttag-fns-and-macros*').  Be careful!  Those restrictions are in place
 because their use can destroy the integrity of an ACL2 session.  As
 developers, we can't be hampered by such restrictions, but in return for this
 freedom we take responsibility for wise usage.</p>

 <h3>Build-time proofs</h3>

 <p>ACL2 has the ability to ``prove its way through'' some of its source code.
 Most proofs are skipped by default.  To do such proofs, run `<color
 rgb='#c00000'><tt>make proofs</tt></color>', which should be done only after
 compiling the sources if that would normally be done for the host Lisp that is
 being used.  To be safe it might be best to build ACL2 first the normal way,
 even if CCL or SBCL is being used and hence sources aren't subjected to
 @('compile-file').</p>

 <h3>Proving termination and guards in books: Making a ``devel'' build</h3>

 <color rgb='#800080'><p>[JUST TOUCH ON THIS SECTION]</p></color>

 <p>Just above, we talk about doing proofs during the build.  That is an
 admirable thing to do, but it can be difficult to carry out certain proofs,
 for at least two reasons: the build environment is not interactive, and there
 is no way to include helpful books during the build.  Fortunately, there is a
 procedure for deferring those proofs until after the build is complete.  The
 documentation topic @(see verify-guards-for-system-functions) provides
 details.  <color rgb='#c00000'>However, after you have some familiarity with
 this procedure you might prefer to follow a script given as a comment in
 @('*system-verify-guards-alist*').</color></p>

 <p>NEXT SECTION: @(see developers-guide-maintenance)</p>")

(defxdoc developers-guide-maintenance
  :parents (developers-guide)
  :short "Modifying, Testing, and Debugging"
  :long "<color rgb='#c00000'><p>Before working on changes to ACL2, consider
 sending email to the acl2-devel list (@('acl2-devel@utlists.utexas.edu')),
 explaining what you have in mind.  This will avoid duplication and also
 provide an opportunity for feedback.  In particular, you may want to wait for
 confirmation from Kaufmann or Moore that at least one of them will be willing
 to review your patch; otherwise they make no commitment to do so, and your
 efforts might be wasted!</p></color>

 <p>Please try to limit your modifications to those that are directly related
 to what you intend to change.  For example, please don't delete comments in a
 source file or a book.  (If you feel moved to do so, at least first check with
 an author of the file you propose to change.)  That said, it's certainly it's
 fine to fix typos.</p>

 <p>Detailed steps for making a contribution are outlined in the topic, @(see
 developers-guide-contributing).</p>

 <h3>Development</h3>

 <color rgb='#c00000'>
 <p>The first step towards changing ACL2 is typically to create a patch file,
 which here we call @('patch.lisp').  It will typically have the following
 shape.</p>
 </color>

 @({
 ;;; Github commit hash as of your starting ACL2 version (see below)

 ;;; Comments at the top (perhaps an email thread with a request for the
 ;;; change)

 (redef+)

 <your code>

 (redef-)
 (reset-prehistory) ; optional
 })

 <p>The reason to record the github commit hash is so that Kaufmann and Moore
 can correctly merge in your changes even after there have been several ACL2
 commits.  You can get that hash by running the following command under the
 main ACL2 directory.</p>

 @({
 git rev-parse HEAD
 })

 <p>Next, start copying into @('patch.lisp') the source functions that you want
 to modify.  (As already noted, it is helpful for this process to use
 @('meta-.') in Emacs.)  It is often best to keep the functions in order: if
 @('f') calls @('g') and both are defined (or redefined) in @('patch.lisp'),
 then the definition of @('g') should precede the definition of @('f') in
 @('patch.lisp').</p>

 <p>Now modify those source functions and write any additional supporting
 functions that you need.  Try to use existing source functions when possible.
 perhaps finding them by using the Emacs command, @('meta-x tags-apropos').
 For example, to find a function that concatenates a list of strings, you could
 run @('meta-x tags-apropos append') and then search for @('string') in the
 resulting display; you would find @('string-append-lst'), and you could run
 the Emacs command @('meta-.') on that word in order to find its definition in
 the sources, to see if it has the desired functionality.  You may also find it
 useful to consult the documentation topic, @(see system-utilities).</p>

 <p>If there are further changes that you wish to make to the ACL2 source code
 which are not of the form of function definitions or redefinitions &mdash; for
 example, if you want to add or modify a top-level comment, or put some of the
 new functions in a particular file or a newly created file, etc. &mdash; then
 feel free to add instructions that reflect your intent in comments in
 @('patch.lisp'), within reason.  We will be reading over @('patch.lisp')
 manually, so human-directed comments are welcome &mdash; the exact format of
 @('patch.lisp') is not rigid.</p>

 <h3>Initial testing</h3>

 <p>Test your patch by starting ACL2 and evaluating the following form in the
 loop (but see below for an exception).  The use of @(':ld-pre-eval-print') is
 optional, but can be helpful when debugging since it prints each form before
 evaluating it.</p>

 @({
 (ld \"patch.lisp\" :ld-pre-eval-print t)
 })

 <color rgb='#c00000'>
 <p>EXCEPTION: the form above may not work if your patch file has any
 occurrences of the @('acl2-loop-only') readtime conditional (preceded either
 by @('#+') or by @('#-')).  In that case, run @('LP!') as follows.  NOTE: if
 you are making changes that affect definition processing, then you may need to
 switch the order: first @('load'), then after @('(LP!)'), run @('ld').</p>
 </color>

 @({
 :q
 (LP!)
 (ld \"patch.lisp\" :ld-pre-eval-print t)
 :q
 (load \"patch.lisp\") ; only needed if #-acl2-loop-only occurs in patch.lisp
 (LP)
 })

 <p>Remark (only rarely to be considered).  If efficiency is a concern and you
 are using a Lisp implementation that does not compile on-the-fly (as of this
 writing, that includes Lisps other than CCL and SBCL), then put
 @('(set-compile-fns t)') near the top of @('patch.lisp'), and replace @('(load
 \"patch.lisp\")') just above by the following (perhaps first adding
 @('(in-package \"ACL2\")') at the top of @('patch.lisp')):</p>

 @({
 (load \"patch.lisp\")
 (compile-file \"patch.lisp\")
 (load \"patch\")
 })

 <p>Now test your patch.  A quick test could be the following.</p>

 @({
 (mini-proveall) ; should complete normally
 (ubt! 1) ; back to just after reset-prehistory was evaluated
 })

 <p>You might also want to do your own tests.  In some cases, you could even
 add a book of tests in directory @('books/system/tests/').  If the change was
 inspired by problems with a specific event in an existing book, the following
 can be useful.</p>

 @({
 (ld \"foo.port\")
 (rebuild \"foo.lisp\" t)
 :ubt <bad-event-name>
 <bad-event>
 })

 <h3>Installing and building</h3>

 <p>When you are satisfied that all is well, take your copy of ACL2 and install
 the patches: for each system function redefined in patch.lisp, replace the
 definition in your copy of the ACL2 sources with the redefinition, preceded by
 new supporting definitions as necessary.  Then in your acl2-sources directory,
 build the system; see @(see developers-guide-build).</p>

 <color rgb='#c00000'>
 <p>Since ACL2 insists that functions, macros, and constants are introduced
 before they are referenced, you might need to move some definitions around.
 You might even need to move then to ``earlier'' files (see @(see
 developers-guide-background)).  This is normal.  Although a file name like
 ``@('rewrite.lisp')'' is suggestive of its contents, and ideally the file
 contains code that reflects the intent of the filename, nevertheless this is
 not a rule; ACL2 implementors often need to move definitions forward in
 support of other functions.</p>
 </color>

 <p>The following two additional steps are occasionally advisable, especially
 for patches that change definitions that are in @(':')@(tsee logic) mode.
 Feel free to ask an ACL2 author if they are necessary; as of this writing,
 that would be Matt Kaufmann, at @('kaufmann@cs.utexas.edu').</p>

 <ul>

 <li>Run ``@('make proofs')''.  That should conclude with the message,
 ``Initialization SUCCEEDED.''</li>

 <li>Do a ``devel'' build, regression, and check.  See @(see
 verify-guards-for-system-functions), specifically the six steps at the end of
 the topic.</li>

 </ul>

 <h3>Regression testing</h3>

 <p>Now do a regression test.  The most complete regression is done using the
 @('regression-everything') target in the top-level ACL2 sources directory, or
 equivalently, the @('everything') target in the @('books/') directory.  Please
 install a SAT solver first; see @(see satlink::sat-solver-options).</p>

 <p>Note that the ``@('everything')'' level of testing may only work for CCL
 and SBCL; for other Lisps, or for ACL2(p) or ACL2(r), just use the
 @('regression') target in the top-level ACL2 sources directory or,
 equivalently, the @('all') target in the @('books/') directory.  This could
 take a few hours &mdash; perhaps more than 5 hours or even more than 8 hours,
 depending on the Lisp and the machine.  But feel free to do only an
 @('everything') regression for ACL2 using CCL or SBCL, ignoring ACL2(p) and
 ACL2(r).</p>

 @({
 make clean-books ; \\
 (time nice make -j 8 regression-everything) >& make-regression-everything.log&
 })

 <p>A search for @('**') in the log will determine whether there have been any
 failures; equivalently, in most cases, a failure has occurred when there is a
 non-zero exit status.</p>

 <p><color rgb='#c00000'>It is a good idea to keep a record of the time it
 takes to complete a regression</color> using a given host Lisp and a given
 value for the @('-j') argument of `@('make')'.  If there is a jump of more
 than a percent or two that is not attributable to book changes, then perhaps
 the change is degrading performance.  Of course, that time increase could be
 noise; we have observed significantly more reliable timings, for example, on
 Linux than on Mac.  There are wonderful tools @('books/build/critpath.pl') and
 @('books/build/compare.pl') for narrowing time increases to the level of
 individual books, which you can investigate interactively, for example using
 profiling; see @(see profile-acl2) and @(see profile-all).  (Also, Allegro CL
 has a particularly nice statistical profiler.)  Here is the first step, to be
 run in two ACL2 directories, @('DIR1') and @('DIR2'), that you want to compare
 after having run a regression test in each.</p>

 @({
 cd books
 find . -name '*.cert.time' -print | sed 's/[.]time$//' | sort > certs.txt
 ./build/critpath.pl -t certs.txt --write-costs timingfile > timing.txt
 })

 <p>Then run the following command anywhere, which produces a file
 @('compare.txt') showing results, sorted two different ways.</p>

 @({
 <path_to_acl2>/books/build/compare.pl \\
   DIR1/books/timingfile \\
   DIR2/books/timingfile > compare.txt
 })

 <h3>Documentation</h3>

 <color rgb='#800080'><p>[JUST TOUCH ON THIS SECTION]</p></color>

 <p>Be sure to document your changes.  This will typically involve adding a
 release note to a topic like @(see note-8-2).  The XDOC source code
 documentation for ACL2 resides in the community book
 @('books/system/doc/acl2-doc.lisp').  If the change is not user visible, then
 a Lisp comment in the corresponding @('defxdoc') form is probably best; the
 existing @('(defxdoc note-xxx ...)') forms can provide guidance on this.
 Minor output changes don't generally require any release note.  Be sure to
 keep the @(see XDOC) documentation at a user level, not at the level of the
 implementation.  Note that it is good practice to explain your changes as
 noted above &mdash; that is, in the text or comments of a @(tsee defxdoc)
 release note form &mdash; rather than merely in GitHub commit messages.
 Every user should be able to find changes documented in the release notes, and
 every developer should additionally be able to find pertinent Lisp comments;
 neither will necessarily look back in GitHub logs (some may, but some may
 not).</p>

 <p>Also be sure to comment your code well with Lisp comments, at an
 implementation level.  For example, don't say ``union is commutative'' without
 explaining that you mean this with respect to set equality, not
 ordinary (Lisp) equality.</p>

 <p>Whoever actually commits and pushes to github &mdash; just Kaufmann and
 Moore as of this writing, but ideally others in the future &mdash; should also
 synchronize generated ACL2 source file @('doc.lisp') (see @(see
 developers-guide-build)) with @('books/system/doc/acl2-doc.lisp').</p>

 <p>When you add new documentation in community book
 @('books/system/doc/acl2-doc.lisp') for a symbol that is the name of a
 function, macro, or constant, there is a check in the community book
 @('books/misc/check-acl2-exports.lisp') that the symbol belongs to the list,
 @('*acl2-exports*').  Rather than add the symbol immediately to that list,
 however, it may be best to override the check for that symbol, as indicated in
 the definition of the constant, @('*acl2-exports-exclusions*'), in
 @('books/misc/check-acl2-exports.lisp').  The reason for this delay is that if
 you change @('*acl2-exports*'), many books may need to be recertified, which
 could be inconvenient for users.  This issue is documented in the definition
 of the constant @(tsee *acl2-exports*); see the ``WARNING'' comment there.</p>

 <h3>Debugging</h3>

 <color rgb='#800080'><p>[JUST TOUCH ON THIS SECTION]</p></color>

 <p>The art of debugging is... an art.  Some tools that can help with debugging
 are @(tsee trace$), @(tsee trace!), @(tsee break-on-error), @(tsee
 set-debugger-enable), @(tsee walkabout), @(see iprinting), and (rarely) @(tsee
 disassemble$).  Also see @(see debugging).</p>

 <p>A common way to debug an unexpected error is to invoke
 @('(set-debugger-enable t)') and @('(break-on-error)').  This may put you in
 the debugger when there is an error.  Each host Lisp has its own debugger
 commands for looking at the backtrace; for example, in CCL the command is
 @(':b'), while in SBCL it is @('backtrace').  CCL's debugger lets you easily
 explore individual forms in the backtrace.  <color rgb='#c00000'>Here is an
 edited log showing how that works.</color></p>

 @({
 ACL2 !>(defun f (x) (declare (xargs :mode :program)) (car x))

 Summary
 Form:  ( DEFUN F ...)
 Rules: NIL
 Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)
  F
 ACL2 !>(set-debugger-enable t)
 <state>
 ACL2 !>(f 3)

 > Error: Fault during read of memory address #x1D
 > While executing: F, in process listener(1).
 > Type :GO to continue, :POP to abort, :R for a list of available restarts.
 > If continued: Skip evaluation of (acl2::acl2-default-restart)
 > Type :? for other options.
 1 > :b
 *(25819710) : 0 (F 3) 16
  (25819770) : 1 (RAW-EV-FNCALL F (3) ('3) ((STATE . ACL2_INVISIBLE::|The Live State Itself|)) ((COMMAND-LANDMARK GLOBAL-VALUE 7662 # \"/Users/kaufmann/acl2/acl2-git-scratch/books/system/doc/\") (EVENT-LANDMARK GLOBAL-VALUE 9539 DEFUN F ...) (F ABSOLUTE-EVENT-NUMBER . 9539) (CLTL-COMMAND GLOBAL-VALUE DEFUNS :PROGRAM NIL ...) (TOP-LEVEL-CLTL-COMMAND-STACK GLOBAL-VALUE #) ...) NIL NIL T) 1253
  (25819840) : 2 (EV (F '3) ((STATE . ACL2_INVISIBLE::|The Live State Itself|)) ACL2_INVISIBLE::|The Live State Itself| ((STATE . ACL2_INVISIBLE::|The Live State Itself|)) NIL T) 357

 <<... etc. ...>>

  (25819F98) : 21 (FUNCALL #'#<(:INTERNAL CCL::THREAD-MAKE-STARTUP-FUNCTION)>) 277
 1 > (:form 1) ; show the form labeled with 1 in the backtrace
 (RAW-EV-FNCALL 'F '# '# '# ...)
 1 > (walkabout (unquote (nth 5 *)) state) ; world

 Commands:
 0, 1, 2, ..., nx, bk, pp, (pp n), (pp lev len), =, (= symb), and q.

 ((COMMAND-LANDMARK GLOBAL-VALUE 7662 ...)
  (EVENT-LANDMARK GLOBAL-VALUE 9539 ...)
  (F ABSOLUTE-EVENT-NUMBER . 9539)
  ...)
 :
 })

 <p>Some problems are, of course, more awkward to debug.  One that pops up from
 time to time is an error like this.</p>

 @({
    > Error: value NIL is not of the expected type NUMBER.
    > While executing: CCL::+-2, in process listener(1).
 })

 <p>That particular sort of error may indicate that the @('state') argument of
 some function was passed incorrectly, perhaps in the wrong argument
 position.</p>

 <p>In rare cases an error may occur for which the backtrace isn't helpful or
 even makes little sense.  Something to try is to build with safety 3, for
 example as follows.</p>

 @({
 make ACL2_SAFETY=3 PREFIX=safety-3-
 })

 <p>If your test case involves including books, then also clean the books or
 use @(tsee set-compiler-enabled) to avoid loading their compiled files.  Then
 try again with the new executable; of course, if you cleaned the books, then
 first recertify as appropriate using the new executable.  ACL2 will run more
 slowly, but in return it will do a lot more checking along the way and might
 well provide a much better backtrace than before.</p>

 <p>If you are reading this and have more debugging suggestions, by all means
 consider adding them here!</p>

 <h3>Finishing up</h3>

 <p>Now feel free to send all changed files and also the starting git commit
 hash (or even the entire patch file, too) for review, to whoever has offered
 to look at your patch!  Some day others besides Kaufmann and Moore may be
 authorized to commit and push source code changes directly to GitHub; but
 getting someone else to review the changes could still be a good thing to
 do.</p>

 <p>When you are ready to have your patch incorporated into ACL2, follow the
 detailed steps for making a contribution outlined in the topic, @(see
 developers-guide-contributing).</p>

 <h3>General guidance</h3>

 <p>We close this chapter with some relevant tips and observations, some of
 which may also be found elsewhere in this Guide.</p>

 <ul>

 <li><color rgb='#c00000'>Small examples help when testing new features or bug fixes.</color>  For a bug fix
 it is important to have an example that exhibits the bug, both to guarantee
 that there really is a problem and to use to test your patch.  Ideally the
 example will be small, as this is useful for reading the output from tracing
 functions or debugger backtraces, and small examples are often helpful for
 understanding the problem.  Consider adding one or more relevant tests to
 @('books/system/tests/') or perhaps, if appropriate, @('books/demos/').</li>

 <li><color rgb='#c00000'>Often it is best to avoid making a more sweeping change than necessary,
 instead waiting for users to complain.</color>  This process has several advantages:
 it avoids needless code complications; the user's complaint may help to inform
 the nature of the additional changes; and it may take significantly less time
 to complete the implementation, especially if there is a simple fix that is
 clearly correct and solves the problem.</li>

 <li><color rgb='#c00000'>Look for precedents</color>, since new code is probably more likely to be correct
 to the extent it is analogous to existing code.  ACL2 is a complex system with
 invariants that are not always explicit, so to the extent that you can follow
 the existing implementation of some feature, you may avoid introducing bugs or
 undesirable behavior.  For example, if you want to add a new key to the @(tsee
 acl2-defaults-table), find an existing such key and do a tags-search for it,
 and mimic the implementation of that existing key to the extent it makes
 sense.  Try to pick a key that is little-used, so that the tags-search mainly
 hits on the essential aspects of being a key in the @('acl2-defaults-table').
 For another example: to arrange for adding @(tsee system-attachments) to the
 @(see summary), the process was to follow how @('hint-events') is put into the
 summary, so a first step was to do tags-search for ``@('hint-events')''.</li>

 <li>At what point during the development of a source code change is it best to
 write comments and user-level documentation?  It may be good to write an
 outline before coding, as a guide towards what you want.  But ACL2
 implementation work can be tricky, which may lead you to change the
 specification slightly; so it is probably best to leave detailed documentation
 until after the other work is done, including testing.</li>

 <li><color rgb='#c00000'>Expect to take considerable time writing comments,
 documentation, and output (e.g., for warnings and errors).</color> These are
 important and may take longer than the implementation work itself.</li>

 </ul>

 <p>NEXT SECTION: @(see developers-guide-contributing)</p>")

(defxdoc developers-guide-contributing
  :parents (developers-guide)
  :short "Contributing changes"
  :long "<p><b>WARNING</b>: This is just a draft.  Suggestions for improvements
 would be great; please send them to kaufmann@cs.utexas.edu</p>

 <p><b>IMPORTANT</b>: Before reading this topic, be sure to read the topic,
 @(see developers-guide-maintenance).  The present topic assumes that you have
 followed the process there to make changes in your copy of ACL2 and the @(see
 community-books), including testing and documentation.  Here are the steps for
 contributing your changes when they are complete and fully tested and
 documented.</p>

 <ol>

 <li>Create your modifications by following the processes outlined in the
 topic, @(see developers-guide-maintenance).  Have you added at least one
 release note item?  If not, then please look again at the topic, @(see
 developers-guide-maintenance), where that and other prerequisites are
 covered.</li>

 <li>Create a tarball that contains your changes that are <i>NOT</i> under the
 @('books/') directory.  For example, if (as is typical) those changes are all
 in the top-level ACL2 @('*.lisp') source files, you can do the following while
 standing in the ACL2 sources directory:
 @({
 tar cfz acl2-sources.tgz *.lisp
 })</li>

 <li>Create a git branch on your local machine, called @('my-branch') below
 (but give it a more descriptive name, for example, @('true-list-fix')):
 @({
 git checkout -b my-branch
 })</li>

 <li>Commit your updates that are under @('books/'), but <i>ONLY</i> those
 updates.  Be sure that the file with your commit message, @('tmp.msg') (or
 whatever you decide to call it, but below it is called @('tmp.msg')),
 describes your changes to the books.  The description can generally be brief
 (use @('git log') if you want to see examples), often quoting your new release
 note item.
 @({
 git add books
 git commit -F tmp.msg
 })</li>

 <li>Create your own GitHub fork if you don't already have one (for example, as
 explained in the documentation topic, @(see
 github-commit-code-using-pull-requests), Section (A)).  Assuming your GitHub
 username is @('my-username') and (again) your branch name is @('my-branch'),
 this should make your branch publicly accessible at the following URL: @({
 https://github.com/my-username/acl2/tree/my-branch })</li>

 <li>Push to your own GitHub fork, as follows:
 @({
 git push https://github.com/my-username/acl2 my-branch
 })</li>

 <li>Send the commit hash and tarball (see ``Create a tarball'' above), as well
 as the name and URL of your new branch (as discussed above), to an ACL2
 author.  Optionally also send the commit hash for the version of master that
 was your starting point.  As of this writing, those are to be sent to Matt
 Kaufmann, at @('kaufmann@cs.utexas.edu').</li>

 <li>The last steps will be done by Matt, who will start by getting your
 changes as follows, in a fresh directory.

 @({
 git clone https://github.com/acl2/acl2 .
 git fetch https://github.com/my-username/acl2 my-branch:my-branch
 git checkout my-branch
 })

 Note that after the @('checkout') command just above, @('my-branch') will
 contain only your changes.  Matt will then install your source code
 changes (from the tarball) into the branch, @('my-branch'), possibly make some
 edits, and run an @('`everything'') regression.  When this passes, Matt will
 run the following two commands, where @('tmp.msg') says something about the
 changes, with credit to you.  Note that the @('commit') command will cause
 @('my-branch') to contain all changes, both under @('books/') and from the
 sources tarball, possibly after edits from Matt.  NOTE: Matt might instead
 decide not to make any edits or run a regression before doing this, in which
 case he will do those things after the merge below, as noted below.

 @({
 git commit -a -F tmp.msg
 })

 Finally, Matt will run a @('merge') command so that @('master') contains all
 changes (both from @('books/') and from outside @('books/')), and then
 complete the update to @('master') in the GitHub repository.

 @({
 git checkout master
 # Get master up-to-date (this is just ``git pull'' with a check):
 bin/pull.sh
 git merge my-branch
 # Possibly run ``regression-everything'' before the final push just
 # below.  In fact this is critical if that wasn't done before.  There
 # may be additional edits and additional commits to master before the
 # push just below.
 git push https://github.com/acl2/acl2 master
 })</li>
 </ol>

 <p>NEXT SECTION: @(see developers-guide-utilities)</p>")

(defxdoc developers-guide-utilities
  :parents (developers-guide)
  :short "Data Structures and Utilities"
  :long "<p>This topic introduces some of the data structures and utilities
 built into ACL2.  Also see @(see system-utilities) and @(see
 programming-with-state).  Those topics have lots of useful information not
 covered in this overview topic.  Just to give one example: someone once needed
 a utility to print clauses nicely, so the utility @('prettyify-clause'), not
 mentioned below, was added to the list of utilities in @(see
 system-utilities).</p>

 <h3>@(csee State) and the logical @(see world).</h3>

 <color rgb='#800080'>
 <p>Much of this is covered in @(see developers-guide-background).</p>
 </color>

 <p>The @('state') is, logically, a data structure with many fields.  However,
 it is represented in ACL2 by a symbol, which is the value of
 @('*the-live-state*'):</p>

 @({
 ACL2 !>:q

 Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
 ? state
 ACL2_INVISIBLE::|The Live State Itself|
 ? *the-live-state*
 ACL2_INVISIBLE::|The Live State Itself|
 ?
 })

 <p>For technical reasons involving (as best recalled at this writing) tail
 recursion removal in some host Lisps, @('state') is not declared as a Common
 Lisp special variable.  So raw Lisp code (say, conditioned by
 @('#-acl2-loop-only')) should reference @('*the-live-state*') when @('state')
 is not lexically bound, to avoid compiler warnings.</p>

 @({
 ? (defun foo () state)
 ;Compiler warnings :
 ;   In FOO: Undeclared free variable STATE
 FOO
 ? (defun foo () *the-live-state*)
 FOO
 ?
 })

 <p>As discussed in an earlier chapter of this Guide (see @(see
 developers-guide-background)), a key logical field of @('state') is the
 @('global-table'), which is an alist associating state global variables with
 their values.  Also see @(see programming-with-state), which explains this
 idea further along with many other key data structures and programming idioms
 that pertain to @('state').</p>

 <p>The logical world is the value of state global variable
 @('current-acl2-world'), but is normally accessed using the function,
 @('w').</p>

 @({
 ACL2 !>(equal (f-get-global 'current-acl2-world state)
               (w state))
 T
 ACL2 !>(set-guard-checking nil)

 Masking guard violations but still checking guards except for self-
 recursive calls.  To avoid guard checking entirely, :SET-GUARD-CHECKING
 :NONE.  See :DOC set-guard-checking.

 ACL2 >(eq (f-get-global 'current-acl2-world state)
           (w state))
 T
 ACL2 >
 })

 <h3>Enabled structures</h3>

 <color rgb='#800080'>
 <p>THIS SECTION IS WORTH COVERING IN ITS ENTIRETY.</p>
 </color>

 <p>ACL2 handles @(see theories) using <i>enabled structures</i>.  Ideally you
 could learn about enabled structures by visiting the @(tsee defrec) form for
 @('enabled-structure').  As of this writing, there are virtually no comments
 in that @('defrec') form!  Fortunately, the field names are suggestive of
 their meaning; but that is not really adequate documentation.  This is one of
 those place in the ACL2 sources where additional comments would be useful.  In
 the meantime, you can learn about enabled structures by seeing how they are
 used, by doing an Emacs tags-search for ``@('enabled-structure')'' or perhaps
 ``@('(access enabled-structure')''.  Another option is to follow the
 definition of @('disabledp') to find the definition of @('enabled-runep'),
 where you'll see that @('(enabled-runep rune ens wrld)') is
 @('(enabled-numep (fnume rune wrld) ens)').  Note that @('ens') is a variable
 that is commonly used for enabled structures, and @('fnume') returns the
 <i>nume</i> of a @(see rune), which is a unique number corresponding to the
 rune.  The definition of @('enabled-numep') helps to explain the fields of an
 enabled structure.</p>

 @(def enabled-numep)

 <p>An ACL2 developer sometimes needs to be able to follow definitions like
 this to learn about ACL2 data structures &mdash; sad, but true.</p>

 <h3>Tag trees</h3>

 <color rgb='#800080'>
 <p>PERHAPS WE'LL JUST LOOK AT A CALL OF PUSH-LEMMA IN REWRITE.</p>
 </color>

 <p>A <i>tag tree</i>, or <i>ttree</i> (pronounced ``tee-tree''), is a
 structure that is used for recording information generated by the prover.
 There is no @('defrec') form for tag trees, but fortunately, there is a long
 comment in the ACL2 sources labeled ``; Essay on Tag-Trees''.  Here is a
 high-level introduction that may be helpful before you read that Essay.</p>

 <p>Abstractly a tag-tree represents a list of sets, each member set having a
 name given by one of the ``tags'' (which are symbols) of the ttree.  The
 elements of the set named @('tag') are all of the objects tagged @('tag') in
 the tree.  Definitions of primitives in the source code for manipulating tag
 trees are labeled with the comment ``; Note: Tag-tree primitive''.</p>

 <p>Many ACL2 prover functions take and return tag trees.  The function
 @('rewrite'), for example, takes a @(see term) and a ttree (among other
 things), and returns a new term, @('term''), and new ttree, @('ttree'').
 @('Term'') is provably equivalent to the input term (under the current
 assumptions) and @('ttree'') is an extension of the input ttree.  If we focus
 just on the set associated with the tag @('LEMMA') in the ttrees, then the set
 for @('ttree'') is the extension of that for the input ttree, which is
 obtained by unioning into it all the @(see rune)s used by the rewriter.  The
 set associated with tag @('LEMMA') can be obtained by @('(tagged-objects
 'LEMMA ttree)').  Tag trees contain useful prover information based not only
 on lemmas used but also on hints, assumptions generated by @(tsee force),
 @(see forward-chaining), and so on.</p>

 <p>The Essay on Tag-Trees describes some of the legal tags for a ttree, but
 the definitive list is the one enforced by function
 @('all-runes-in-ttree').  Here for example is an interesting clause from a
 @(tsee case) expression in the body of that definition.</p>

 @({
            (assumption
 ; Shape: assumption record
             ans)
 })

 <p>If you see this, then you might be curious about the notion of an
 ``assumption record''.  Then you can simply go to the definition of
 @('assumption') (typically, using the Emacs command, @('meta-.')).  You'll see
 quite a few lines of comments in that vicinity, which may help to get your
 head around these records.</p>

 <h3>Macros</h3>

 <p>Many macros that are useful in the ACL2 source code are also helpful to
 users, and hence are documented.  Among these are @(tsee defrec) (already
 discussed in the chapter, @(see developers-guide-background))), @(tsee
 defabbrev), @(tsee er-progn), @(tsee pprogn), @(tsee state-global-let*), and
 @(tsee revert-world).  Others could reasonably have their own documentation
 topics but are discussed in other topics; for example, see @(see
 programming-with-state) for a discussion of @(tsee er-let*).  Still others are
 not mentioned in the xdoc documentation but have Lisp comments in the source
 code, for example, @('revert-world-on-error'), @('with-ctx-summarized'),
 @('io?'), and @('acl2-unwind-protect').  Perhaps the best way to learn about
 the variety of available macros for ACL2 system programming is to notice their
 usage in existing ACL2 source code, then looking them up in the xdoc
 documentation and/or in the source code (typically with the Emacs command,
 @('meta-.')).</p>

 <h3>Evaluators</h3>

 <p>Source code often contains calls that evaluate terms.  A prime example is
 the implementation of the read-eval-print loop, as explained in the chapter,
 @(see developers-guide-background).  There are several evaluators available.
 The most familiar to users may be @(tsee trans-eval), which is actually a
 combination of translation and evaluation.  If you look at the source code and
 drill down (following definitions) from @('trans-eval'), you'll see that there
 are several optimizations, in part to support lazy treatment of @('if') calls:
 based on the test, perhaps only one of the two branches will need to be
 translated, let alone evaluated.  If you keep drilling down, you may
 ultimately see a call of @('ev'), which is an evaluator for (translated)
 terms.  In a sense @('ev') is the most basic term evaluator.  Note that
 @('ev') takes and returns @('state').  A related evaluator, @('ev-w'), may be
 used if @('state') and @('stobjs') are not involved.</p>

 <p>There is more to evaluation, such as the handling of stobjs via so-called
 ``latches'' and the @('user-stobj-alist'), which pertain to the subtle notion
 that user-defined stobjs are actually part of the ACL2 state; you can read
 comments in the sources to learn more about that when the need arises.  Also
 see the chapter, @(see developers-guide-evaluation).</p>

 <h3>Using @(tsee return-last)</h3>

 <color rgb='#800080'>
 <p>THIS SECTION IS WORTH COVERING IN ITS ENTIRETY.</p>
 </color>

 <p>There are occasions in which a utility is naturally defined as a function
 in ACL2 but as a macro in Common Lisp.  Consider @(tsee mbe).  Even though
 @('mbe') is itself a macro, it must expand to a function call involving its
 @(':logic') and @(':exec') arguments, so that a suitable @(see guard) proof
 obligation can be generated.  However, in raw Lisp we want an @('mbe') call to
 be fast, by simply running the @(':exec') argument.  Let's see how this is all
 arranged.</p>

 @({
 ACL2 !>:trans (mbe :logic (zp n) :exec (= n 0))

 (RETURN-LAST 'MBE1-RAW (= N '0) (ZP N))

 => *

 ACL2 !>:q

 Exiting the ACL2 read-eval-print loop.  To re-enter, execute (LP).
 ? (macroexpand '(mbe :logic (zp n) :exec (= n 0)))
 (= N 0)
 T
 ?
 })

 <p>The key, obviously, is to use @(tsee return-last), which is the <i>only</i>
 ACL2 utility that is defined to be a function in the ACL2 loop but is defined
 to be a macro in raw Lisp.  Before you add a new utility that, like @('mbe'),
 needs to operate as a function in the ACL2 loop but as a macro in raw Lisp,
 commit yourself to defining it using @('return-last').  The reason is that
 handling any such utility is tricky (see for example the definition of
 @('ev-rec-return-last')), so it would be ill-advised to replicate all the work
 done already for @('return-last') in handling any additional such utility.  Of
 course, the first step then is to become familiar with @('return-last').  The
 xdoc documentation on @(see return-last) is quite extensive, and may suffice;
 of course, it is also advisable to read the comments in the source code
 definition of @('return-last').</p>

 <p>The use of @('return-last') provides an example of the suggestion to use
 precedents (see @(see developers-guide-maintenance)).  Imagine that you want
 to add a function to ACL2 that is implemented under-the-hood as a macro in raw
 Lisp.  Ideally, you would look at an existing such utility, such as @('mbe'),
 to see how it is implemented.  This would lead you to @('return-last'), which
 you would then use similarly to implement your new utility.</p>

 <h3>Type-alists</h3>

 <p>A fundamental data structure in the ACL2 prover is the <i>type-alist</i>.
 Since some user-level utilities display the type-alist, there is user-level
 documentation for this data structure; see @(see type-alist), which contains
 important system-level background.  Perusal of the source code will reveal
 utilities for computing with type-alists.  Two key such utilities are
 @('type-set'), which computes the type-set of a term with respect to a given
 type-alist, and which again has user-level documentation (see @(see type-set))
 that also serves to provide important system-level background; and
 @('assume-true-false'), which extends a type-alist as one dives into the true
 or false branch of a call of @('IF').  Before creating type-alists with
 lower-level or new utilities, be sure to <color rgb='#c00000'>read the ``Essay
 on the Invariants on Type-alists, and Canonicality</color>.''  In general,
 look for essays on any topic that is relevant to changes that you are making,
 unless you are reasonably confident that the essay is at a lower level than
 you need.  For example, <color rgb='#c00000'>if you call
 @('assume-true-false') to extend an existing type-alist, then you are using a
 well-worn interface and you needn't be concerned about the well-formedness of
 the resulting type-alists</color>.</p>

 <p>NEXT SECTION: @(see developers-guide-logic)</p>")

(defxdoc developers-guide-logic
  :parents (developers-guide)
  :short "Logical Considerations"
  :long "<p>This Developer's Guide may give the impression that ACL2
 maintenance is primarily a programming exercise, and that is probably true.
 However, <color rgb='#c00000'>there are some subtle logical
 considerations</color> that need to be considered when working with some parts
 of the implementation.  This topic addresses an assortment of such
 considerations, often by pointing to source code comments.  Additional reading
 for those intrigued by logic is the paper: ``Structured Theory Development for
 a Mechanized Logic,'' Matt Kaufmann and J Strother Moore, Journal of Automated
 Reasoning 26, no. 2 (2001), pp. 161--203.</p>

 <p><b>Note:</b> <color rgb='#c00000'>The examples below are by no means
 comprehensive!</color> You are encouraged to extend this documentation topic
 with additional logical considerations as they arise.  Also see the Essay on
 Soundness Threats.</p>

 <h3>Histories, chronologies, and theories</h3>

 <p>An ACL2 session has at least three logical interpretations, as follows.</p>

 <ul>

 <li>The corresponding <color rgb='#c00000'><i>history</i></color>, which is
 the sequence of all <i>axiomatic @(see events)</i> from the session: this
 includes @(tsee defun), @(tsee defchoose), and @(tsee defaxiom) events, as
 well as @(tsee encapsulate) events with non-empty @(see signature)s.  It does
 not include @(tsee defthm) events.</li>

 <li>The corresponding <color rgb='#c00000'><i>chronology</i></color>, which is
 the sequence of all events from the session with logical content.  Thus the
 history is a subsequence of the chronology, but the chronology also includes
 @('defthm') events.</li>

 <li>The corresponding <color rgb='#c00000'><i>theory</i></color> of the
 session, which is the first-order theory of its history, that is, axiomatized
 by the formulas in its history.  (Careful: This theory is not sensitive to
 which runes are enabled, unlike the macro, @(tsee current-theory).)  A basic
 property of ACL2 is that all formulas in the session's chronology are provable
 in the session's theory.  In particular, by restricting to the chronology of
 events up to and including a given @('defthm') event, we see that the formula
 of that event is provable from the axiomatic events that precede it.</li>

 </ul>

 <color rgb='#c00000'>

 <p>When a session @('S1') is extended to a session @('S2') without using
 @('defaxiom') events, then the theory @('T2') for @('S2') is a <i>conservative
 extension</i> of the theory @('T1') for @('S1'): that is, every theorem of
 @('T2') whose function symbols all occur in @('T1') &mdash; that is, are all
 introduced in @('S1') &mdash; is a theorem of @('T1').  An important corollary
 is that if a session has no @('defaxiom') events, then its theory is
 consistent.</p>

 </color>

 <p>Note that @(tsee defattach) events are ignored for all three notions listed
 above.  There is also a notion of <i>evaluation theory</i>, which is the
 extension of the session's theory by the equations that equate each function
 with its attachment.  A basic property is that every evaluation theory built
 from a session free of @('defaxiom') events is the theory of some history that
 is free of @('defaxiom') events, and thus (by the corollary stated in the
 preceding paragraph) is consistent.  For a detailed development of theory
 supporting the use of @('defattach') (though this can probably ignored unless
 you are doing deep work with @('defattach')), see the source code comment,
 ``Essay on Defattach.''</p>

 <p>There is also a logical explanation for @(tsee apply$), which is based on
 the notion of evaluation theory mentioned above for @('defattach').  The
 upshot is that a certain construction, the ``doppelganger construction'',
 produces an evaluation theory in which every @(see warrant) is valid.  For
 detailed theoretical justification (probably not necessary for most
 developers, unless perhaps they are doing deep modifications pertaining to
 @('defattach') or @('apply$')), see the source code comment, ``Essay on
 Admitting a Model for Apply$ and the Functions that Use It.''</p>

 <h3>@(tsee Local)</h3>

 <color rgb='#800080'>
 <p>IN THIS SECTION WE CAN FOCUS MAINLY ON THE DISPLAYS.</p>
 </color>

 <color rgb='#c00000'>

 <p>Many soundness bugs in past versions of ACL2 &mdash; indeed, perhaps the
 majority of them &mdash; can be attributed to a subtle mishandling of @(tsee
 local) @(see events).  Perhaps the only advice possible in this regard is the
 following: Think carefully about the effects of @('local') when making
 event-level changes to ACL2!</p>

 </color>

 <p>Consider for example the following, seemingly innocuous ``enhancement'':
 allow @(tsee verify-guards) to comprehend macro-aliases (see @(see
 macro-aliases-table)).  Such an ``enhancement'' would be unsound!  Instead, a
 similar but sound enhancement, @('verify-guards+'), was introduced (into
 Version 6.3).  <color rgb='#c00000'>See @(see verify-guards+) for an example,
 using @(tsee encapsulate) and @(tsee local), for why such an enhancement to
 @('verify-guards') would be unsound.</color></p>

 <p>We turn now to discuss a key mechanism for avoiding potential soundness
 issues caused by @('local'): the @(tsee acl2-defaults-table).  Because of the
 logical information stored in this @(see table), it is prohibited to modify
 this table locally, as we illustrate with a couple of examples.  First
 consider the following introduction of a @(see program)-mode function, @('f'),
 that clearly is inadmissible in @(see logic)-mode.</p>

 @({
 (encapsulate
   ()
   (program)
   (defun f () (not (f))))
 })

 <p>If the @('(program)') event were allowed to be local, then the second pass
 of the @('encapsulate') event would introduce @('f') in logic-mode, creating
 an inconsistent theory!</p>

 <p>A slightly more subtle example is the following.</p>

 @({
 (encapsulate
   ()
   (set-ruler-extenders :all)
   (defun foo (x)
     (cons (if (consp x) (foo (cdr x)) x)
           3)))
 })

 <p>The induction scheme stored for @('foo') is as follows, which is the same
 as would be stored for the simpler definition, @('(defun foo (x) (if (consp
 x) (foo (cdr x)) x))').  (Don't worry about the form of the structure below.
 Further relevant discussion may be found below in the section, ``Induction,
 recursion, and termination.'')</p>

 @({
 ACL2 !>(getpropc 'foo 'induction-machine)
 ((TESTS-AND-CALLS ((CONSP X))
                   (FOO (CDR X)))
  (TESTS-AND-CALLS ((NOT (CONSP X)))))
 ACL2 !>
 })

 <p>The @(''induction-machine') property is computed based on the
 ruler-extenders.  So if the event @('(set-ruler-extenders :all)') above could
 be made local, we would be storing the same induction machine as for the
 following definition.</p>

 @({
 (skip-proofs
  (defun foo (x)
    (declare (xargs :measure (acl2-count x)))
    (cons (if (consp x) (foo (cdr x)) x)
          3)))
 })

 <p>But that induction-machine is unsound!</p>

 @({
 (thm nil :hints ((\"Goal\" :induct (foo x))))
 })

 <p>The two examples above illustrate the importance of thinking about whether
 an event can soundly be local.  If not, then it may be best for that event to
 be one that sets the @(tsee acl2-defaults-table), like @(tsee program) and
 @(tsee set-ruler-extenders), since @(tsee table) events that set the
 @('acl2-defaults-table') are not permitted to be local.</p>

 <h3>@(tsee Skip-proofs) vs. @(tsee defaxiom)</h3>

 <color rgb='#800080'>
 <p>IN THE WORKSHOP THE FOCUS WILL BE ONLY ON THE LOGICAL DIFFERENCE.</p>
 </color>

 <p>There is a fundamental logical difference between wrapping @(tsee
 skip-proofs) around a @(tsee defthm) event and using @(tsee defaxiom).  When
 using @('skip-proofs'), the user is promising that the ensuing proof
 obligations are indeed theorems of the theory of the current ACL2 session.
 However, the meaning of @('defaxiom') is to extend that theory with a new
 axiom, one which is generally not provable from the session's theory.  See
 @(see skip-proofs) and see @(see defaxiom).  This logical distinction has
 ramifications for the implementation, as we now describe.</p>

 <p>Since the use of @(tsee skip-proofs) carries an implicit promise of
 provability, the implementation can largely ignore the question of whether an
 event was, or was not, introduced using @('skip-proofs').  The key reason to
 do any such tracking is to inform @(tsee certify-book) when the use of keyword
 argument @(':skip-proofs-okp t') is required.</p>

 <p>On the other hand, it is critical for soundness to track the use of @(tsee
 defaxiom).  In particular, it is unsound to allow @(see local) @('defaxiom')
 events.  That is obvious from the following example, which would leave us in
 an ACL2 world in which @('nil') is provable even though there is no
 @('defaxiom') event in that world.</p>

 @({
 (encapsulate
   ()
   (local (defaxiom bad-axiom nil :rule-classes nil))
   (defthm bad-theorem nil
     :hints ((\"Goal\" :use bad-axiom))
     :rule-classes nil))
 })

 <p>That event is, of course, rejected by ACL2.  The following, on the other
 hand, is accepted; but this does not demonstrate unsoundness of ACL2, because
 the user violated the implied promise that, quoting from above, ``the ensuing
 proof obligations are indeed theorems of the theory of the current ACL2
 session.''</p>

 @({
 (encapsulate
   ()
   (local (skip-proofs (defthm bad-axiom nil :rule-classes nil)))
   (defthm bad-theorem nil
     :hints ((\"Goal\" :use bad-axiom))
     :rule-classes nil))
 })

 <p>We conclude this section by noting that there are different ``levels'' of
 @('skip-proofs') used by the implementation that are not directly visible to
 the user.  The basic @('skip-proofs') you see around an event generates a
 binding of state global @(''ld-skip-proofsp') to @('t').  However, when you
 include a book, state global @(''ld-skip-proofsp') is bound to
 @(''include-book'), which has two major effects: @('local') events are
 skipped, and some checks are omitted.  For example, the redundancy checks
 normally performed after @('(set-enforce-redundancy t)') are, as one would
 hope, omitted when including a book.  If you tags-search the sources for
 ``@('(enforce-redundancy')'', you'll see that it is used to implement
 events (see for example the definition of @('defconst-fn')); then if you look
 at the definition of @('enforce-redundancy'), you'll see that its check is
 skipped when state global @(''ld-skip-proofsp') is bound to
 @(''include-book'), hence when a book is being included.  Also see @(see
 ld-skip-proofsp).</p>

 <h3>Induction, recursion, and termination</h3>

 <p>Every proposed definition with recursion generates two related artifacts: a
 proof obligation that is generally described as the termination proof
 obligation, and an induction scheme to be stored if the definition is
 admitted.  <color rgb='#c00000'>A key soundness requirement is that the
 termination proof obligation justifies use of the induction scheme.</color>
 This produces a tension, as can be seen by the analysis below of the following
 example.</p>

 @({
 (defun f (x)
   (if (consp x)
       (cons (if (consp (car x)) (f (car x)) x)
             x)
     x))
 })

 <p>The generated induction is displayed symbolically just below: when proving
 a proposition @('(P x)'), the induction step is to assume @('(consp x)') and
 @('(P (car x))') when proving @('(P x)'), and the base case is to assume
 @('(not (consp x))') when proving @('(P x)').</p>

 @({
 ACL2 !>(getpropc 'f 'induction-machine)
 ((TESTS-AND-CALLS ((CONSP X))
                   (F (CAR X)))
  (TESTS-AND-CALLS ((NOT (CONSP X)))))
 ACL2 !>
 })

 <p>There is a comment just above the @('defrec') for @('tests-and-calls') that
 explains that record structure.  The corresponding termination
 scheme may be seen by evaluating @('(trace$ termination-machine)') before
 submitting the @('defun') form above.  Here is the result.</p>

 @({
 <1 (TERMINATION-MACHINE ((TESTS-AND-CALL ((CONSP X))
                                          (F (CAR X)))))
 })

 <p>What this means is that ACL2 must prove that under the hypothesis @('(consp
 x)'), then @('(acl2-count (car x))') is smaller than @('(acl2-count x)').
 That proof obligation clearly justifies the induction scheme described
 above.</p>

 <p>But let us try an experiment in which ACL2 is instructed to consider, for
 termination and induction, any @('IF')-tests that are not at the top level
 &mdash; in this case, within the call of @('cons').  In a fresh session, we
 try this instead.</p>

 @({
 (defun f (x)
   (declare (xargs :ruler-extenders (cons)))
   (if (consp x)
       (cons (if (consp (car x)) (f (car x)) x)
             x)
     x))
 })

 <p>The induction machine produced this time includes the extra @('if') test or
 its negation.  It says that when proving a proposition @('(P x)'), the
 induction step is to assume @('(consp x)'), @('(consp (car x))'), and
 @('(P (car x))') when proving @('(P x)'); one base case is to assume @('(consp
 x)') and @('(not (consp (car x)))') when proving @('(P x)'); and the other
 base case is to assume @('(not (consp x))') when proving @('(P x)').</p>

 @({
 ACL2 !>(getpropc 'f 'induction-machine)
 ((TESTS-AND-CALLS ((CONSP X) (CONSP (CAR X)))
                   (F (CAR X)))
  (TESTS-AND-CALLS ((CONSP X) (NOT (CONSP (CAR X)))))
  (TESTS-AND-CALLS ((NOT (CONSP X)))))
 ACL2 !>
 })

 <p>This time there is a different termination proof obligation as well,
 stating that @('(car x)') has a smaller @('acl2-count') than that of @('x')
 under the conjunction of the pair of assumptions @('(consp x)') and
 @('(consp (car x))').  As before, it justifies the induction scheme just
 above.</p>

 @({
 <1 (TERMINATION-MACHINE ((TESTS-AND-CALL ((CONSP X) (CONSP (CAR X)))
                                          (F (CAR X)))))

 })

 <p>Now suppose that the implementation is careless, by making the @(see
 ruler-extenders) affect the termination proof obligations but not the
 induction scheme.  Consider the following example.</p>

 @({
 (defun g (x)
   (declare (xargs :ruler-extenders (cons)))
   (cons (if (consp x) (g (car x)) x)
         x))
 })

 <p>This produces the termination proof obligation represented as follows
 (again from a trace), which says that assuming @('(consp x)'), @('(acl2-count
 (car x))') is less than @('(acl2-count x)').  Note that this is indeed a
 theorem.</p>

 @({
 <1 (TERMINATION-MACHINE ((TESTS-AND-CALL ((CONSP X))
                                          (G (CAR X)))))

 })

 <p>To see what the induction scheme would be if we ignored the
 ruler-extenders, we submit the following.</p>

 @({
 (skip-proofs
  (defun g (x)
    (declare (xargs :measure (acl2-count x)))
    (cons (if (consp (car x)) (g (car x)) x)
          x)))
 })

 <p>The corresponding induction machine states that to prove @('(P x)'), we may
 assume @('(P (car x))').</p>

 @({
 ACL2 !>(getpropc 'g 'induction-machine)
 ((TESTS-AND-CALLS NIL (G (CAR X))))
 ACL2 !>
 })

 <p>If we let @('(P x)') be @('(consp x)'), then clearly this induction scheme
 allows us to prove @('(consp x)') for all @('x')!</p>

 @({
 (thm (consp x)
      :hints ((\"Goal\" :induct (g x))))
 })

 <p>This induction scheme is thus clearly unsound.</p>

 <p>The moral of the story is this: As the termination machine is modified to
 accommodate the ruler-extenders, the induction machine must be modified
 accordingly.  More generally, and as already noted: The termination machine
 must justify the induction machine.</p>

 <h3>Other tricky stuff</h3>

 <p>The logical underpinnings of ACL2 can be a bit overwhelming when considered
 together, so the following paragraphs should be taken as a suggestion for what
 to explore only when you're in the mood for some logic, and also as an
 acknowledgment that many subtle logical issues exist.  It is <i>NOT</i> meant
 as a prescription for what you need to explore!  Moreover, it is far from
 complete.</p>

 <p>The foundations of metatheoretic reasoning can be challenging.  If you
 tags-search for ``; Essay on Metafunction Support'', you'll see two relevant
 essays.  But a much longer essay is the ``Essay on Correctness of Meta
 Reasoning''.  That essay even ties into the ``Essay on Defattach'', at the
 mention of the Attachment Restriction Lemma.  If you decide to change the
 handling of metafunctions or clause-processors or their corresponding @(see
 rule-classes), @(':meta') and @(':clause-processor'), other than fixing coding
 bugs or making extra-logical changes such as output, you probably should read
 these Essays.  Of course, before reading these or any essays, it is generally
 a good idea to read relevant user-level documentation, such as the
 documentation for @(see meta) or @(see clause-processor).</p>

 <p>A few other features of ACL2 with interesting logical foundations are
 @(tsee defchoose), @(tsee defabsstobj), and the interaction of packages with
 @(tsee local) (see the ``Essay on Hidden Packages'').</p>

 <p>NEXT SECTION: @(see developers-guide-programming)</p>")

(defxdoc developers-guide-programming
  :parents (developers-guide)
  :short "Programming Considerations"
  :long "<p>This chapter discusses some things to keep in mind when modifying
 the ACL2 sources.  It is not intended to discuss any particular aspects of the
 ACL2 source code, but rather, to highlight some general principles.</p>

 <color rgb='#800080'>
 <p>ALL OF THIS TOPIC IS VERY IMPORTANT.</p>
 </color>

 <h3>Keep the user in mind</h3>

 <p>Error and warning messages take time to write, but can (obviously) be
 really helpful to users.  Avoid trying to say too much in one message, instead
 pointing to one or more @(see documentation) topics for elaboration if
 appropriate.</p>

 <p>It is generally fine to change a system utility's behavior or even to
 delete its definition.  However, this is discouraged if that utility is
 documented; otherwise there could be an annoyed user who is adversely
 affected.</p>

 <h3>Program defensively</h3>

 <p>It is a good idea to look for precedents.  See also the discussion of
 precedents in the topic, @(see developers-guide-maintenance).</p>

 <p>Add assertions and errors when appropriate.  For example, the function
 @('all-runes-in-ttree') contains a large @(tsee case) expression, which covers
 each tag that could occur in a tag tree.  The last case is an error whose
 message mentions the bad tag together with the values associated with that
 tag.</p>

 <p>Check invariants.  For example, the function @('check-acl2-initialization')
 checks some properties that are expected to hold at the end of a build; in
 particular, it calls @('check-none-ideal'), which reports @(see logic)-mode
 functions that are not @(see guard)-verified.  (If a logic-mode function is
 not guard-verified, then it may run slowly.  We don't want built-in functions
 to run slowly.)</p>

 <h3>Use installed worlds</h3>

 <p>Fundamental utilities for ACL2 programmers are the function, @(tsee
 getprop), and its associated abbreviation, @(tsee getpropc).  @('Getprop') is
 defined in the logic to walk through a given logical @(see world), much as
 @(tsee assoc) walks through a given association list.  However, @('getprop')
 is defined ``under-the-hood'' with raw Lisp code (see the discussion of
 @('acl2-loop-only') in @(see developers-guide-background)) so that if the
 world is what we call ``installed'', typically @('(w state)'), then access is
 essentially constant-time.  The ACL2 utilities @('set-w'), @('set-w!'),
 @('extend-world'), and @('retract-world') all may be invoked to install
 worlds, but it is rarely necessary or even advisable to call these directly.
 They are typically used in the implementations of @(see events).</p>

 <p>Typically, ACL2 system programming passes along worlds that are installed,
 and one needn't think about whether a world is installed or not.  A major
 exception is when code recurs through the world, looking for a suitable
 triple.  Consider the source code definition of @('new-verify-guards-fns1');
 we include an elided version of it here.</p>

 @({
 (defun new-verify-guards-fns1 (wrld installed-wrld acc)
   (declare (xargs :guard ...))
   (cond ((or (endp wrld) ...)
          ...)
         ((and (eq (cadar wrld) 'symbol-class)
               (eq (cddar wrld) :COMMON-LISP-COMPLIANT)
               (getpropc (caar wrld) 'predefined nil installed-wrld))
          (new-verify-guards-fns1 (cdr wrld)
                                  installed-wrld
                                  (cons (caar wrld) acc)))
         (t (new-verify-guards-fns1 (cdr wrld) installed-wrld acc))))
 })

 <p>We may reasonably assume from its name that the argument
 @('installed-wrld') is an installed world.  That's a good thing, since it
 guarantees that the @('getpropc') call above will be fast.  Suppose, by
 contrast, that the definition had been made in the following, more
 ``straightforward'', manner.</p>

 @({
 (defun BAD-new-verify-guards-fns1 (wrld acc)
   (declare (xargs :guard ...))
   (cond ((or (endp wrld) ...)
          ...)
         ((and (eq (cadar wrld) 'symbol-class)
               (eq (cddar wrld) :COMMON-LISP-COMPLIANT)
               (getpropc (caar wrld) 'predefined nil wrld))
          (BAD-new-verify-guards-fns1 (cdr wrld)
                                      (cons (caar wrld) acc)))
         (t (BAD-new-verify-guards-fns1 (cdr wrld) installed-wrld acc))))
 })

 <p>As we cdr down the given world, we deal with worlds that are not the
 installed world.  The @('getpropc') call will then need to walk linearly
 through its world until it finds the desired property &mdash; typically very
 far from constant-time behavior.</p>

 <p>Note that there are occasions for which the world is extended a bit before
 properties are obtained, and that's fine.  For example, in the source code
 definition of function @('chk-acceptable-defuns1') we find a call
 @('(putprop-x-lst1 names 'symbol-class symbol-class wrld1)'), which
 contributes to an extension of @('wrld1') that will ultimately be used for
 definitional processing, including the termination proof.  The prover makes
 many calls of @('getprop') (typically via @('getpropc')) on that extended
 world.  Normally this isn't a problem: @('getprop') will then walk linearly
 through the new part of the world but will soon hit the installed world, and
 then finish its work quickly.  When large @(tsee mutual-recursion) nests are
 involved, this could be problematic, except that this issue is taken care of
 by the @('big-mutrec') hack; see for example the definition of
 @('defuns-fn1').  But we're getting into the weeds now; our point is that
 @('getprop') and @('getpropc') do best with worlds that are installed or are
 modest extensions of installed worlds.</p>

 <h3>More generally, program efficiently</h3>

 <p>Program with tail-recursion when possible, as tail-recursive functions are
 less likely to cause stack overflows and might also execute more
 efficiently.</p>

 <p>Undoubtedly there are many other tips that could be given here on efficient
 programming.  Maybe they'll be added over time.</p>

 <h3>Write good comments</h3>

 <p>This is a matter of taste, and tastes vary.  Probably we can all agree that
 obvious bits of simple code need not be commented; for example, the code
 @('(append lst1 lst2)') does not need a comment ``concatenate the two
 lists''.  At the other extreme, probably we can all agree that a complex
 algorithm deserves a comment.  When in doubt it might be best to write a bit
 too much rather than a bit too little.  A good guiding principle is to imagine
 yourself reading the code ten or twenty years later; will it make sense?</p>

 <p>NOTE: If a comment is worth putting into a git commit message, then it's
 probably worth putting into the source code or documentation.</p>

 <h3>Use good names</h3>

 <p>For new names, avoid common strings so that it's easy to tags-search for
 them later.  Good examples include @('\"rune\"') and @('\"pspv\"') for the
 data structures, ``RUle NamE'' and ``Prover SPecial Variable'' (see the record
 @('prove-spec-var')).  (With the Emacs command @('meta-x tags-apropos') you
 can see many function names that mention include these two strings.)  A
 thesaurus such as <a href='http://thesaurus.com'>@('thesaurus.com')</a> may be
 helpful in naming a notion.</p>

 <p>Do not abbreviate excessively.  Good naming examples may be found in the
 fields of the record @('prove-spec-var').  These fields are not well
 commented, but the names are helpful; for example, the field name
 @('user-supplied-term') is suggestive of the contents of that field, i.e., the
 term supplied to the prover by the user.  For another example, the function
 @('rewrite-with-linear') hints at its purpose, which is to use linear
 arithmetic during rewriting.  If we see a call of this function we can get a
 sense of what it's about.  That would be more difficult if the function were
 named @('rwl').</p>

 <p>But this is a matter of taste.  For example, the function
 @('assume-true-false') hints at its functionality, which, roughly speaking, is
 to extend a @(see type-alist) by assuming an @('IF') test either true or
 false.  So why is there a function @('mv-atf')?  This is not such a huge
 transgression, since it's only used in the implementation of
 @('assume-true-false'), so if you see it then your head is probably in a place
 where the abbreviation @('atf') makes sense.</p>

 <h3>Add tests</h3>

 <p>This is something that could probably be done more often; as of this
 writing, unit testing of specific features is relatively rare or in Lisp
 comments.  The @(see community-books) directories @('books/system/tests/') and
 @('books/demos/') are places to put small, specific tests, and others exist
 elsewhere, for example, the four test files
 @('books/misc/defabsstobj-example-*.lisp').  So there really aren't specific
 places to place tests.  If you run the following command in the @('books/')
 directory, you will find that there are likely well over 100 books that do
 some sort of testing, albeit not necessarily of specific features implemented
 in the ACL2 source code (159 of these as of this writing).</p>

 @({
 find . -name '*test*.lisp' -print | fgrep -v quicklisp | wc -l
 })

 <h3>In general, be careful</h3>

 <p>Of course, that's easier said than done!  But please, at the least, make
 some effort to avoid introducing inefficiencies, unclear code, or (especially)
 unsoundness.</p>

 <p>Let us consider one example: the question of whether to skip certain checks
 when proofs are skipped.  You may want to look for precedents (as discussed
 above).  You may find that when @('(ld-skip-proofsp state)') is
 @(''include-book') or @(''include-book-with-locals'), the function
 @('load-theory-into-enabled-structure') avoids a call of
 @('chk-theory-invariant') (actually shown as @('chk-theory-invariant@par');
 see the discussion of ACL2(p) in the chapter, @(see
 developers-guide-background)).  Thus, theory invariants <i>are</i> checked
 when @('(ld-skip-proofsp state)') is @('t'), i.e., when we are skipping proofs
 but not including a book (as discussed in the chapter, @(see
 developers-guide-logic)).  The idea here is that when including a certified
 book, we check theory-invariants just once, at the end of the book inclusion
 process, for efficiency.  So one way to be careful is to do various checks
 even when @('(ld-skip-proofsp state)') is @('t'), even if these checks are to
 be skipped when including books.</p>

 <p>NEXT SECTION: @(see developers-guide-prioritizing)</p>")

(defxdoc developers-guide-prioritizing
  :parents (developers-guide)
  :short "Prioritizing: When to Make Changes"
  :long "<p>It may be tempting to enhance ACL2 whenever an intriguing idea
 comes along for making an improvement.  There is something to be said for
 doing so: the immediate motivation may make the work fun and lead to good
 results.</p>

 <color rgb='#800080'>
 <p>SUMMARY THAT SHOULD SUFFICE: Fix bugs, prioritize what will actually be
 used, and beware of massive regression failures.  Changes can be extremely
 valuable, and can also be substantially more work than predicted.</p>
 </color>

 <p>But there can be drawbacks to taking on every opportunity to make an
 improvement.  Heuristic improvements can be very difficult to work out without
 breaking, or slowing down, the regression suite.  A change may inadvertently
 break something.  Changes may be much more time-consuming than expected, and
 may take time away from other more important changes to be made.  Below we
 explore some aspects of prioritizing development tasks.</p>

 <h3>Bugs</h3>

 <p>Bug fixes are generally a priority, especially (of course) if they impact
 soundness.  Enough said?</p>

 <h3>Accommodating user requests</h3>

 <p>It has been observed that many ideas for improvements that may <i>seem</i>
 helpful are actually <i>not</i> very helpful to anyone actually using ACL2.
 It is therefore usually a good idea to prioritize changes that either
 accommodate specific requests from a user, or at the least can be seen as
 having significant positive impact on users.  It is very easy to think a new
 feature will be useful, but with the result that it's rarely or ever used, yet
 it complicates the source base.  A feature you consider might be close to
 being useful, but by waiting for a specific request, you can perhaps get
 substantially more insight about what would truly be useful, thus refining
 your initial idea for that feature.</p>

 <h3>Impacts on the regression suite</h3>

 <p>The ACL2 @(see community-books) provide a well-established set of
 libraries, as well as a useful set of regression tests.  Changes to ACL2 may
 cause some failures when certifying these books.  Often these are easy to fix,
 for example by modifying @(see theory) @(see hints) or by changing subgoal
 names on hints.  Changes may also impact ACL2(p) or ACL2(r), which are
 probably tested significantly less frequently.  More worrisome is the
 potential impact on private repositories, for example proprietary (not public)
 sets of books at companies.  There can also be slowdowns, which can be
 debugged by running the tool @('compare.pl'); see the chapter, @(see
 developers-guide-maintenance).  There is a balance, addressed by using
 judgment, between introducing behavioral changes and maintaining the community
 books and private repositories.  There needs to be a guess about whether the
 benefit of the change outweighs the effort required to design and implement it
 and the fallout of requiring changes to books.</p>

 <p>NEXT SECTION: @(see developers-guide-evaluation)</p>")

(defxdoc developers-guide-evaluation

; An "inefficiency" (referenced below) is getting the value of a special
; variable twice: (F-GET-GLOBAL 'GUARD-CHECKING-ON *THE-LIVE-STATE*).  Instead
; we could bind a lexical variable to that value, and use the lexical variable
; twice.

  :parents (developers-guide)
  :short "How Evaluation Is Implemented in ACL2"
  :long "<p>Our focus here is primarily on evaluation in the top-level loop.
 Also see the section on ``Evaluators'' in the chapter, @(see
 developers-guide-utilities).</p>

 <color rgb='#800080'>
 <p>ALL OF THIS TOPIC IS IMPORTANT; coverage will depend on time available at
 the workshop.</p>
 </color>

 <h3>Introduction and further reading</h3>

 <p>This chapter is in two parts (not including this introduction).  It starts
 with a very brief review of evaluation in the read-eval-print loop.  Then it
 dives a bit into how *1* function definitions are generated.  It may be
 helpful to read the following additional material either before or after
 reading this chapter, or perhaps, both.</p>

 <p>The documentation topic, @(see evaluation), explains ``*1* functions''
 &mdash; we assume here that you have some basic familiarity with that notion
 &mdash; and ``submitted functions'', which are the functions directly produced
 by the @('defun') forms in raw Lisp).  That topic also explains the role of
 these two functions in evaluation.  Below we start with a very brief
 illustration of that material.  For other reading relevant to evaluation at
 the user level, see @(see guard) and consider looking at some of its
 subtopics, especially @(see guard-evaluation-table).  Finally, look at
 relevant source comments pertaining to the aspect of evaluation that you are
 modifying, whether that is in @('ev-rec'), @('oneify'), or some other
 function.</p>

 <p>The implementation of evaluation in ACL2 is rather subtle.  As is the case
 for this Developer's Guide in general, this chapter is not intended to provide
 complete coverage of the topic.  Its purpose is to provide sufficient
 background so that comments and code in the ACL2 sources can fill in on
 demand, as necessary.</p>

 <h3>Brief overview of evaluation in the ACL2 read-eval-print loop</h3>

 <p>The section on ``Commands and events'' in the chapter, @(see
 developers-guide-background), explains that evaluation of a form in the ACL2
 loop is performed by a variant of the function, @(tsee trans-eval).  That
 function (as well as @('trans-eval') itself), in turn, leads to a call of the
 evaluator, @('ev'), which ultimately leads to calls of the raw Lisp function,
 @('raw-ev-fncall'), to evaluate function calls @('(f val1 ... valk)').  The
 function @('raw-ev-fncall'), in turn, calls the *1* function for the function
 symbol given as its first argument.  Let's see how that works.  First we
 define two functions and trace both of them.</p>

 @({
 (defun f1 (x)
   (declare (xargs :guard (true-listp x)))
   (car x))

 (defun f2 (x)
   (f1 x))

 (trace$ f1 f2)
 })

 <p>Now let's see what can happen during evaluation.</p>

 @({
 ACL2 !>(f2 '(3 4))
 1> (ACL2_*1*_ACL2::F2 (3 4))
   2> (ACL2_*1*_ACL2::F1 (3 4))
     3> (F1 (3 4))
     <3 (F1 3)
   <2 (ACL2_*1*_ACL2::F1 3)
 <1 (ACL2_*1*_ACL2::F2 3)
 3
 ACL2 !>
 })

 <p>Evaluation starts with a call to the *1* function for @('f2').  Since
 @('f2') is not guard-verified, there is no call of the submitted function for
 @('f2') (see @(see evaluation) for terminology).  Instead, the *1* function
 for @('f2') directly calls the *1* function for @('f1').  Since @('f1') is
 guard-verified, this leads to a call of the submitted function for
 @('f1').</p>

 <h3>Producing *1* functions: @('oneify') and @('oneify-cltl-code')</h3>

 <p>The production of *1* functions is subtle, largely because many cases need
 to be handled in order to connect the ACL2 logic with Common Lisp; see @(see
 guard-evaluation-table) for a partial exploration of that connection.  @(Csee
 stobjs) must be handled properly as well.</p>

 <p>The top-level function for creating *1* functions is @('oneify-cltl-code').
 This function, in turn, calls @('oneify') on its guard and body.  Here is
 annotated trace output, created by submitting the definition of @('f1') above
 after tracing as follows: @('(trace! (oneify-cltl-code :native
 t) (oneify :native t))').  Note that we use ``oneify'' as a verb: to oneify is
 to create code for a *1* function.</p>

 @({
 ; Top-level call:

 1> (ONEIFY-CLTL-CODE :LOGIC
                      (F1 (X)
                          (DECLARE (XARGS :GUARD (TRUE-LISTP X)))
                          (CAR X))
                      NIL |current-acl2-world|)

 ; Oneify the guard:

   2> (ONEIFY (TRUE-LISTP X)
              NIL |current-acl2-world| NIL)
     3> (ONEIFY X NIL |current-acl2-world| NIL)
     <3 (ONEIFY X)
   <2 (ONEIFY (ACL2_*1*_ACL2::TRUE-LISTP X))

 ; Oneify the body:

   2> (ONEIFY (CAR X)
              NIL |current-acl2-world| NIL)
     3> (ONEIFY X NIL |current-acl2-world| NIL)
     <3 (ONEIFY X)
   <2 (ONEIFY (ACL2_*1*_COMMON-LISP::CAR X))

 ; Return the definition of the *1* function for f1 (without the leading
 ; ``defun''):

 <1 (ONEIFY-CLTL-CODE
         (ACL2_*1*_ACL2::F1
              (X)
              (WHEN (NOT (EQ (F-GET-GLOBAL 'GUARD-CHECKING-ON
                                           *THE-LIVE-STATE*)
                             :NONE))

 ; Unless guard-checking is :none, we check the guard.

                    (COND ((TRUE-LISTP X)

 ; When the guard holds, call the submitted function to obtain the value.

                           (RETURN-FROM ACL2_*1*_ACL2::F1 (F1 X)))
                          ((F-GET-GLOBAL 'GUARD-CHECKING-ON
                                         *THE-LIVE-STATE*)

 ; The guard fails, and unless guard-checking is nil (or :none, but that was
 ; already considered above), cause an guard violation.

                           (THROW-RAW-EV-FNCALL (LIST 'EV-FNCALL-GUARD-ER
                                                      'F1
                                                      (LIST X)
                                                      '(TRUE-LISTP X)
                                                      '(NIL)
                                                      NIL)))))

 ; If we didn't return or get a guard violation, then call a local function
 ; defined to have the oneified body.  Note: LABELS is like LET but for
 ; local function definitions, which may be recursively defined.  See any
 ; Common Lisp documentation for more about LABELS.

              (LABELS ((ACL2_*1*_ACL2::F1 (X)
                                          (ACL2_*1*_COMMON-LISP::CAR X)))
                      (ACL2_*1*_ACL2::F1 X))))
 })

 <p>Do you see an inefficiency above?</p>

 <p>See code comments for how oneification deals with subtleties such as
 safe-mode, stobjs, and invariant-risk.</p>

 <p>NEXT SECTION: @(see developers-guide-miscellany)</p>")

(defxdoc developers-guide-miscellany
  :parents (developers-guide)
  :short "Miscellaneous Information"
  :long "<p>The initial version of this chapter is little more than a stub.  It
 will probably always benefit from expansion to cover more topics.</p>

 <h3>Trust tags</h3>

 <p>See @(see defttag) for user-level information about trust tags.  The
 ``Essay on Trust Tags (Ttags)'' provides a lot of relevant background on trust
 tags at the implementation level.  A particularly important point to be
 emphasized here is the following: The critical aspect of trust tags is that
 whenever a trust tag is activated, the string @('\"TTAG NOTE\"') must be
 printed to @('*standard-co*') (see the definition of @('print-ttag-note')),
 with the exception that if ttag notes are deferred then initially, only the
 first such is printed; see @(see set-deferred-ttag-notes).  The paper
 ``Hacking and Extending ACL2'' from the 2007 ACL2 Workshop may be helpful.</p>

 <h3>Fixnums</h3>

 <p>In general, Common Lisp computations with numbers are much faster when they
 only deal with ``small'' numbers called <i>fixnums</i>.  See the ``Essay on
 Fixnum Declarations'' for information about fixnums and ACL2, including a
 description of the ranges for 32-bit fixnums in different Common Lisp
 implementations as of this writing.  There may be some opportunities made
 available by modern Lisps that have 64-bit implementations.  (CMUCL seems to
 be an exception.)</p>

 <h3>Infix printing is no longer supported</h3>

 <p>At one time ACL2 had support for infix printing, which was used rarely if
 at all.  Infix code is still present, conditioned by feature @(':acl2-infix'),
 but it has probably been quite some time since it was tested.  Perhaps it is
 time to remove all such code; indeed, the release notes for Version 8.0 (see
 @(see note-8-0)) say that ``The (minimal) support for infix printing has been
 removed.''</p>

 <p>NEXT SECTION: @(see developers-guide-releases)</p>")

(defxdoc developers-guide-releases
  :parents (developers-guide)
  :short "Releases"
  :long "<p>For ACL2, there are two senses of the notion, ``release''.  This
 word traditionally referred to numbered releases of ACL2 at the University of
 Texas, such as Version 8.0, as documented in the @(see release-notes).  But
 the ACL2 community increasingly obtains versions of ACL2 from GitHub, at <a
 href='https://github.com/acl2/acl2'>@('https://github.com/acl2/acl2')</a>.
 These ``releases'' are typically well-tested, though not as thoroughly tested
 as numbered releases, which (as of this writing) are always tested on Linux
 using all of the supported Common Lisp implementations, and also tested on
 Mac.  Even GitHub releases should generally be tested using the
 ``@('regression-everything')'' target for `@('make')' in the top-level
 directory, or equivalently, the ``@('everything')'' target in the @('books/')
 directory.</p>

 <p>There are extensive instructions for doing numbered releases, which as of
 this writing have not been made public.  Anyone who cares to volunteer to make
 numbered releases should talk with Matt Kaufmann about obtaining those
 instructions, which perhaps would become public at that point.  (It could take
 non-trivial effort to clarify those instructions for the ``public'', so let's
 wait till there is such a volunteer.)</p>

 <p>NEXT SECTION: @(see developers-guide-style)</p>")

(defxdoc developers-guide-style
  :parents (developers-guide)
  :short "Style Guidelines for Developing ACL2 System Code"
  :long "<p>Here we set out some style guidelines that have traditionally been
 followed in the ACL2 sources.  They can guide development to help maintain
 ACL2's quality by giving its source files a consistent look.</p>

 <p>The right margin is 79.  (In Emacs: @('set-fill-column 79').)  Existing
 code with margin 70 is OK to leave as is, though it's nice to convert to a
 margin of 79 when modifying comments within a given function.</p>

 <p>Tabs are not used.  In Emacs, setting buffer-local variable
 @('indent-tabs-mode') to @('nil') will accomplish this.  That can be
 accomplished automatically for Lisp files, as is done in distributed file
 @('emacs/emacs-acl2.el'); search there for @('indent-tabs-mode'), or simply
 load that file in your @('.emacs') file.</p>

 <p>Periods that end sentences are followed by two spaces (useful for the
 @('meta-e') command in Emacs).</p>

 <p>Comments for a function go immediately after its formal parameters
 (even before @(see declare) forms).</p>

 <p>Comments generally consist of complete sentences, starting on the left
 margin, each line starting with a single semicolon followed by a space.  An
 exception is very short comments to the right of code up to the end of the
 same line.</p>

 <p>Use of the @(tsee cond) macro is generally preferred to the use of @('if'),
 an exception being small expressions that are not at the top level of the
 @('if') structure.</p>

 <p>System state globals need to be included in @('*initial-global-table*') or
 @('*initial-ld-special-bindings*').</p>

 <p>Blank lines are avoided except in the usual circumstances, e.g.,
 surrounding comments and between definitions.  Avoid consecutive blank
 lines.</p>

 <p>A multi-line argument is not followed by an argument on the same line.  For
 example, there should be a linebreak before the argument, @('arg'), after the
 string in this @('COND') clause:</p>

 @({
 (t (er soft ctx
        \"The value associated with a :SOME-NEW-HINT hint must be a positive ~
        integer, but ~x0 is not.\" arg))
 })

 <p>We generally avoid capitalizing all letters in a single word, except
 perhaps for keywords or quoted constants.</p>

 <p>There are no multi-line comments: @('#|| ... ||#').</p>

 <p>NEXT SECTION: @(see developers-guide-other)</p>")

(defxdoc developers-guide-other
  :parents (developers-guide)
  :short "Topics Not Covered"
  :long "<p>There are many aspects of the ACL2 implementation, even major ones,
 that aren't covered in this Development Guide.</p>

 <h3>It's perfectly OK that this Guide is incomplete!</h3>

 <p>ACL2 has been maintained for more than 25 years by people who don't recall
 very much about large portions of the source code, probably the majority of
 it.  The key is that when making changes, one explores relevant code, reading
 relevant user-level documentation and code comments (including Essays), and
 talking with other developer(s) about questions and issues.  System
 maintenance generally gets easier with experience.</p>

 <p>Here is a partial list of topics, in no particular order, that are left
 uncovered by this guide, or largely so: @(tsee defproxy) and (except for brief
 mention) @(tsee defattach); @(see stobj)s, including nested stobjs and
 abstract stobjs; @(see arrays); hons, memoization, and fast-alists (see @(see
 hons-and-memoization)); the @(see serialize) reader and writer; @(tsee
 apply$); @(tsee make-event); @(see meta)functions and @(see
 clause-processor)s; @(see hints), including @(see computed-hints), default
 hints, @(see override-hints), and custom keyword hints; @(see wormhole)s;
 printing, including evisceration (see @(see evisc-tuple)), @(see iprinting),
 pretty-printing, @(tsee fmt), @(tsee cw), @(tsee print-object$) and @(tsee
 with-output); @(see constraint)s and @(see functional-instantiation); the
 @(see documentation) system; the prover, including the @(see waterfall), the
 rewriter (for example @(see break-rewrite), congruences and patterned
 congruences, the @(see rewrite-cache), etc.), the @(see tau-system), @(see
 forward-chaining), and much more; pathnames, including @(see
 canonical-pathname)s; @(tsee encapsulate) and @(see functional-instantiation),
 including the @('proved-functional-instances-alist'); the @(see
 proof-builder); and certifying and including @(see books).  And this is only a
 partial list!</p>

 <p>But again, the Guide is not intended to be complete.  In principle, at
 least, you can learn about any of the topics above when necessary, by reading
 user-level documentation and using the Emacs tags-search and @('meta-.')
 commands to find relevant code, and comments, and in particular, essays.</p>

 <h3>Expanding this Guide</h3>

 <p>Perhaps this Guide will be expanded in the future.  If so, the expansion
 should probably not duplicate code comments, but rather, provide overview
 information and perspective with pointers to those comments.</p>

 <p>NEXT SECTION: @(see developers-guide-acl2-devel)</p>")

(defxdoc developers-guide-acl2-devel
  :parents (developers-guide)
  :short "<color rgb='#c00000'>Use the acl2-devel List!</color>"
  :long "<p>For years, Kaufmann and Moore have had regular chats during which
 they collaborate on development issues.  Use the acl2-devel mailing list to
 continue that tradition.  For example, if you are trying to get oriented about
 the waterfall and how hints interact with it, you could query the acl2-devel
 list and maybe someone will point you to the documentation topic, @(see
 hints-and-the-waterfall).</p>

 <p>But please don't use the acl2-help or acl2 mailing lists for
 developer-level discussions, as that can spook users.  The acl2-books list
 also is not the right place; note that it is missing at least one important
 member of acl2-devel.</p>

 <p>This is the final topic under @(see developers-guide).<br/>HAPPY
 DEVELOPING!</p>")

(defxdoc stobj-fields-of-abstract-stobjs
  :parents (developers-guide)
  :short "<color rgb='#c00000'>To-do list for @(see stobj) fields of abstract stobjs</color>"
  :long "<p>Although the code is complete for @(see stobj) fields of abstract
 stobjs, without known errors as of this writing (May 2021), nevertheless there
 remains some testing, comments, and documentation to complete.  See text file
 @('books/system/doc/stobj-fields-of-abstract-stobjs.txt') for a list.  Matt
 Kaufmann intends to take are of these by the end of July 2021.</p>")

(xdoc::order-subtopics developers-guide
                       ()
                       t)
