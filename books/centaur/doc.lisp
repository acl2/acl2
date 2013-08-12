; Centaur Book Documentation
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "ACL2")

(make-event

; Disabling waterfall parallelism because the include-books are too slow with
; it enabled, since waterfall parallelism unmemoizes the six or so functions
; that ACL2(h) memoizes by default (in particular, fchecksum-obj needs to be
; memoized to include centaur/tutorial/alu16-book).

 (if (and (hons-enabledp state)
          (f-get-global 'parallel-execution-enabled state))
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))

(include-book "misc/memory-mgmt")
(value-triple (set-max-mem (* 10 (expt 2 30))))

; [Jared]: I suspect the following comment may be out of date?  But this
; seems harmless enough anyway...
;
;   The following are included automatically by the xdoc::save command below,
;   but we include them explicitly to support the hons `make' target in the
;   books/ directory (and hence the regression-hons `make' target in the
;   acl2-sources directory).

(include-book "xdoc/save-fancy" :dir :system)
(include-book "xdoc/defxdoc-raw" :dir :system)
(include-book "xdoc/mkdir-raw" :dir :system)
(include-book "xdoc/topics" :dir :system)

(include-book "4v-sexpr/top")

(include-book "aig/aiger")
(include-book "aig/aig-equivs")
(include-book "aig/aig-vars")
(include-book "aig/aig-vars-fast")
(include-book "aig/aig2c")
(include-book "aig/aig-sat")
(include-book "aig/base")
(include-book "aig/bddify")
(include-book "aig/bddify-correct")
(include-book "aig/eval-restrict")
(include-book "aig/g-aig-eval")
(include-book "aig/induction")
(include-book "aig/misc")
(include-book "aig/three-four")
(include-book "aig/witness")
(include-book "aig/best-aig")
(include-book "aig/random-sim")

(include-book "aignet/aig-sim")
(include-book "aignet/copying")
(include-book "aignet/from-hons-aig-fast")
(include-book "aignet/prune")
(include-book "aignet/to-hons-aig")
(include-book "aignet/types")
(include-book "aignet/vecsim")

(include-book "bitops/top")
(include-book "bitops/congruences")
(include-book "bitops/sign-extend")
(include-book "bitops/install-bit")
(include-book "bitops/rotate")
(include-book "bitops/ash-bounds")
(include-book "bitops/defaults")
(include-book "bitops/saturate")
(include-book "bitops/signed-byte-p")

(include-book "bridge/top")

(include-book "clex/example")

(include-book "countereg-gen/top" :dir :system)

(include-book "defrstobj/defrstobj")

(include-book "esim/stv/stv-top")
(include-book "esim/stv/stv-debug")
(include-book "esim/esim-sexpr-correct")

(include-book "centaur/getopt/top" :dir :system)
(include-book "centaur/getopt/demo" :dir :system)

(include-book "gl/gl")
(include-book "gl/bfr-aig-bddify")
(include-book "gl/gl-ttags")
(include-book "gl/gobject-type-thms")
(include-book "gl/bfr-satlink")

(include-book "misc/top")
(include-book "misc/smm")
(include-book "misc/tailrec")
(include-book "misc/hons-remove-dups")
(include-book "misc/seed-random")
(include-book "misc/load-stobj")
(include-book "misc/load-stobj-tests")
(include-book "misc/count-up")

;; BOZO conflicts with something in 4v-sexpr?

;; (include-book "misc/remove-assoc")
;; (include-book "misc/sparsemap")
;; (include-book "misc/sparsemap-impl")
(include-book "misc/stobj-swap")

(include-book "oslib/top" :dir :system)

(include-book "regex/regex-ui" :dir :system)

(include-book "regression/common")

(include-book "std/top" :dir :system)
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/lists/nth" :dir :system)

(include-book "ubdds/lite")
(include-book "ubdds/param")

(include-book "vcd/vcd")
(include-book "vcd/esim-snapshot")
(include-book "vcd/vcd-stub")
;; BOZO causes some error with redefinition?  Are we loading the right
;; books above?  What does stv-debug load?
;; (include-book "vcd/vcd-impl")

(include-book "vl/top")
(include-book "vl/kit/top")
(include-book "vl/mlib/clean-concats")
(include-book "vl/mlib/atts")
(include-book "vl/mlib/json")
(include-book "vl/transforms/xf-clean-selects")
(include-book "vl/transforms/xf-propagate")
(include-book "vl/transforms/xf-expr-simp")
(include-book "vl/transforms/xf-inline")
(include-book "vl/mlib/sub-counts")

;; BOZO these are incompatible?  which is right?
(include-book "vl/util/prefix-hash")
;;(include-book "vl/util/prefixp")

(include-book "vl/checkers/use-set-tool")

;; BOZO uh, incompatible with lint?  is this dead?
;; (include-book "vl/lint/xf-drop-unresolved-submodules")
(include-book "vl/mlib/lvalues-mentioning")
(include-book "vl/mlib/rvalues")
(include-book "vl/mlib/ram-tools")


(include-book "hacking/all" :dir :system)
(include-book "hints/consider-hint" :dir :system)
(include-book "tools/do-not" :dir :system)

(include-book "tutorial/intro")
(include-book "tutorial/alu16-book")
(include-book "tutorial/counter")


#||

;; This is a nice place to put include-book scanner hacks that trick cert.pl
;; into certifying unit-testing books that don't actually need to be included
;; anywhere.  This just tricks the dependency scanner into building
;; these books.

(include-book "defrstobj/basic-tests")
(include-book "cutil/deflist-tests" :dir :system)
(include-book "cutil/defalist-tests" :dir :system)
(include-book "cutil/defmapappend-tests" :dir :system)
(include-book "cutil/defprojection-tests" :dir :system)
(include-book "cutil/tools/assert-return-thms" :dir :system)
(include-book "centaur/misc/tshell-tests" :dir :system)

(include-book "defrstobj/groundwork/demo1")
(include-book "defrstobj/groundwork/demo2")
(include-book "defrstobj/groundwork/demo3")
(include-book "defrstobj/groundwork/demo4")
(include-book "defrstobj/groundwork/demo5")

(include-book "ubdds/sanity-check-macros")

;; BOZO why do we care about coi/records/fast?
(include-book "../coi/records/fast/log2")
(include-book "../coi/records/fast/memory")
(include-book "../coi/records/fast/memory-impl")
(include-book "../coi/records/fast/memtree")
(include-book "../coi/records/fast/private")

(include-book "../memoize/old/case")
(include-book "../memoize/old/profile")
(include-book "../memoize/old/watch")
(include-book "../memoize/portcullis")
(include-book "../memoize/tests")
(include-book "../memoize/top")

||#

; Historically we had a completely ad-hoc organization that grew organically as
; topics were added.  This turned out to be a complete mess.  To make the
; manual more approachable and relevant, we now try to impose a better
; hierarchy and add some context.

(local
 (defxdoc acl2::top

; The TOP topic will be the first thing the user sees when they open the
; manual!  We localize this because you may want to write your own top topics
; for custom manuals.

   :short "User manual for the <a
href='http://www.cs.utexas.edu/users/moore/acl2/'>ACL2 Theorem Prover</a> and
the <a href='http://acl2-books.googlecode.com/'>ACL2 Community Books</a>."

   :long "<h3>Introduction</h3>

<p><a href='http://www.cs.utexas.edu/users/moore/acl2/'>ACL2</a> is an
interactive theorem prover.  It combines a Lisp-based programming language for
developing formal models of systems with a reasoning engine that can prove
properties about these models.  It has been used to <a
href='http://en.wikipedia.org/wiki/Formal_verification'>formally verify</a>
many <see topic='@(url interesting-applications)'>interesting systems</see> in
academia and industry.</p>

<p>The <a href='http://acl2-books.googlecode.com/'>ACL2 Community Books</a> are
the canonical set of open-source libraries (\"@(see books)\") for ACL2.  They
include lemma libraries for reasoning in many domains, macro libraries for more
quickly writing and documenting code, interfacing tools for connecting ACL2 to
other systems, productivity tools for better proof automation and debugging,
and specialty libraries for areas like hardware verification.</p>

<p>This documentation is a combined manual that covers ACL2 and the Community
Books.  It is derived from both the classic @(see doc-string)s found in the
ACL2 source code and certain books, and also from the @(see xdoc) topics found
in other books.  Beyond just importing the documentation, we also rearrange the
topic hierarchy to try to improve its organization.</p>

<p>This manual is very much a work in progress.  If you would like to
contribute to its development, please join the <a
href='https://code.google.com/p/acl2-books/'>acl2-books</a> project!</p>"))

(defsection arithmetic
  :parents (top)
  :short "Libraries for reasoning about basic arithmetic, bit-vector
arithmetic, modular arithmetic, etc.")

(defsection boolean-reasoning
  :parents (top)
  :short "Libraries related to representing and processing Boolean functions,
geared toward large-scale automatic reasoning, e.g., via SAT solving and AIG or
BDD packages."

  :long "<h3>Introduction</h3>

<p><a href='http://en.wikipedia.org/wiki/Boolean_function'>Boolean
functions</a> are widely useful throughout mathematical logic, computer
science, and computer engineering.  In formal verification, they are especially
interesting because many high-capacity, fully automatic techniques are known
for analyzing, comparing, and simplifying them; for instance, see <a
href='http://en.wikipedia.org/wiki/Binary_decision_diagram'>binary decision
diagrams</a> (bdds), <a
href='http://en.wikipedia.org/wiki/Boolean_satisfiability_problem'>SAT
solvers</a>, <a
href='http://en.wikipedia.org/wiki/And-inverter_graph'>and-inverter
graphs</a> (aigs), <a href='http://en.wikipedia.org/wiki/Model_checking'>model
checking</a>, <a
href='http://en.wikipedia.org/wiki/Formal_equivalence_checking'>equivalence
checking</a>, and so forth.</p>

<h3>Libraries for Boolean Functions</h3>

<p>We have developed some libraries for working with Boolean functions, for
instance:</p>

<ul>

<li>@(see satlink) provides a representation of <a
href='http://en.wikipedia.org/wiki/Conjunctive_normal_form'>conjunctive normal
form</a> formulas and a way to call SAT solvers from ACL2 and trust their
results.</li>

<li>Libraries like @(see aig) and @(see ubdd) provide @(see hons)-based AIG and
BDD packages.</li>

<li>@(see aignet) provides a more efficient, @(see stobj)-based AIG
representation similar to that used by <a
href='http://www.eecs.berkeley.edu/~alanmi/abc/'>ABC</a>.</li>

</ul>

<p>These libraries are important groundwork for the @(see gl) framework for
bit-blasting ACL2 theorems, and may be of interest to anyone who is trying to
develop new, automatic tools or proof techniques.</p>

<h3>Libraries for Four-Valued Logic</h3>

<p>Being able to process large-scale Boolean functions is especially important
in @(see hardware-verification).  But actually, here, to model certain circuits
and to implement certain algorithms, it can be useful to go beyond Boolean
functions and consider a richer logic.</p>

<p>You might call Boolean functions or Boolean logic a two-valued logic, since
there are just two values (true and false) that any variable can take.  It is
often useful to add a third value, usually called X, to represent an
\"unknown\" value.  In some systems, a fourth value, Z, is added to represent
an undriven wire.  For more on this, see @(see why-4v-logic).</p>

<p>We have developed two libraries to support working in four-valued logic.  Of
these, the @(see 4v) library is somewhat higher level and is generally simpler
and more convenient to work with.  It serves as the basis of the @(see esim)
hardware simulator.  Meanwhile, the @(see faig) library is a bit lower-level
and does not enjoy the very nice @(see 4v-monotonicy) property of @(see
4v-sexprs).  On the other hand, @(see faig)s are closer to @(see aig)s, and can
be useful for loading expressions into @(see aignet) or @(see satlink).</p>

<h3>Related Papers</h3>

<p>Besides the documentation here, you may find the following papers
useful:</p>

<p>Jared Davis and Sol Swords.  <a
href='http://dx.doi.org/10.4204/EPTCS.114.8'>Verified AIG Algorithms in
ACL2.</a>  In ACL2 Workshop 2013. May, 2013. EPTCS 114.  Pages 95-110.</p>

<p>Sol Swords and Jared Davis.  <a
href='http://dx.doi.org/10.4204/EPTCS.70.7'>Bit-Blasting ACL2 Theorems</a>.
In ACL2 Workshop 2011.  November, 2011.  EPTCS 70.  Pages 84-102.</p>

<p>Sol Swords and Warren A Hunt, Jr.  <a
href='http://dx.doi.org/10.1007/978-3-642-14052-5_30'>A Mechanically Verified
AIG to BDD Conversion Algorithm</a>.  In ITP 2010,LNCS 6172, Springer.  Pages
435-449.</p>")

(defsection macro-libraries
  :parents (top macros)
  :short "Generally useful macros for writing more concise code, and frameworks
for quickly introducing concepts like typed structures, typed lists, defining
functions with type signatures, and automating other common tasks.")

(defsection hardware-verification
  :parents (top)
  :short "Libraries for working with hardware description languages, modeling
circuits, etc.")

(defsection proof-automation
  :parents (top)
  :short "Tools, utilities, and strategies for dealing with particular kinds
of proofs.")

(defsection interfacing-tools
  :parents (top)
  :short "Libraries and tools for doing basic <see topic='@(url std/io)'>file
i/o</see>, using raw <see topic='@(url quicklisp)'>Common Lisp libraries</see>,
working with the <see topic='@(url oslib)'>operating system</see>, and
interfacing with <see topic='@(url bridge)'>other programs</see>.")

(defsection debugging
  :parents (top)
  :short "Tools for debugging failed or slow proofs, or misbehaving
functions.")

(defsection macros
  :parents (acl2)
  :short "Macros allow you to extend the syntax of ACL2.")



; Huge stupid hack.  Topics that are documented with the old :DOC system can't
; have XDOC topics for their parents.  So, get them all loaded and converted
; into proper XDOC topics, then move them around where we want them.


(local (xdoc::import-acl2doc))

#!XDOC
(defun change-parents-fn (name new-parents all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'change-parents-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (change-parents-fn name new-parents (cdr all-topics))))
       (topic (cons (cons :parents new-parents)
                    (delete-assoc-equal :parents topic))))
    (cons topic (cdr all-topics))))

#!XDOC
(defmacro change-parents (name new-parents)
  `(table xdoc 'doc
          (change-parents-fn ',name ',new-parents
                             (get-xdoc-table world))))

#!XDOC
(defun force-root-parents (all-topics)
  ;; Assumes the topics have been normalized.
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        nil)
       (topic (car all-topics))
       (name    (cdr (assoc :name topic)))
       (parents (cdr (assoc :parents topic)))
       ((when (or (equal name 'acl2::top)
                  (consp parents)))
        (cons topic (force-root-parents (cdr all-topics))))
       (- (cw "Relinking top-level ~x0 to be a child of TOPICS.~%" name))
       (new-topic
        (cons (cons :parents '(acl2::top))
              topic)))
    (cons new-topic (force-root-parents (cdr all-topics)))))


(defmacro xdoc::fix-the-hierarchy ()
  ;; I make this a macro so I can reuse it in Centaur internal manuals.
  `(progn
     (xdoc::change-parents ihs (arithmetic))

     (xdoc::change-parents b* (macro-libraries))
     (xdoc::change-parents data-definitions (macro-libraries))
     (xdoc::change-parents data-structures (macro-libraries))

     (xdoc::change-parents io (interfacing-tools))
     (xdoc::change-parents hacker (interfacing-tools))

     (xdoc::change-parents witness-cp (proof-automation))
     (xdoc::change-parents gl (proof-automation hardware-verification))
     (xdoc::change-parents esim (hardware-verification))

     (xdoc::change-parents testing (debugging))

;; So I got started on that, and decided to move around a whole bunch of ACL2
;; doc topics.  Much of this would probably make more sense to do in ACL2 itself.

     (xdoc::change-parents copyright (about-acl2))
     (xdoc::change-parents version (about-acl2))
     (xdoc::change-parents release-notes (about-acl2))
     (xdoc::change-parents bibliography (about-acl2))
     (xdoc::change-parents acknowledgments (about-acl2))
     (xdoc::change-parents acl2-help (about-acl2))

     (xdoc::change-parents nqthm-to-acl2 (acl2-tutorial))

     (xdoc::change-parents exit (good-bye))
     (xdoc::change-parents quit (good-bye))

     (xdoc::change-parents |Pages Written Especially for the Tours| (acl2-tutorial))

     (xdoc::change-parents introduction-to-the-tau-system (tau-system))
     (xdoc::change-parents tau-data (tau-system))
     (xdoc::change-parents tau-database (tau-system))

     (xdoc::change-parents wof (io))
     (xdoc::change-parents serialize (io))

     (xdoc::change-parents guard-obligation (guard))
     (xdoc::change-parents guard-debug (guard debugging))
     (xdoc::change-parents verify-guards-formula (guard))
     (xdoc::change-parents print-gv (guard debugging))
     (xdoc::change-parents walkabout (debugging))
     (xdoc::change-parents trace (debugging))
     (xdoc::change-parents time-tracker (debugging))
     (xdoc::change-parents disassemble$ (debugging))
     (xdoc::change-parents splitter (debugging))
     (xdoc::change-parents splitter-output (splitter))
     (xdoc::change-parents immed-forced (splitter))
     (xdoc::change-parents if-intro (splitter))
     (xdoc::change-parents proof-checker (debugging))
     (xdoc::change-parents proof-tree (debugging))
     (xdoc::change-parents pstack (debugging))
     (xdoc::change-parents forward-chaining-reports (debugging))
     (xdoc::change-parents accumulated-persistence (debugging))
     (xdoc::change-parents set-accumulated-persistence (accumulated-persistence))
     (xdoc::change-parents show-accumulated-persistence (accumulated-persistence))
     (xdoc::change-parents dmr (debugging))
     (xdoc::change-parents dynamically-monitor-rewrites (dmr))
     (xdoc::change-parents break-rewrite (debugging))
     (xdoc::change-parents why-brr (break-rewrite))
     (xdoc::change-parents cw-gstack (break-rewrite))

     (xdoc::change-parents default-hints (hints))
     (xdoc::change-parents override-hints (hints))
     (xdoc::change-parents hints-and-the-waterfall (hints))
     (xdoc::change-parents lemma-instance (hints))
     (xdoc::change-parents induct (hints))
     (xdoc::change-parents hands-off (hints))
     (xdoc::change-parents expand (hints))
     (xdoc::change-parents nonlinearp (hints linear-arithmetic))
     (xdoc::change-parents no-thanks (hints))
     (xdoc::change-parents backchain-limit-rw (hints))
     (xdoc::change-parents backtrack (hints))
     (xdoc::change-parents consideration (hints))
     (xdoc::change-parents restrict (hints))
     (xdoc::change-parents reorder (hints))
     (xdoc::change-parents use (hints))
     (xdoc::change-parents by (hints))
     (xdoc::change-parents do-not (hints))
     (xdoc::change-parents do-not-hint (hints))
     (xdoc::change-parents do-not-induct (hints))
     (xdoc::change-parents goal-spec (hints))
     (xdoc::change-parents clause-identifier (goal-spec))


     (xdoc::change-parents otf-flg (defthm thm xargs))

     (xdoc::change-parents package-reincarnation-import-restrictions
                           (defpkg))

     (xdoc::change-parents print-doc-start-column (documentation))
     (xdoc::change-parents proof-supporters-alist (dead-events))

     (xdoc::change-parents cases (hints))
     (xdoc::change-parents custom-keyword-hints (hints))
     (xdoc::change-parents computed-hints (hints))
     (xdoc::change-parents using-computed-hints (computed-hints))
     (xdoc::change-parents using-computed-hints-1 (computed-hints))
     (xdoc::change-parents using-computed-hints-2 (computed-hints))
     (xdoc::change-parents using-computed-hints-3 (computed-hints))
     (xdoc::change-parents using-computed-hints-4 (computed-hints))
     (xdoc::change-parents using-computed-hints-5 (computed-hints))
     (xdoc::change-parents using-computed-hints-6 (computed-hints))
     (xdoc::change-parents using-computed-hints-7 (computed-hints))
     (xdoc::change-parents using-computed-hints-8 (computed-hints))

     (xdoc::change-parents forced (force))
     (xdoc::change-parents forcing-round (force))
     (xdoc::change-parents enable-forcing (force))
     (xdoc::change-parents disable-forcing (force))
     (xdoc::change-parents immediate-force-modep (force))
     (xdoc::change-parents enable-immediate-force-modep (force))
     (xdoc::change-parents disable-immediate-force-modep (force))
     (xdoc::change-parents failed-forcing (force))

     (xdoc::change-parents lambda (term))

     (xdoc::change-parents loop-stopper (rewrite))

     (xdoc::change-parents lp (ld))
     (xdoc::change-parents reset-ld-specials (ld))
     (xdoc::change-parents keyword-commands (ld))
     (xdoc::change-parents ld-error-action (ld))
     (xdoc::change-parents ld-error-triples (ld))
     (xdoc::change-parents ld-evisc-tuple (ld))
     (xdoc::change-parents ld-keyword-aliases (ld))
     (xdoc::change-parents ld-missing-input-ok (ld))
     (xdoc::change-parents ld-post-eval-print (ld))
     (xdoc::change-parents ld-pre-eval-filter (ld))
     (xdoc::change-parents ld-pre-eval-print (ld))
     (xdoc::change-parents ld-prompt (ld))
     (xdoc::change-parents ld-query-control-alist (ld))
     (xdoc::change-parents ld-redefinition-action (ld))
     (xdoc::change-parents ld-skip-proofsp (ld))
     (xdoc::change-parents ld-verbose (ld))
     (xdoc::change-parents prompt (ld))
     (xdoc::change-parents p! (ld))
     (xdoc::change-parents a! (ld))
     (xdoc::change-parents abort! (ld))
     (xdoc::change-parents default-print-prompt (ld))
     (xdoc::change-parents redef (ld))
     (xdoc::change-parents redef- (ld))
     (xdoc::change-parents redef+ (ld))
     (xdoc::change-parents redef! (ld))

     (xdoc::change-parents ignorable (declare))
     (xdoc::change-parents ignore (declare))
     (xdoc::change-parents optimize (declare))
     (xdoc::change-parents type (declare))


     (xdoc::change-parents xargs (defun))
     (xdoc::change-parents measure (xargs))
     (xdoc::change-parents guard-hints (xargs))
     (xdoc::change-parents mode (xargs))
     (xdoc::change-parents non-executable (xargs))
     (xdoc::change-parents normalize (xargs))
     (xdoc::change-parents stobjs (xargs))

     (xdoc::change-parents stobj (programming))
     (xdoc::change-parents defabsstobj (stobj))
     (xdoc::change-parents single-threaded-objects (stobj))


     (xdoc::change-parents obdd (bdd))

     (xdoc::change-parents defund (defun))
     (xdoc::change-parents defun-inline (defun))
     (xdoc::change-parents defund-inline (defun))
     (xdoc::change-parents defun-notinline (defun))
     (xdoc::change-parents defund-notinline (defun))
     (xdoc::change-parents defun-nx (defun))
     (xdoc::change-parents defun-mode (defun))


     (xdoc::change-parents defabbrev (macros))
     (xdoc::change-parents macro-args (macros))
     (xdoc::change-parents &allow-other-keys (macro-args))
     (xdoc::change-parents &body (macro-args))
     (xdoc::change-parents &key (macro-args))
     (xdoc::change-parents &optional (macro-args))
     (xdoc::change-parents &rest (macro-args))
     (xdoc::change-parents &whole (macro-args))
     (xdoc::change-parents trans (macros))
     (xdoc::change-parents trans1 (macros))
     (xdoc::change-parents trans! (macros))
     (xdoc::change-parents defmacro (macros events))
     (xdoc::change-parents make-event (macros events))
     (xdoc::change-parents untranslate-patterns (macros user-defined-functions-table))
     (xdoc::change-parents add-macro-alias (macros switches-parameters-and-modes))
     (xdoc::change-parents add-macro-fn (macros switches-parameters-and-modes))
     (xdoc::change-parents macro-aliases-table (macros switches-parameters-and-modes))
     (xdoc::change-parents remove-binop (macros switches-parameters-and-modes))
     (xdoc::change-parents remove-macro-alias (macros switches-parameters-and-modes))
     (xdoc::change-parents remove-macro-fn (macros switches-parameters-and-modes))
     (xdoc::change-parents untrans-table (macros switches-parameters-and-modes))
     (xdoc::change-parents user-defined-functions-table (macros switches-parameters-and-modes))




     (xdoc::change-parents apropos (docs))

     (xdoc::change-parents certify-book! (certify-book))

     (xdoc::change-parents save-exec (interfacing-tools))

     (xdoc::change-parents wormhole-data (wormhole))
     (xdoc::change-parents wormhole-entry-code (wormhole))
     (xdoc::change-parents wormhole-eval (wormhole))
     (xdoc::change-parents wormhole-implementation (wormhole))
     (xdoc::change-parents wormhole-p (wormhole))
     (xdoc::change-parents wormhole-statusp (wormhole))
     (xdoc::change-parents make-wormhole-status (wormhole))
     (xdoc::change-parents get-wormhole-status (wormhole))
     (xdoc::change-parents set-wormhole-entry-code (wormhole))
     (xdoc::change-parents set-wormhole-data (wormhole))

     (xdoc::change-parents show-bodies (definition))
     (xdoc::change-parents set-body (events definition))

     (xdoc::change-parents the-method (acl2-tutorial))

     (xdoc::change-parents proof-of-well-foundedness (ordinals))
     (xdoc::change-parents o< (ordinals))
     (xdoc::change-parents o-p (ordinals))

     (xdoc::change-parents keyword (keywordp))

     #!XDOC
     (table xdoc 'doc
            (force-root-parents
             (normalize-parents-list
              (clean-topics
               (get-xdoc-table world)))))))

(local (xdoc::fix-the-hierarchy))



(make-event
; xdoc::save is an event, so we might have just called it directly.  But for
; reasons Jared doesn't understand this is screwing up the extended manual we
; build at Centaur.  So, I'm putting the save event into a make-event to try
; to localize its effects to just this book's certification.
 (er-progn (xdoc::save "./manual"
                       ;; Don't import again since we just imported.
                       :import nil
                       ;; For classic mode only...
                       :expand-level 2)
           (value `(value-triple :manual))))