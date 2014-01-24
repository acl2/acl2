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
(set-inhibit-warnings "ttags")
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

(include-book "xdoc/save" :dir :system)

(include-book "relnotes")
(include-book "build/doc" :dir :system)

(include-book "4v-sexpr/top")
(include-book "aig/top")

(include-book "projects/doc" :dir :system)

(include-book "aignet/aig-sim")
(include-book "aignet/copying")
(include-book "aignet/from-hons-aig-fast")
(include-book "aignet/prune")
(include-book "aignet/to-hons-aig")
(include-book "aignet/types")
(include-book "aignet/vecsim")

(include-book "bitops/top")
(include-book "bitops/congruences")
(include-book "bitops/defaults")

(include-book "bridge/top")

(include-book "clex/example")

(include-book "cgen/top" :dir :system)

(include-book "defrstobj/defrstobj")

(include-book "esim/stv/stv-top")
(include-book "esim/stv/stv-debug")
(include-book "esim/esim-sexpr-correct")

(include-book "centaur/getopt/top" :dir :system)
(include-book "centaur/getopt/demo" :dir :system)
(include-book "centaur/getopt/demo2" :dir :system)
(include-book "centaur/bed/top" :dir :system)

(include-book "gl/gl")
(include-book "gl/bfr-aig-bddify")
(include-book "gl/gl-ttags")
(include-book "gl/gobject-type-thms")
(include-book "gl/bfr-satlink")

(include-book "centaur/satlink/top" :dir :system)
(include-book "centaur/satlink/check-config" :dir :system)

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

(include-book "std/top" :dir :system)
(include-book "std/io/unsound-read" :dir :system)
(include-book "std/bitsets/top" :dir :system)

(include-book "std/strings/top" :dir :system)
(include-book "std/strings/base64" :dir :system)

(include-book "ubdds/lite")
(include-book "ubdds/param")

(include-book "vcd/vcd")
(include-book "vcd/esim-snapshot")
(include-book "vcd/vcd-stub")
;; BOZO causes some error with redefinition?  Are we loading the right
;; books above?  What does stv-debug load?
;; (include-book "vcd/vcd-impl")

(include-book "vl/top")
(include-book "vl/doc")
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
;; (include-book "vl/mlib/ram-tools")   obsolete


(include-book "hacking/all" :dir :system)
(include-book "hints/consider-hint" :dir :system)
(include-book "tools/do-not" :dir :system)

; [Jared] removing these to speed up the manual build
;(include-book "tutorial/intro")
;(include-book "tutorial/alu16-book")
;(include-book "tutorial/counter")

; [Jared] removed this to avoid depending on glucose and to speed up
; the manual build
; (include-book "regression/common")


;; Not much doc here, but some theorems from arithmetic-5 are referenced by
;; other topics...
(include-book "arithmetic-5/top" :dir :system)
(include-book "arithmetic/top" :dir :system)

#||

;; This is a nice place to put include-book scanner hacks that trick cert.pl
;; into certifying unit-testing books that don't actually need to be included
;; anywhere.  This just tricks the dependency scanner into building
;; these books.

(include-book "xdoc/all" :dir :system)
(include-book "defrstobj/basic-tests")
(include-book "std/util/deflist-tests" :dir :system)
(include-book "std/util/defalist-tests" :dir :system)
(include-book "std/util/defmapappend-tests" :dir :system)
(include-book "std/util/defprojection-tests" :dir :system)
(include-book "std/util/defredundant-tests" :dir :system)
(include-book "std/util/defval-tests" :dir :system)
(include-book "std/util/extensions/assert-return-thms" :dir :system)
(include-book "centaur/misc/tshell-tests" :dir :system)
(include-book "oslib/tests/top" :dir :system)

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

; The TOP topic will be the first thing the user sees when they open the
; manual!  We localize this because you may want to write your own top topics
; for custom manuals.

 (include-book "doc-top"))

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

<li>Libraries like @(see aig) and @(see ubdds) provide @(see hons)-based AIG and
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
and does not enjoy the very nice @(see 4v-monotonicity) property of @(see
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


(defsection hardware-verification
  :parents (top)
  :short "Libraries for working with hardware description languages, modeling
circuits, etc.")

(defxdoc macro-libraries
  :parents (top macros)
  :short "Generally useful macros for writing more concise code, and frameworks
 for quickly introducing concepts like typed structures, typed lists, defining
 functions with type signatures, and automating other common tasks.")

(defxdoc proof-automation
  :parents (top

; Including acl2 as a parent so that all ACL2 system topics can be found under
; the graph rooted at the acl2 node.

            acl2)
  :short "Tools, utilities, and strategies for dealing with particular kinds
of proofs.")

; Huge stupid hack.  Topics that are documented with the old :DOC system can't
; have XDOC topics for their parents.  So, get them all loaded and converted
; into proper XDOC topics, then move them around where we want them.

(xdoc::import-acl2doc)

(include-book "xdoc/topics" :dir :system)

#!XDOC
(defun change-parents-fn (name new-parents all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'change-parents-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (change-parents-fn name new-parents (cdr all-topics))))
       (- (cw "; Note: changing parents of ~x0 from ~x1 to ~x2.~%"
              name (cdr (assoc :parents topic)) new-parents))
       (topic (cons (cons :parents new-parents)
                    (delete-assoc-equal :parents topic))))
    (cons topic (cdr all-topics))))

#!XDOC
(defmacro change-parents (name new-parents)
  `(table xdoc 'doc
          (change-parents-fn ',name ',new-parents
                             (get-xdoc-table world))))



; These are legacy defdoc topics that need to be incorporated into the
; hierarchy at some sensible places.  These changes are not controversial, so
; we'll do them globally, so they'll be included, e.g., in the Emacs version of
; the combined manual.
(xdoc::change-parents ihs (arithmetic))
(xdoc::change-parents b* (macro-libraries))
(xdoc::change-parents data-definitions (macro-libraries))
(xdoc::change-parents data-structures (macro-libraries))
(xdoc::change-parents hacker (interfacing-tools))
(xdoc::change-parents witness-cp (proof-automation))
(xdoc::change-parents esim (hardware-verification))
(xdoc::change-parents testing (debugging))

(xdoc::change-parents leftist-trees (projects/leftist-trees))
(xdoc::change-parents ltree-sort (leftist-trees))
(xdoc::change-parents how-many-lt (leftist-trees))



#!XDOC
(defun fix-redundant-acl2-parents (all-topics)
  (b* (((when (atom all-topics))
        nil)
       (topic (car all-topics))
       (parents (cdr (assoc :parents topic)))
       (topic (if (or (equal parents '(acl2::top acl2::acl2))
                      (equal parents '(acl2::acl2 acl2::top)))
                  (progn$
                   (cw "; Note: Removing 'redundant' ACL2 parent for ~x0.~%"
                       (cdr (assoc :name topic)))
                   (cons (cons :parents '(acl2::top))
                         (delete-assoc-equal :parents topic)))
                topic)))
    (cons topic
          (fix-redundant-acl2-parents (cdr all-topics)))))


(defsection books-reference
  :parents (books)
  :short "Reference guide for ACL2 functionality related to books, e.g.,
@(see include-book), @(see certify-book), @(see cbd), etc.")

(defxdoc books-tour
  :parents (books)
  :short "The <i>guided tour</i> of concepts related to ACL2 @(see books)."
  :long "<p>The tour begins with @(see book-example).</p>")

(defmacro xdoc::fix-the-hierarchy ()
  ;; Semi-bozo.
  ;;
  ;; This is a place that Jared can put changes that are either experimental or
  ;; under discussion.
  ;;
  ;; Later in this file, I call fix-the-hierarchy, but only LOCALLY, so that it
  ;; only affects the web manual (not the Emacs manual), and not any other
  ;; manuals that include centaur/doc.
  ;;
  ;; I wrap these changes up in a non-local macro so that authors of other
  ;; manuals (e.g., our internal manual at Centaur) can also choose to call
  ;; fix-the-hierarchy if they wish.
  `(progn

     #!XDOC
     (table xdoc 'doc (fix-redundant-acl2-parents
                       (get-xdoc-table acl2::world)))

     (xdoc::change-parents release-notes (about-acl2))
     (xdoc::change-parents consideration (hints))
     (xdoc::change-parents do-not-hint (hints))
     (xdoc::change-parents untranslate-patterns
                           (macros user-defined-functions-table))

     (xdoc::change-parents legacy-documentation (documentation))
     (xdoc::change-parents documentation (top))
     (xdoc::change-parents bdd (boolean-reasoning proof-automation))

     (xdoc::change-parents xdoc (documentation))

     ;; bozo where should this go...
     (xdoc::change-parents unsound-eval (miscellaneous))

     ;; new books documentation stuff
     (xdoc::change-parents books (top))
     (xdoc::change-parents cbd (books-reference))
     (xdoc::change-parents set-cbd (books-reference))
     (xdoc::change-parents book-compiled-file (books-reference))
     (xdoc::change-parents full-book-name (books-reference))
     (xdoc::change-parents pathname (books-reference))

     ;; bury this down within books-certification to help people avoid it
     (xdoc::change-parents books-certification (community-books))
     (xdoc::change-parents books-certification-classic (books-certification))
     (xdoc::change-parents provisional-certification (books-certification))

     ;; Topics associated with the "guided tour" of books
     (xdoc::change-parents book-example (books-tour))
     (xdoc::change-parents book-name (books-tour))
     (xdoc::change-parents book-contents (books-tour))
     (xdoc::change-parents certificate (books-tour))
     (xdoc::change-parents portcullis (books-tour))
     (xdoc::change-parents keep (books-tour))
     (xdoc::change-parents include-book (books-reference books-tour events))
     (xdoc::change-parents certify-book (books-reference books-tour))

     ))

(comp t)

(local (xdoc::fix-the-hierarchy))
(local (deflabel doc-rebuild-label))

(make-event
 (b* ((state (serialize-write "xdoc.sao"
                              (xdoc::get-xdoc-table (w state))
                              :verbosep t)))
   (value '(value-triple "xdoc.sao"))))

(make-event
; xdoc::save is an event, so we might have just called it directly.  But for
; reasons Jared doesn't understand this is screwing up the extended manual we
; build at Centaur.  So, I'm putting the save event into a make-event to try
; to localize its effects to just this book's certification.
 (er-progn (xdoc::save "./manual"
                       ;; Don't import again since we just imported.
                       :import nil
                       ;; Allow redefinition so that we don't have to get
                       ;; everything perfect (until it's release time)
                       :redef-okp t
                       ;; For classic mode only...
                       :expand-level 2)
           (value `(value-triple :manual))))

(local
 (defmacro doc-rebuild ()

; It is sometimes useful to make tweaks to the documentation and then quickly
; be able to see your changes.  This macro can be used to do this, as follows:
;
; SETUP:
;
;  (ld "doc.lisp")  ;; slow, takes a few minutes to get all the books loaded
;
; DEVELOPMENT LOOP: {
;
;   1. make documentation changes in new-doc.lsp; e.g., you can add new topics
;      there with defxdoc, or use commands like change-parents, etc.
;
;   2. type (doc-rebuild) to rebuild the manual with your changes; this only
;      takes 20-30 seconds
;
;   3. view your changes, make further edits
;
; }
;
; Finally, move your changes out of new-doc.lsp and integrate them properly
; into the other sources, and do a proper build.

   `(er-progn
     (ubt! 'doc-rebuild-label)
     (ld ;; newline to fool dependency scanner
      "new-doc.lsp")
     (xdoc::save "./manual"
                 :import nil
                 :redef-okp t
                 :expand-level 2)
     (value `(value-triple :manual)))))
