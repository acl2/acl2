; ACL2 System+Books Combined XDOC Manual
; Copyright (C) 2008-2014 Centaur Technology
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

(include-book "centaur/misc/memory-mgmt" :dir :system)
(value-triple (set-max-mem (* 10 (expt 2 30))))

(include-book "relnotes")
(include-book "practices")

(include-book "xdoc/save" :dir :system)

(include-book "build/doc" :dir :system)

(include-book "centaur/4v-sexpr/top" :dir :system)
(include-book "centaur/aig/top" :dir :system)

(include-book "projects/doc" :dir :system)

(include-book "centaur/aignet/aig-sim" :dir :system)
(include-book "centaur/aignet/copying" :dir :system)
(include-book "centaur/aignet/from-hons-aig-fast" :dir :system)
(include-book "centaur/aignet/prune" :dir :system)
(include-book "centaur/aignet/to-hons-aig" :dir :system)
(include-book "centaur/aignet/types" :dir :system)
(include-book "centaur/aignet/vecsim" :dir :system)

; The rest of ihs is included elsewhere transitively.
; We load logops-lemmas first so that the old style :doc-strings don't get
; stripped away when they're loaded redundantly later.
(include-book "ihs/logops-lemmas" :dir :system)

(include-book "centaur/bitops/top" :dir :system)
(include-book "centaur/bitops/congruences" :dir :system)
(include-book "centaur/bitops/defaults" :dir :system)

(include-book "centaur/bridge/top" :dir :system)

(include-book "centaur/clex/example" :dir :system)
(include-book "centaur/nrev/demo" :dir :system)

(include-book "cgen/top" :dir :system)

(include-book "centaur/defrstobj/defrstobj" :dir :system)

(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/esim/stv/stv-debug" :dir :system)
(include-book "centaur/esim/esim-sexpr-correct" :dir :system)

(include-book "centaur/getopt/top" :dir :system)
(include-book "centaur/getopt/demo" :dir :system)
(include-book "centaur/getopt/demo2" :dir :system)
(include-book "centaur/bed/top" :dir :system)

(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/gl/bfr-aig-bddify" :dir :system)
(include-book "centaur/gl/gl-ttags" :dir :system)
(include-book "centaur/gl/gobject-type-thms" :dir :system)
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "centaur/gl/def-gl-rule" :dir :system)

(include-book "centaur/satlink/top" :dir :system)
(include-book "centaur/satlink/check-config" :dir :system)

(include-book "centaur/misc/top" :dir :system)
(include-book "centaur/misc/smm" :dir :system)
(include-book "centaur/misc/tailrec" :dir :system)
(include-book "centaur/misc/hons-remove-dups" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(include-book "centaur/misc/load-stobj" :dir :system)
(include-book "centaur/misc/load-stobj-tests" :dir :system)
(include-book "centaur/misc/count-up" :dir :system)
(include-book "centaur/misc/fast-alist-pop" :dir :system)

;; BOZO conflicts with something in 4v-sexpr?

;; (include-book "misc/remove-assoc")
;; (include-book "misc/sparsemap")
;; (include-book "misc/sparsemap-impl")
(include-book "centaur/misc/stobj-swap" :dir :system)

(include-book "oslib/top" :dir :system)

(include-book "regex/regex-ui" :dir :system)

(include-book "std/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)
(include-book "std/io/unsound-read" :dir :system)
(include-book "std/bitsets/top" :dir :system)

(include-book "std/strings/top" :dir :system)
(include-book "std/strings/base64" :dir :system)
(include-book "std/strings/pretty" :dir :system)

; Note, 7/28/2014: if we include
; (include-book "std/system/top" :dir :system)
; instead of the following, we get a name conflict.
(include-book "std/system/non-parallel-book" :dir :system)

(include-book "centaur/ubdds/lite" :dir :system)
(include-book "centaur/ubdds/param" :dir :system)

(include-book "centaur/vcd/vcd" :dir :system)
(include-book "centaur/vcd/esim-snapshot" :dir :system)
(include-book "centaur/vcd/vcd-stub" :dir :system)
;; BOZO causes some error with redefinition?  Are we loading the right
;; books above?  What does stv-debug load?
;; (include-book "vcd/vcd-impl")

(include-book "centaur/vl/top" :dir :system)
(include-book "centaur/vl/doc" :dir :system)
(include-book "centaur/vl/kit/top" :dir :system)
(include-book "centaur/vl/mlib/clean-concats" :dir :system)
(include-book "centaur/vl/mlib/atts" :dir :system)
(include-book "centaur/vl/mlib/json" :dir :system)
(include-book "centaur/vl/transforms/xf-clean-selects" :dir :system)
(include-book "centaur/vl/transforms/xf-propagate" :dir :system)
(include-book "centaur/vl/transforms/xf-expr-simp" :dir :system)
(include-book "centaur/vl/transforms/xf-inline" :dir :system)

;; BOZO these are incompatible?  which is right?
(include-book "centaur/vl/util/prefix-hash" :dir :system)
;;(include-book "vl/util/prefixp")

;; (include-book "vl/mlib/ram-tools")   obsolete


(include-book "hacking/all" :dir :system)
(include-book "hints/consider-hint" :dir :system)
(include-book "tools/do-not" :dir :system)
(include-book "tools/plev" :dir :system)
(include-book "tools/plev-ccl" :dir :system)
(include-book "tools/with-supporters" :dir :system)
(include-book "tools/remove-hyps" :dir :system)
(include-book "clause-processors/doc" :dir :system)

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

(include-book "rtl/rel9/lib/top" :dir :system)
(include-book "rtl/rel9/lib/logn" :dir :system)
(include-book "rtl/rel9/lib/add" :dir :system)
(include-book "rtl/rel9/lib/mult" :dir :system)

(include-book "centaur/fty/deftypes" :dir :system)

#||

;; This is a nice place to put include-book scanner hacks that trick cert.pl
;; into certifying unit-testing books that don't actually need to be included
;; anywhere.  This just tricks the dependency scanner into building
;; these books.

(include-book "xdoc/all" :dir :system)

(include-book "xdoc/tests/preprocessor-tests" :dir :system)
(include-book "xdoc/tests/unsound-eval-tests" :dir :system)
(include-book "xdoc/tests/defsection-tests" :dir :system)
(include-book "centaur/defrstobj/basic-tests" :dir :system)
(include-book "std/util/tests/top" :dir :system)
(include-book "std/util/extensions/assert-return-thms" :dir :system)
(include-book "centaur/misc/tshell-tests" :dir :system)
(include-book "oslib/tests/top" :dir :system)

(include-book "centaur/ubdds/sanity-check-macros" :dir :system)

;; BOZO why do we care about coi/records/fast?
(include-book "coi/records/fast/log2" :dir :system)
(include-book "coi/records/fast/memory" :dir :system)
(include-book "coi/records/fast/memory-impl" :dir :system)
(include-book "coi/records/fast/memtree" :dir :system)
(include-book "coi/records/fast/private" :dir :system)

(include-book "centaur/memoize/old/case" :dir :system)
(include-book "centaur/memoize/old/profile" :dir :system)
(include-book "centaur/memoize/old/watch" :dir :system)
(include-book "centaur/memoize/portcullis" :dir :system)
(include-book "centaur/memoize/tests" :dir :system)
(include-book "centaur/memoize/top" :dir :system)

||#

; Historically we had a completely ad-hoc organization that grew organically as
; topics were added.  This turned out to be a complete mess.  To make the
; manual more approachable and relevant, we now try to impose a better
; hierarchy and add some context.

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
(include-book "xdoc/alter" :dir :system)


; These are legacy defdoc topics that need to be incorporated into the
; hierarchy at some sensible places.  These changes are not controversial, so
; we'll do them globally, so they'll be included, e.g., in the Emacs version of
; the combined manual.
(xdoc::change-parents ihs (arithmetic))
(xdoc::change-parents data-definitions (macro-libraries projects debugging))
(xdoc::change-parents with-timeout (data-definitions))
(xdoc::change-parents data-structures (macro-libraries))
(xdoc::change-parents hacker (interfacing-tools))
(xdoc::change-parents witness-cp (proof-automation))
(xdoc::change-parents testing (debugging))

(xdoc::change-parents leftist-trees (projects))
(xdoc::change-parents ltree-sort (leftist-trees))
(xdoc::change-parents how-many-lt (leftist-trees))

(xdoc::change-parents consideration (hints))
(xdoc::change-parents untranslate-patterns (macros user-defined-functions-table))

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


(defxdoc *acl2-exports*
  :parents (packages)
  :short "Symbols that are often imported into new @(see packages) to provide
easy access to ACL2 functionality."

  :long "<p>When you define a new package for your own work with @(see defpkg),
you will usually want to import many symbols from the @('\"ACL2\"') package,
for instance you will usually want to be able to use symbols like @(see
defthm), @(see in-theory), @(see xargs), @(see state), etc., without an
@('acl2::') prefix.</p>

<p>The constant @('*acl2-exports*') lists @(`(len *acl2-exports*)`) symbols,
including most documented ACL2 system constants, functions, and macros.  You
will typically also want to import many symbols from Common Lisp; see @(see
*common-lisp-symbols-from-main-lisp-package*).</p>

@(`(:code *acl2-exports*)`)")

(defxdoc *common-lisp-symbols-from-main-lisp-package*
  :parents (packages)
  :short "Symbols that are often imported into new packages to provide easy
access to Common Lisp functionality."

  :long "<p>When you define a new package for your own work with @(see defpkg),
you will usually want to import many symbols from the @('\"COMMON-LISP\"')
package so that you can access them without a @('common-lisp::') or @('acl2::')
prefix.</p>

<p>The constant @('*common-lisp-symbols-from-main-lisp-package*') lists the
@(`(len *common-lisp-symbols-from-main-lisp-package*)`) symbols of the
@('COMMON-LISP') package found in <a
href='http://dx.doi.org/10.1145/147135.147249'>dpAns</a>.  You will typically
also want to import many symbols from ACL2; see @(see *acl2-exports*).</p>

@(`(:code *common-lisp-symbols-from-main-lisp-package*)`)")


(defmacro xdoc::fix-the-hierarchy ()
  ;; Semi-bozo.
  ;;
  ;; This is a place that Jared can put changes that are either experimental or
  ;; under discussion.
  ;;
  ;; Later in this file, I call fix-the-hierarchy, but only LOCALLY, so that it
  ;; only affects the web manual (not the Emacs manual), and not any other
  ;; manuals that include doc/top
  ;;
  ;; I wrap these changes up in a non-local macro so that authors of other
  ;; manuals (e.g., our internal manual at Centaur) can also choose to call
  ;; fix-the-hierarchy if they wish.
  `(progn

     #!XDOC
     (table xdoc 'doc (fix-redundant-acl2-parents
                       (get-xdoc-table acl2::world)))

     ;; These run afoul of the acl2-parents issue
     (xdoc::change-parents documentation (top))
     (xdoc::change-parents bdd (boolean-reasoning proof-automation))
     (xdoc::change-parents books (top))

     ;; bozo where should this go... Matt suggests maybe interfacing-tools?
     ;; But by the same token, maybe programming, maybe lots of places...
     (xdoc::change-parents unsound-eval (miscellaneous))

; New proposals from Jared ------------------------------

; Things that were in miscellaneous/other

     (xdoc::change-parents command (history))
     (xdoc::change-parents world (state))
     (xdoc::change-parents props (world))
     (xdoc::change-parents guard (acl2 note1))

     (xdoc::change-parents wormhole (state ld))

     (xdoc::change-parents sharp-comma-reader (defconst))
     (xdoc::change-parents sharp-dot-reader (defconst))

     (xdoc::change-parents computed-hints (hints))


;; stuff from acl2-built-ins

     (defxdoc packages
       :parents (acl2)
       :short "Packages are collections of symbols.  They can be used to avoid name
conflicts when working on large ACL2 projects.")

     (xdoc::change-parents defpkg (packages events))
     (xdoc::change-parents in-package (packages))
     (xdoc::change-parents sharp-bang-reader (packages))
     (xdoc::change-parents pkg-witness (packages))
     (xdoc::change-parents pkg-imports (packages))
     (xdoc::change-parents hidden-death-package (packages))
     (xdoc::change-parents hidden-defpkg (packages))
     (xdoc::change-parents package-reincarnation-import-restrictions (packages))
     (xdoc::change-parents managing-acl2-packages (packages))
     (xdoc::change-parents working-with-packages (best-practices packages))
     (xdoc::change-parents intern (packages))
     (xdoc::change-parents intern-in-package-of-symbol (packages))
     (xdoc::change-parents intern$ (packages))
     (xdoc::change-parents acl2-user (packages))

     (xdoc::change-parents symbol-name (symbolp))
     (xdoc::change-parents symbol-package-name (symbolp packages))
     (xdoc::change-parents symbol-< (symbolp))
     (xdoc::change-parents keywordp (symbolp))
     (xdoc::change-parents add-to-set (symbolp)) ;; bozo horrible name for this function


     (defxdoc numbers
       :parents (acl2)
       :short "Arithmetic functions for working with numbers in ACL2."
       :long "<p>BOZO see @(see |Numbers in ACL2|) for introductory background.
See @(see arithmetic) for libraries for arithmetic reasoning.</p>")

     (xdoc::change-parents *  (numbers))
     (xdoc::change-parents +  (numbers))
     (xdoc::change-parents -  (numbers))
     (xdoc::change-parents /  (numbers))
     (xdoc::change-parents /= (numbers))
     (xdoc::change-parents 1+ (numbers))
     (xdoc::change-parents 1- (numbers))
     (xdoc::change-parents <  (numbers))
     (xdoc::change-parents <= (numbers))
     (xdoc::change-parents =  (numbers))
     (xdoc::change-parents >  (numbers))
     (xdoc::change-parents >= (numbers))

     (xdoc::change-parents acl2-numberp (numbers))
     (xdoc::change-parents acl2-number-listp (numbers))

     (xdoc::change-parents ash (numbers))
     (xdoc::change-parents abs (numbers))
     (xdoc::change-parents binary-* (*))
     (xdoc::change-parents binary-+ (+))
     (xdoc::change-parents boole$ (numbers))
     (xdoc::change-parents ceiling (numbers))
     (xdoc::change-parents complex (numbers))
     (xdoc::change-parents complex-rationalp (numbers))
     (xdoc::change-parents complex/complex-rationalp (numbers))
     (xdoc::change-parents conjugate (numbers))

     (xdoc::change-parents denominator (numbers))
     (xdoc::change-parents expt (numbers))
     (xdoc::change-parents fix (numbers))
     (xdoc::change-parents floor (numbers))
     (xdoc::change-parents ifix (numbers))
     (xdoc::change-parents imagpart (numbers))
     (xdoc::change-parents int= (numbers))
     (xdoc::change-parents integerp (numbers))
     (xdoc::change-parents integer-listp (numbers))
     (xdoc::change-parents integer-length (numbers))

     (xdoc::change-parents logand (numbers))
     (xdoc::change-parents logandc1 (numbers))
     (xdoc::change-parents logandc2 (numbers))
     (xdoc::change-parents logbitp (numbers))
     (xdoc::change-parents logcount (numbers))
     (xdoc::change-parents logeqv (numbers))
     (xdoc::change-parents logior (numbers))
     (xdoc::change-parents lognand (numbers))
     (xdoc::change-parents lognor  (numbers))
     (xdoc::change-parents lognot (numbers))
     (xdoc::change-parents lognor (numbers))
     (xdoc::change-parents logorc1 (numbers))
     (xdoc::change-parents logorc2 (numbers))
     (xdoc::change-parents logtest (numbers))
     (xdoc::change-parents logxor (numbers))
     (xdoc::change-parents max (numbers))
     (xdoc::change-parents min (numbers))
     (xdoc::change-parents mod (numbers))
     (xdoc::change-parents mod-expt (numbers))
     (xdoc::change-parents minusp (numbers))

     (xdoc::change-parents natp (numbers))
     (xdoc::change-parents nat-listp (numbers))
     (xdoc::change-parents nfix (numbers))
     (xdoc::change-parents nonnegative-integer-quotient (numbers))
     (xdoc::change-parents numerator (numbers))

     (xdoc::change-parents oddp (numbers))
     (xdoc::change-parents evenp (numbers))
     (xdoc::change-parents plusp (numbers))
     (xdoc::change-parents posp (numbers))
     (xdoc::change-parents rationalp (numbers))
     (xdoc::change-parents rational-listp (numbers))
     (xdoc::change-parents realpart (numbers))
     (xdoc::change-parents realfix (numbers))
     (xdoc::change-parents real/rationalp (numbers))
     (xdoc::change-parents round (numbers))
     (xdoc::change-parents rem (numbers))
     (xdoc::change-parents rfix (numbers))

     (xdoc::change-parents signed-byte-p (numbers))
     (xdoc::change-parents signum (numbers))
     (xdoc::change-parents truncate (numbers))
     (xdoc::change-parents unary-- (-))
     (xdoc::change-parents unary-/ (/))
     (xdoc::change-parents unsigned-byte-p (numbers))

     (xdoc::change-parents zero-test-idioms (numbers))
     (xdoc::change-parents zerop (numbers))
     (xdoc::change-parents zip (numbers))
     (xdoc::change-parents zp (numbers))
     (xdoc::change-parents zpf (numbers))

     (xdoc::change-parents sharp-u-reader (numbers))

     (defxdoc alists
       :parents (acl2)
       :short "Association lists bind keys to values.")

     (xdoc::change-parents alistp (alists))
     (xdoc::change-parents acons (alists))
     (xdoc::change-parents assoc (alists))
     (xdoc::change-parents assoc-string-equal (alists))
     (xdoc::change-parents delete-assoc (alists))
     (xdoc::change-parents eqlable-alistp (alists))
     (xdoc::change-parents rassoc (alists))
     (xdoc::change-parents put-assoc (alists))
     (xdoc::change-parents rassoc (alists))
     (xdoc::change-parents r-eqlable-alistp (alists))
     (xdoc::change-parents r-symbol-alistp (alists))
     (xdoc::change-parents standard-string-alistp (alists))
     (xdoc::change-parents strip-cars (alists))
     (xdoc::change-parents strip-cdrs (alists))
     (xdoc::change-parents symbol-alistp (alists))

     (xdoc::change-parents assoc-keyword (keyword-value-listp))


     (defxdoc conses
       :parents (acl2)
       :short "A <b>cons</b> is an ordered pair.  In ACL2, data structures like
 @(see lists), @(see alists), etc., are made up of conses.")

     (xdoc::change-parents atom (conses))
     (xdoc::change-parents atom-listp (conses))
     (xdoc::change-parents cons (conses))
     (xdoc::change-parents consp (conses))
     (xdoc::change-parents car (conses))
     (xdoc::change-parents cdr (conses))
     (xdoc::change-parents caaaar (conses))
     (xdoc::change-parents caaadr (conses))
     (xdoc::change-parents caaar (conses))
     (xdoc::change-parents caadar (conses))
     (xdoc::change-parents caaddr (conses))
     (xdoc::change-parents caadr (conses))
     (xdoc::change-parents caar (conses))
     (xdoc::change-parents cadaar (conses))
     (xdoc::change-parents cadadr (conses))
     (xdoc::change-parents cadar (conses))
     (xdoc::change-parents caddar (conses))
     (xdoc::change-parents cadddr (conses))
     (xdoc::change-parents caddr (conses))
     (xdoc::change-parents cadr (conses))
     (xdoc::change-parents cdaaar (conses))
     (xdoc::change-parents cdaadr (conses))
     (xdoc::change-parents cdaar (conses))
     (xdoc::change-parents cdadar (conses))
     (xdoc::change-parents cdaddr (conses))
     (xdoc::change-parents cdadr (conses))
     (xdoc::change-parents cdar (conses))
     (xdoc::change-parents cddaar (conses))
     (xdoc::change-parents cddadr (conses))
     (xdoc::change-parents cddar (conses))
     (xdoc::change-parents cdddar (conses))
     (xdoc::change-parents cddddr (conses))
     (xdoc::change-parents cdddr (conses))
     (xdoc::change-parents cddr (conses))
     (xdoc::change-parents cdr (conses))


     (xdoc::change-parents arrays (acl2))
     (xdoc::change-parents aref1 (arrays))
     (xdoc::change-parents aref2 (arrays))
     (xdoc::change-parents array1p (arrays))
     (xdoc::change-parents array2p (arrays))
     (xdoc::change-parents aset1 (arrays))
     (xdoc::change-parents aset2 (arrays))
     (xdoc::change-parents compress1 (arrays))
     (xdoc::change-parents compress2 (arrays))
     (xdoc::change-parents default (arrays))
     (xdoc::change-parents dimensions (arrays))
     (xdoc::change-parents flush-compress (arrays))
     (xdoc::change-parents header (arrays))
     (xdoc::change-parents maximum-length (arrays))

     (xdoc::change-parents characters (acl2))
     (xdoc::change-parents alpha-char-p (characters))
     (xdoc::change-parents char (characters))
     (xdoc::change-parents char-code (characters))
     (xdoc::change-parents char-downcase (characters))
     (xdoc::change-parents char-equal (characters))
     (xdoc::change-parents char-upcase (characters))
     (xdoc::change-parents char< (characters))
     (xdoc::change-parents char<= (characters))
     (xdoc::change-parents char> (characters))
     (xdoc::change-parents char>= (characters))
     (xdoc::change-parents character-alistp (characters alists))
     (xdoc::change-parents character-listp (characters))
     (xdoc::change-parents characterp (characters))
     (xdoc::change-parents code-char (characters))
     (xdoc::change-parents digit-char-p (characters))
     (xdoc::change-parents digit-to-char (characters))
     (xdoc::change-parents lower-case-p (characters))
     (xdoc::change-parents make-character-list (characters))
     (xdoc::change-parents standard-char-p (characters))
     (xdoc::change-parents standard-char-listp (characters))
     (xdoc::change-parents upper-case-p (characters))

     (xdoc::change-parents make-ord (ordinals))
     (xdoc::change-parents O-finp (ordinals))
     (xdoc::change-parents O-first-coeff (ordinals))
     (xdoc::change-parents O-first-expt (ordinals))
     (xdoc::change-parents O-infp (ordinals))
     (xdoc::change-parents O-p (ordinals))
     (xdoc::change-parents O-rst (ordinals))
     (xdoc::change-parents O< (ordinals))
     (xdoc::change-parents O<= (ordinals))
     (xdoc::change-parents O> (ordinals))
     (xdoc::change-parents O>= (ordinals))

     (xdoc::change-parents io (interfacing-tools))
     (xdoc::change-parents fms (io))
     (xdoc::change-parents Fms! (io))
     (xdoc::change-parents Fmt (io))
     (xdoc::change-parents Fmt1 (io))
     (xdoc::change-parents Fmt1! (io))
     (xdoc::change-parents Fmt! (io))
     (xdoc::change-parents Fmt-to-comment-window (io))
     (xdoc::change-parents printing-to-strings (io))
     (xdoc::change-parents proofs-co (io))
     (xdoc::change-parents msg (io))
     (xdoc::change-parents standard-co (io))
     (xdoc::change-parents standard-oi (io))
     (xdoc::change-parents princ$ (io))
     (xdoc::change-parents observation (io))
     (xdoc::change-parents cw (io))
     (xdoc::change-parents cw! (io))

     ;; I guess Matt just did these
     ;; (xdoc::change-parents pso (prover-output))
     ;; (xdoc::change-parents pso! (prover-output))
     ;; (xdoc::change-parents psof (prover-output))
     ;; (xdoc::change-parents psog (prover-output))
     (xdoc::change-parents gag-mode (prover-output))


     (xdoc::change-parents String (stringp))
     (xdoc::change-parents String-append (stringp))
     (xdoc::change-parents String-downcase (stringp))
     (xdoc::change-parents String-equal (stringp))
     (xdoc::change-parents String-listp (stringp))
     (xdoc::change-parents String-upcase (stringp))
     (xdoc::change-parents String< (stringp))
     (xdoc::change-parents String<= (stringp))
     (xdoc::change-parents String> (stringp))
     (xdoc::change-parents String>= (stringp))
     (xdoc::change-parents Stringp (stringp))

     (xdoc::change-parents coerce (stringp characters))

     (defxdoc errors
       :parents (acl2)
       :short "Support for causing runtime errors, breaks, assertions, etc.")

     (xdoc::change-parents er (errors))
     (xdoc::change-parents illegal (errors))
     (xdoc::change-parents error1 (errors))
     (xdoc::change-parents hard-error (errors))
     (xdoc::change-parents er-progn (errors state))
     (xdoc::change-parents assert$ (errors))
     (xdoc::change-parents break$ (errors))
     (xdoc::change-parents breaks (errors))
     (xdoc::change-parents error-triples (errors state))

     (xdoc::change-parents mbe (guard))
     (xdoc::change-parents mbe1 (mbe))
     (xdoc::change-parents mbt (mbe))
     (xdoc::change-parents must-be-equal (mbe))

     (xdoc::change-parents mv-let (mv))
     (xdoc::change-parents mv-list (mv))
     (xdoc::change-parents mv-nth (mv))
     (xdoc::change-parents mv? (mv))
     (xdoc::change-parents mv?-let (mv))

     (xdoc::change-parents state (acl2))
     (xdoc::change-parents pprogn (state))
     (xdoc::change-parents read-acl2-oracle (state))
     (xdoc::change-parents read-run-time (state))
     (xdoc::change-parents with-live-state (state))
     (xdoc::change-parents state-global-let* (state))
     (xdoc::change-parents setenv$ (state))
     (xdoc::change-parents getenv$ (state))
     (xdoc::change-parents canonical-pathname (state))
     (xdoc::change-parents assign (state))
     (xdoc::change-parents f-put-global (assign))
     (xdoc::change-parents @ (state))
     (xdoc::change-parents f-get-global (@))

     (xdoc::change-parents comp (compilation))
     (xdoc::change-parents comp-gcl (compilation))
     (xdoc::change-parents disassemble$ (compilation debugging))


     (defsection lists
       :parents (acl2)
       :short "Lists of objects, the classic Lisp data structure.")

     (xdoc::change-parents binary-append (append))

     (xdoc::change-parents list (lists))
     (xdoc::change-parents append (lists))
     (xdoc::change-parents butlast (lists))
     (xdoc::change-parents endp (lists))
     (xdoc::change-parents fix-true-list (lists))
     (xdoc::change-parents proper-consp (lists))
     (xdoc::change-parents improper-consp (lists))
     (xdoc::change-parents intersection$ (lists))
     (xdoc::change-parents intersectp (lists))
     (xdoc::change-parents last (lists))
     (xdoc::change-parents len (lists))
     (xdoc::change-parents make-list (lists))
     (xdoc::change-parents list* (lists))
     (xdoc::change-parents listp (lists))
     (xdoc::change-parents member (lists))
     (xdoc::change-parents no-duplicatesp (lists))
     (xdoc::change-parents nth (lists))
     (xdoc::change-parents nthcdr (lists))
     (xdoc::change-parents pairlis (lists))
     (xdoc::change-parents pairlis$ (lists))
     (xdoc::change-parents remove (lists))
     (xdoc::change-parents remove1 (lists))
     (xdoc::change-parents revappend (lists))
     (xdoc::change-parents set-difference$ (lists))
     (xdoc::change-parents subsetp (lists))
     (xdoc::change-parents take (lists))
     (xdoc::change-parents true-listp (lists))
     (xdoc::change-parents true-list-listp (lists))
     (xdoc::change-parents union$ (lists))
     (xdoc::change-parents update-nth (lists))

     (xdoc::change-parents first (nth))
     (xdoc::change-parents rest (nth))
     (xdoc::change-parents second (nth))
     (xdoc::change-parents third (nth))
     (xdoc::change-parents fourth (nth))
     (xdoc::change-parents fifth (nth))
     (xdoc::change-parents sixth (nth))
     (xdoc::change-parents seventh (nth))
     (xdoc::change-parents eighth (nth))
     (xdoc::change-parents ninth (nth))
     (xdoc::change-parents tenth (nth))

     (xdoc::change-parents concatenate (lists stringp))
     (xdoc::change-parents count (lists stringp))
     (xdoc::change-parents length (lists stringp))
     (xdoc::change-parents position (lists stringp))
     (xdoc::change-parents remove-duplicates (lists stringp))
     (xdoc::change-parents reverse (lists stringp))
     (xdoc::change-parents search (lists stringp))
     (xdoc::change-parents subseq (lists stringp))
     (xdoc::change-parents substitute (lists stringp))

     (xdoc::change-parents kwote (pseudo-termp))
     (xdoc::change-parents kwote-lst (pseudo-termp))

     (xdoc::change-parents ec-call (guard))
     (xdoc::change-parents non-exec (guard))
     (xdoc::change-parents the (guard compilation))

     (defxdoc basics
       :parents (acl2)
       :short "Basic control structures like @(see if) and @(see cond), binding
 operators like @(see let) and @(see flet), and @(see mv), and so forth.")

     (xdoc::change-parents and (basics))
     (xdoc::change-parents booleanp (basics))
     (xdoc::change-parents case (basics))
     (xdoc::change-parents case-match (basics))
     (xdoc::change-parents cond (basics))
     (xdoc::change-parents equal (basics))
     (xdoc::change-parents flet (basics))
     (xdoc::change-parents identity (basics))
     (xdoc::change-parents if (basics))
     (xdoc::change-parents iff (basics))
     (xdoc::change-parents implies (basics))
     (xdoc::change-parents let (basics))
     (xdoc::change-parents let* (basics))
     (xdoc::change-parents mv (basics))
     (xdoc::change-parents not (basics))
     (xdoc::change-parents null (basics))
     (xdoc::change-parents quote (basics))
     (xdoc::change-parents or (basics))
     (xdoc::change-parents xor (basics))
     (xdoc::change-parents progn$ (basics))
     (xdoc::change-parents prog2$ (progn$))
     (xdoc::change-parents good-bye (basics))

     (xdoc::change-parents eq (equal))
     (xdoc::change-parents eql (equal))
     (xdoc::change-parents eqlablep (equal))
     (xdoc::change-parents eqlable-listp (equal))

     (xdoc::change-parents sys-call+ (sys-call))
     (xdoc::change-parents sys-call-status (sys-call))

     (xdoc::change-parents getprop (world))
     (xdoc::change-parents putprop (world))

     (xdoc::change-parents cpu-core-count (parallelism))

     (xdoc::change-parents boolean-listp (booleanp))

     (xdoc::change-parents random$ (state numbers))
     (xdoc::change-parents lexorder (<<))
     (xdoc::change-parents alphorder (<<))

     (xdoc::change-parents oracle-apply (state))
     (xdoc::change-parents oracle-apply-raw (state))
     (xdoc::change-parents oracle-funcall (state))

     (xdoc::change-parents check-sum (certificate))

     (xdoc::change-parents fast-alists (alists))
     (xdoc::change-parents cons-subtrees (fast-alists))
     (xdoc::change-parents fast-alist-clean (fast-alists))
     (xdoc::change-parents fast-alist-clean! (fast-alists))
     (xdoc::change-parents fast-alist-fork (fast-alists))
     (xdoc::change-parents fast-alist-fork! (fast-alists))
     (xdoc::change-parents fast-alist-free (fast-alists))
     (xdoc::change-parents fast-alist-free-on-exit (fast-alists))
     (xdoc::change-parents fast-alists-free-on-exit (fast-alists))
     (xdoc::change-parents fast-alist-len (fast-alists))
     (xdoc::change-parents fast-alist-pop (fast-alists))
     (xdoc::change-parents fast-alist-summary (fast-alists))
     (xdoc::change-parents fast-alist-free-on-exit (fast-alists))
     (xdoc::change-parents flush-hons-get-hash-table-link (fast-alist-free))
     (xdoc::change-parents hons-acons (fast-alists))
     (xdoc::change-parents hons-acons! (fast-alists))
     (xdoc::change-parents hons-assoc-equal (fast-alists))
     (xdoc::change-parents hons-get (fast-alists))
     (xdoc::change-parents make-fal (fast-alists))
     (xdoc::change-parents make-fast-alist (fast-alists))
     (xdoc::change-parents with-fast-alist (fast-alists))
     (xdoc::change-parents with-fast-alists (fast-alists))
     (xdoc::change-parents with-stolen-alist (fast-alists))
     (xdoc::change-parents with-stolen-alists (fast-alists))
     (xdoc::change-parents slow-alist-warning (fast-alists))


     (xdoc::change-parents hons (acl2))
     (xdoc::change-parents hons-clear (hons))
     (xdoc::change-parents hons-copy (hons))
     (xdoc::change-parents hons-copy-persistent (hons))
     (xdoc::change-parents hons-equal (hons))
     (xdoc::change-parents hons-equal-lite (hons))
     (xdoc::change-parents hons-make-list (hons))
     (xdoc::change-parents hons-make-list-acc (hons))
     (xdoc::change-parents hons-note (hons))
     (xdoc::change-parents hons-resize (hons))
     (xdoc::change-parents hons-sublis (hons))
     (xdoc::change-parents hons-summary (hons))
     (xdoc::change-parents hons-wash (hons))
     (xdoc::change-parents maybe-wash-memory (hons))
     (xdoc::change-parents normed (hons))

     (xdoc::change-parents memoize (acl2))
     (xdoc::change-parents clear-memoize-tables (memoize))
     (xdoc::change-parents memoize-summary (memoize))
     (xdoc::change-parents memsum (memoize))
     (xdoc::change-parents never-memoize (memoize))
     (xdoc::change-parents restore-memoization-settings (memoize))
     (xdoc::change-parents save-and-clear-memoization-settings (memoize))
     (xdoc::change-parents unmemoize (memoize))
     (xdoc::change-parents clear-memoize-table (memoize))
     (xdoc::change-parents clear-memoize-tables (memoize))
     (xdoc::change-parents clear-hash-tables (memoize))

     (xdoc::change-parents disabledp (theories))


     


     ))

(local

; The TOP topic will be the first thing the user sees when they open the
; manual!  We localize this because you may want to write your own top topics
; for custom manuals.

 (include-book "top-topic"))


(comp t)

(local (xdoc::fix-the-hierarchy))
(local (deflabel doc-rebuild-label))

(make-event
 (b* ((state (serialize-write "xdoc.sao"
                              (xdoc::get-xdoc-table (w state))
                              :verbosep t)))
   (value '(value-triple "xdoc.sao"))))

(value-triple
 (progn$ (cw "--- Writing ACL2+Books Manual ----------------------------------~%")
         :invisible))

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
                       :redef-okp t)
           (value `(value-triple :manual))))

(value-triple
 (progn$ (cw "--- Done Writing ACL2+Books Manual -----------------------------~%")
         :invisible))



; Support for the Emacs-based Manual
;
; Historically this was part of system/doc/render-doc-combined.lisp.  However,
; that file ended up being quite expensive and in the critical path.  Most of
; the expense was that it just had to include-book doc/top.lisp, which takes
; a lot of time because of how many books are included.
;
; So now, instead, to improve performance, we just merge the export of the
; text-based manual into doc/top.lisp.

(include-book "system/doc/render-doc-base" :dir :system)

(defttag :open-output-channel!)

#!XDOC
(acl2::defconsts
 (& & state)
 (state-global-let*
  ((current-package "ACL2" set-current-package-state))
  (b* ((all-topics (force-root-parents
                    (maybe-add-top-topic
                     (normalize-parents-list ; Should we clean-topics?
                      (get-xdoc-table (w state))))))
       ((mv rendered state)
        (render-topics all-topics all-topics state))
       (rendered (split-acl2-topics rendered nil nil nil))
       (outfile (acl2::extend-pathname (cbd)
                                       "../system/doc/rendered-doc-combined.lsp"
                                       state))
       (- (cw "Writing ~s0~%" outfile))
       ((mv channel state) (open-output-channel! outfile :character state))
       ((unless channel)
        (cw "can't open ~s0 for output." outfile)
        (acl2::silent-error state))
       (state (princ$ "; Documentation for acl2+books
; WARNING: GENERATED FILE, DO NOT HAND EDIT!
; The contents of this file are derived from the full acl2+books
; documentation.  For license and copyright information, see community book
; xdoc/fancy/LICENSE.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

(in-package \"ACL2\")

(defconst *acl2+books-documentation* '"
                      channel state))
       (state (fms! "~x0"
                    (list (cons #\0 rendered))
                    channel state nil))
       (state (fms! ")" nil channel state nil))
       (state (newline channel state))
       (state (close-output-channel channel state)))
      (value nil))))



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





#|| 

(redef-errors (get-xdoc-table (w state)))

(defun collect-topics-with-name (name topics)
  (if (atom topics)
      nil
    (if (equal (cdr (assoc :name (car topics))) name)
        (cons (Car topics) (collect-topics-with-name name (Cdr topics)))
      (collect-topics-with-name name (Cdr topics)))))

(b* (((list a b) (collect-topics-with-name 'oslib::lisp-type (get-xdoc-table (w state)))))
  (equal a b))

(b* (((list a b) (collect-topics-with-name 'acl2::ADD-LISTFIX-RULE (get-xdoc-table (w state)))))
  (equal a b))



(defun map-topic-names (x)
  (if (atom x)
      nil
    (cons (cdr (assoc :name (car x)))
          (map-topic-names (cdr x)))))

(map-topic-names (get-xdoc-table (w state)))


(b* (((list a b) (collect-topics-with-name 'oslib::lisp-type (get-xdoc-table (w state)))))
  (equal a b))



(collect-topics-with-name 'acl2::add-listfix-rule (get-xdoc-table (w state)))
||#
