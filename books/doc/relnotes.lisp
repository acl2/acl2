; ACL2 Community Books Release Notes
; Copyright (C) 2013 Centaur Technology
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
(include-book "xdoc/top" :dir :system)

; Please note:
;
;  - Jared often has uncommitted edits to this file.  Please coordinate with
;    him before editing these topics!
;
;  - Book release notes are typically very disorganized.  This shouldn't be
;    considered a bug until we are very close to a release.
;
;  - The following URL is very useful for updating the comments here:
;       http://code.google.com/p/acl2-books/source/list

(defxdoc note-6-5-books
  :parents (note-6-5)
  :short "Release notes for the ACL2 Community Books for ACL2 6.5 (BOZO month)"

; Currently covered: through revision 2412.

  :long "<h3>Deleted Stubs</h3>

<p>When we move a book, we often add a <b>stub</b> book in its previous
location to help you transition your @(see include-book) commands.  The
@(see cert.pl) build system prints warnings when a stub book is being
included.</p>

<p>Stub books have a lifespan of one release.  The following books were stubs
in ACL2 6.4, so we've deleted them.</p>

@({
     Previous Location                         New Location
   ------------------------------------------------------------------
     cutil/*.lisp                              std/util/*.lisp
     tools/defconsts                           std/util/defconsts

     parallel/with-waterfall-parallelism       misc/with-waterfall-parallelism
     parallel/without-waterfall-parallelism    misc/without-waterfall-parallelism

     serialize/unsound-read                    std/io/unsound-read

     centaur/bitops/bitsets                    std/bitsets/bitsets
     centaur/bitops/bitsets-opt                std/bitsets/bitsets-opt
     centaur/bitops/sbitsets                   std/bitsets/sbitsets
   ------------------------------------------------------------------
})

<h3>Other Changes</h3>

<p>VL: fixed excessive, bogus warnings about design wires in toe transform.</p>

<p>STD: @(see defrule) now has a @(':local') option.</p>

<p>(File interface/emacs/inf-acl2.el) One now gets a clear error, suggesting a
solution, when Emacs command @('meta-x run-acl2') cannot find an ACL2
executable.  Thanks to Scott Staley for helpful correspondence leading to this
fix.</p>

<p>Certification of books under @('models/y86') has a much cleaner
implementation in @('GNUmakefile'), with the result that are no longer
certified by the @('make') target, @('all').  For ACL2(h) and host Lisps that
can handle this task, they are certified by using the target @('everything').
Also, the value of the @('-j') option of the @('make') command is no longer
ignored.</p>

<p>A bug has been fixed in @(see xdoc) preprocessor directive @('@(def ...)'),
which sometimes printed the wrong event.  The bug can be seen in the expansion
of @('@(def alist)') in previous releases of the manual.  The bug was in
community book @('xdoc/preprocess.lisp'), in the definition of function
@('xdoc::get-event*').</p>

")


(defxdoc note-6-4-books
  :parents (note-6-4)
  :short "Release notes for the ACL2 Community Books for ACL2 6.4 (January,
2013)."

  :long "<p>The following is a brief summary of changes made to the @(see
community-books) between the releases of ACL2 6.3 and 6.4.  See the <a
href='https://code.google.com/p/acl2-books/wiki/ReleaseVersionNumbers'>acl2-books
Wiki page on ReleaseVersionNumbers</a> for svn revision numbers corresponding
to releases.  See also @(see note-6-4) for the changes made to ACL2 itself.</p>

<p>For additional details, you may also see the raw <a
href='http://code.google.com/p/acl2-books/source/list'>commit log</a>.</p>


<h3>Build System Changes</h3>

<p>In previous versions of ACL2, the default @('make') command for building the
Community Books could take several hours.  Starting in ACL2 6.4, the default
build is much faster because it <b>excludes many books</b>.</p>

<p>This particularly affects what happens when you run @('make') from the
@('books') directory.  We have <i>not</i> changed how @('make regression')
works from the @('acl2-sources') directory&mdash;it still builds (nearly) all
of the books.</p>

<p>See @(see books-certification) for details about how to use the new build
system.</p>


<h3>Deleted Stubs</h3>

<p>When we move a book, we often add a <b>stub</b> book in its previous
location to help you transition your @(see include-book) commands.  The
@(see cert.pl) build system prints warnings when a stub book is being
included.</p>

<p>Stub books have a lifespan of one release.  The following books were stubs
in ACL2 6.3, so we've deleted them.</p>

@({
   Previous Location                              New Location
 -----------------------------------------------------------------------
   finite-set-theory/osets/sets.lisp              std/osets/top.lisp

   finite-set-theory/osets/map.lisp               std/osets/*
   finite-set-theory/osets/map-tests.lisp
   finite-set-theory/osets/instance.lisp
   finite-set-theory/osets/membership.lisp
   finite-set-theory/osets/sort.lisp
   finite-set-theory/osets/cardinality.lisp
   finite-set-theory/osets/under-set-equiv.lisp
   finite-set-theory/osets/quantify.lisp
   finite-set-theory/osets/computed-hints.lisp
   finite-set-theory/osets/delete.lisp
   finite-set-theory/osets/intersect.lisp
   finite-set-theory/osets/primitives.lisp
   finite-set-theory/osets/union.lisp
   finite-set-theory/osets/difference.lisp
   finite-set-theory/osets/outer.lisp
   finite-set-theory/osets/portcullis.lisp

   std/lists/make-character-list.lisp             str/*
   std/lists/coerce.lisp
   std/misc/explode-atom.lisp
   std/misc/explode-nonnegative-integer.lisp

   std/io/unsigned-byte-listp.lisp                std/typed-lists/*
   std/io/signed-byte-listp.lisp

   std/io/read-object.lisp                        std/io/base.lisp

   centaur/aig/base.lisp                          {aig,faig}-base
   centaur/aig/three-four.lisp                    faig-constructors.lisp

   centaur/misc/resize-list.lisp                  std/lists/resize-list.lisp
   centaur/misc/equal-by-nths.lisp                std/lists/nth.lisp
 -----------------------------------------------------------------------
})


<h3>Book Reorganization</h3>

<p>We've moved several books to new homes in an effort to clean up the
top-level @('books') directory.  Users of these libraries will need to update
their @(see include-book) commands, and in some cases, packages may have also
changed.</p>

<p>The table below shows which libraries have moved and where they have moved
to.  Books with stubs may continue to work until the next release, but you'll
need to update your @('include-book')s eventually.</p>

@({
   Stubs?     Previous Location        New Location
  ----------------------------------------------------------------------
    Yes       cutil (cutil::*)         std/util (std::*)
                                        (see also cutil/README)

    Yes       tools/defconsts          std/util/defconsts

    Yes       serialize/unsound-read   std/io/unsound-read

    No        paco                     projects/paco
    No        milawa                   projects/milawa
    No        taspi                    projects/taspi
    No        security                 projects/security
    No        security/suite-b         projects/security/sha-2
    No        wp-gen                   projects/wp-gen
    No        concurrent-programs      projects/concurrent-programs
    No        deduction/passmore       projects/equational
    No        leftist-trees            projects/leftist-trees
    No        symbolic                 projects/symbolic
    No        translators              projects/translators
    No        quadratic-reciprocity    projects/quadratic-reciprocity

    No        parallel                 misc/ or, for some books,
                                       demos/parallel or system/parallel

    No        tutorial-problems        demos/tutorial-problems

    No        workshops/2013-greve-slind    coi/defung

  ----------------------------------------------------------------------
})

<h3>Deprecated Books</h3>

<p>We've deleted the RTL @('rel7') and @('rel8') directories; please upgrade to
@('rtl/rel9').  Note that @('rel8') is essentially part of @('rel9'), so if you
can't directly upgrade to @('rel9'), you may try replacing</p>

@({
    (include-book \"rtl/rel8/lib/top\" :dir :system)
})

<p>with</p>

@({
    (include-book \"rtl/rel9/support/lib3/top\" :dir :system)
    (include-book \"rtl/rel9/arithmetic/top\" :dir :system)
})



<h3>Scripts Moved</h3>

<p>We've moved many build scripts like @(see cert.pl), @('clean.pl'), and
@('critpath.pl') from the top-level @('books') directory, into a new
@('books/build') directory.  You may need to update paths to these files in
your Makefiles or other build scripts.</p>



<h3>Documentation Changes</h3>

<p>The ACL2 system documentation has been extracted from the ACL2 sources,
converted into @(see xdoc) format, and is now located in the Community Books.
This allows for a tighter integration between the system and book
documentation, e.g., system topics like @(see io) can now directly link to
related libraries like @(see std/io).  See @(see note-6-4) for details; and see
especially the file @('system/doc/acl2-doc.lisp').</p>

<p>A new, feature-rich Emacs-based documentation browser named @(see acl2-doc)
has been developed by Matt Kaufmann, and has many features.</p>

<p>We've added at least some minimal @(see xdoc) documentation for several
@(see projects): see @(see concurrent-programs), @(see des), @(see equational),
@(see jfkr), @(see milawa), @(see paco), @(see projects/leftist-trees), @(see
sha-2), @(see taspi), and @(see wp-gen).</p>

<p>We've added significant documentation for many books and utilities,
including at least:</p>

<ul>
<li>@(see cert.pl) - a build system for certifying ACL2 books</li>
<li>@(see defconsts) - like @('defconst') but supports stobjs, state, and multiple values</li>
<li>@(see defrstobj) - a macro for introducing record-like stobjs</li>
<li>@(see bitops) - an arithmetic library especially for bit-vector arithmetic</li>
<li>@(see def-universal-equiv) - a macro for universally quantified equivalences</li>
<li>@(see arith-equivs) - equivalence relations for naturals, integers, and bits</li>
<li>@(see set-max-mem) - a memory management scheme for ccl</li>
<li>@(see str::base64) - base64 string encoding/decoding</li>
</ul>

<p>We've made hundreds of other minor documentation improvements, and we invite
everyone to contribute improvements.</p>


<h3>Enhancements to Particular Libraries</h3>

<h4>General Libraries</h4>

<h5>@(see std) - standard libraries</h5>
<ul>
<li>A new @(see std/basic) library has been added for basic definitions.</li>
<li>Optimized bitset libraries (formerly in @(see bitops)) are now in @(see std/bitsets).</li>
<li>@(see std/io) has a new @(see read-string) utility.</li>
<li>@(see std::deflist) and @(see std::defprojection) macros now implement @(see std::define)-like @('///') syntax.</li>
<li>The @(see std/util) macros now respect @(see xdoc::set-default-parents).</li>
<li>@(see std::defaggregate) now prohibits duplicate keys in @('make-') and @('change-') macros.</li>
<li>@(see std::defaggregate) macro now has a new @(':legiblep :ordered') option, which balances performance and legibility.</li>
<li>@(see std::define) now saves some additional information about definitions in tables.</li>
<li>Fixed bugs with the @(see untranslate-preprocess) support in @(see define).</li>
</ul>

<h5>@(see str) - string library</h5>
<ul>
<li>Added a @('str::binify') function, similar to @(see str::hexify).</li>
<li>Documented @('binify') and @('hexify').</li>
</ul>

<h5>coi - family of libraries</h5>
<ul>
<li>@('coi/util/defun-support') now numbers congruence theorems.</li>
<li>@('coi/nary/nary') has been tweaked with @(see double-rewrite) and now
has additional examples; see @('coi/nary/example2.lisp')</li>
<li>Fixed name clashes between @('coi/generalize') and @('witness-cp')</li>
</ul>

<h5>@(see bitops) - arithmetic library</h5>
<ul>
<li>Added significant documentation, including overview documentation.</li>
<li>Added fast @(see bitops/fast-logrev) and @(see bitops/merge) functions.</li>
<li>Reduced dependencies and use of non-local includes.</li>
</ul>

<h5>@('rtl') - arithmetic library</h5>

<ul>
<li>@('rtl/rel9') library now certifies much faster.</li>
<li>Clarified licensing information on RTL libraries (GPL).</li>
</ul>

<h5>@(see xdoc) - documentation system</h5>
<ul>
<li>Added support for @('<table>') tags.</li>
<li>Added @(see xdoc::preprocessor) @('@(`...`)') syntax for Lisp evaluation within documentation strings.</li>
<li>The @(':xdoc') command now shows where topics came from, and prints parents more nicely.</li>
<li>@(see xdoc::save) now warns about redefined topics and broken (internal) links.</li>
<li>@(see xdoc::save) now creates a <a href='linkcheck.html'>link checking page</a> to identify broken external links.</li>
<li>@(see xdoc::xdoc-prepend) and @(see xdoc::xdoc-extend) now have additional error checking.</li>
</ul>

<h5>@(see defrstobj) - machine modeling library</h5>
<ul>
<li>Reimplemented defrstobj to be based on abstract stobjs.</li>
<li>Large rstobjs are now faster to define.</li>
<li>Good-rstobj predicates are no longer necessary.</li>
<li>Generalized @(see def-typed-record) to support more general fixing functions,
for better compatibility with new @(see gl) features.</li>
<li>Moved old defrstobj code to @(see legacy-defrstobj).</li>
</ul>


<h5>GL and Boolean Reasoning</h5>

<h5>@(see gl) - bit-blasting tool</h5>
<ul>
<li>Optimized symbolic subtraction and @(see logeqv).</li>
<li>Optimized path condition handling in AIG modes.</li>
<li>Added a vacuity check in AIG modes.</li>
<li>@(see gl-mbe) has been reimplemented using @(see gl::gl-assert), a more general mechanism.</li>
<li>A new @(see gl::gl-concretize) utility gives more control over GL in AIG modes.</li>
<li>Added gl-force-true-strong and gl-force-false-strong.</li>
<li>@(see logcons) can now unify with integer g-number objects.</li>
<li>Fixed a bug with @(see gl-mbe) printing.</li>
<li>Tweaks for better counterexample printing.</li>
<li>Tweaks to avoid overwriting a user's gl-mode by including GL books.</li>
</ul>

<h5>@(see aig) and @(see aignet) - and inverter graph libraries</h5>
<ul>
<li>New @(see aig-constructors) ruleset.</li>
<li>Added aignet <a href='http://fmv.jku.at/aiger/FORMAT'>aiger</a> file reader/writers.</li>
</ul>

<h5>@(see satlink) - interface to sat solvers</h5>
<ul>
<li>Improved compatibility with additional SAT solvers.</li>
<li>Documented various @(see satlink::sat-solver-options) that are known to work.</li>
<li>Added scripts for using solvers with (external, unverified) @(see satlink::unsat-checking) capabilities.</li>
<li>Optimization to avoid stack overflows in @(see satlink::eval-formula).</li>
<li>@(':verbose') mode no longer prints variable assignments (they were sometimes too long for Emacs to handle).</li>
</ul>

<p>@(see bed::bed) is a new, preliminary library for Boolean expression
diagrams.</p>


<h4>Hardware Verification Libraries</h4>

<h5>@(see vl) - Verilog toolkit</h5>
<ul>
<li>Expanded @(see vl::always-top) with support for basic @('case') statements.</li>
<li>Expanded @(see vl::expr-simp) to make more reductions and be more modular.</li>
<li>Added new support for hierarchical identifiers.</li>
<li>Cleaned up support for gate instances.</li>
<li>Multiplier synthesis now better matches GL's multipliers.</li>
<li>Modernized and documented many files.</li>
</ul>

<h5>@(see esim) - symbolic hardware simulator</h5>
<ul>
<li>Added a compiler from @(see symbolic-test-vectors) into C++ programs.</li>
<li>Guards are now verified on @('map-aig-vars-fast').</li>
<li>@('esim/stv/stv-decomp-proofs.lisp') adds a special theory for decomposition
proofs; see the multiplier demo in @('centaur/tutorial').</li>
</ul>

<h5>@(see 4v-sexprs) - four-valued logic of esim</h5>
<ul>
<li>@(see sexpr-rewriting) now works toward a fixpoint to better support decomposition proofs.</li>
<li>Added @(see 4v-sexpr-purebool-p) for detecting pure Boolean 4v-sexprs</li>
<li>Documented @(see sexpr-equivs).</li>
</ul>

<h5>@('centaur/tutorial') - hardware verification demos</h5>
<ul>
<li>The multiplier proof by decomposition now has comments</li>
<li>Added a decomposition proof using rewriting, instead of by GL</li>
</ul>


<h4>New Tools and Examples</h4>

<p>A new tool, @('centaur/misc/outer-local'), lets you mark events as
local to an external context.</p>

<p>A new tool, @('tools/last-theory-change'), lets you see when a rule was last
enabled or disabled.</p>

<p>A new tool, @(see def-dag-measure), may be useful when writing functions
that traverse directed acyclic graphs.</p>

<p>A new book, @('misc/enumerate.lisp'), demonstrates a trick by J Moore to
separately consider all possible cases for a particular term during a
proof.</p>

<p>A new book, @('misc/multi-v-uni.lisp'), includes a result from <i>A
Mechanically Checked Proof of a Multiprocessor Result via a Uniprocessor
View</i> by J Moore, in Formal Methods in System Design, March 1999.</p>

<p>A new book, @('demos/patterned-congruences.lisp) demonstrates @(see
patterned-congruence) rules.</p>


<h4>Miscellaneous Libraries</h4>

<p>Added some type theorems to @('regex-ui').</p>

<p>Updated version of @('models/jvm/m1/wormhole-abstraction').</p>

<p>@('clause-processors/magic-ev') now has special handling for OR.</p>

<p>The @(see testing) library has been enhanced.</p>

<p>@(see tshell) now has improved output-filtering capability, which @(see
satlink) takes advantage of.</p>

<p>@(see def-universal-equiv) now features @(see xdoc) integration.</p>

<p>Fixed a bug related to undoing inclusion of the @(see intern-debugging)
book.</p>

<p>Added a workaround for a program-mode bug in SULFA's
@('sat/local-clause-simp.lisp').</p>

<p>Fixed guard violations in @('workshops/2004/sumners-ray/support/invp.lisp')
and @('workshops/2009/sumners/support/kas.lisp').</p>

<p>Fixed a couple of clashes between @('arithmetic-5')/@('ihs') and @(see
bitops).</p>

<p>@(see milawa).  Integrated Milawa into @('books/Makefile'); fixed some
issues with @('ccl::') prefixes and other non-portable constructs.</p>

<p>The @('ordinals') library is now licensed under a (more permissive)
BSD-style license.</p>


<h3>Other Changes</h3>

<h5>Make system</h5>
<ul>
<li>The Makefile has been made more robust, especially for ACL2(r).</li>
<li>To improve the error message when attempting to use non-GNU implementations
of @('make'), the file @('books/Makefile') has been renamed to
@('books/GNUmakefile').  A trivial @('Makefile') which simply prints an error
has been added for non-GNU makes.</li>
</ul>

<h5>XDOC Fancy Viewer - documentation web pages</h5>

<ul>
<li>Mostly fix back-button issues.</li>
<li>Fixes for compatibility with Internet Explorer and Safari.</li>
<li>Broken links now properly lead to the broken-link topic.</li>
<li>Added \"package box\" to shows what package non-ACL2 topics are from,
    to reduce confusion.</li>
<li>Added <a href='download/'>download this manual</a> feature.</li>
<li>Added <a href='javascript:printer_friendly()'>printer friendly</a> feature</li>
<li>Clarified the scope of LICENSE files in XDOC manuals.</li>
<li>Other bugfixes and cosmetic tweaks.</li>
</ul>")

