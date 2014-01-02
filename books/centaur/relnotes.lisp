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

(defxdoc note-6-4-books
  :parents (note-6-4)
  :short "Release notes for the ACL2 Community Books for ACL2 6.4 (???month???,
2013)."

; BOZO this is pretty disorganized.  That probably doesn't matter until it's
; time to release.

; Currently covered: through revision 2342.
; The following URL may be useful for updating the comments here:
;   http://code.google.com/p/acl2-books/source/list

  :long "<p>The following is a brief summary of changes made to the <a
href='http://acl2-books.googlecode.com/'>Community Books</a> between the
release of ACL2 6.3 (svn revision 2094) and 6.4 (svn revision ????).  See also
@(see note-6-4) for the changes made to ACL2 itself.</p>

<p>For additional details, you may also see the raw <a
href='http://code.google.com/p/acl2-books/source/list'>commit log</a>.</p>


<h3>Build System Changes</h3>

<p>The @('books/Makefile') now builds far fewer books than it used to.  BOZO WE
NEED TO DOCUMENT THIS BEFORE THE NEXT RELEASE.</p>


<h3>Deleted Stubs</h3>

<p>When we move a book, we often add a <b>stub</b> book in its previous
location to help you transition your @(see include-book) commands.  The
@('cert.pl') build system prints warnings when a stub book is being
included.</p>

<p>Stub books have a lifespan of one release.  The following books were stubs
in ACL2 6.3, so they have been deleted.</p>

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

<p>We have moved several books to new homes in an effort to clean up the
top-level books/ directory.  Users of these libraries will need to update their
@(see include-book) commands, and in some cases, packages may have also
changed.</p>

<p>The table below shows which libraries have moved and where they have moved
to.  Books with stubs may continue to work until the next release, but you will
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

    No        parallel                 demos/parallel (or systems/parallel)
    No        tutorial-problems        demos/tutorial-problems

    No        workshops/2013-greve-slind    coi/defung

  ----------------------------------------------------------------------
})

<h3>Deprecated Books</h3>

<p>Several books have been eliminated altogether.</p>

<p>The @('rtl/rel7') and @('rtl/rel8') directories have been completely
removed.  Please update to @('rtl/rel9').  Note that rel8 is essentially part
of rel9.  If you can't directly upgrade to @('rel9'), you may try replacing</p>

@({
    (include-book \"rtl/rel8/lib/top\" :dir :system)
})

<p>With:</p>

@({
    (include-book \"rtl/rel9/support/lib3/top\" :dir :system)
    (include-book \"rtl/rel9/arithmetic/top\" :dir :system)
})



<h3>Scripts Moved</h3>

<p>Many build scripts have been relocated from the top-level @('books')
directory, into a new @('books/build') subdirectory.  You may need to update
paths to these files in your Makefiles or other build scripts.</p>



<h3>Documentation Changes</h3>

<p>The ACL2 system documentation has been extracted from the ACL2 sources and
is now located in the Community Books.  See @(see note-6-4) for details; and
see especially @('system/doc/acl2-doc.lisp').</p>

<p>A new Emacs-based documentation browser has been developed by Matt Kaufmann;
see @(see acl2-doc).</p>

<p>Several @(see projects) now have at least minor @(see xdoc) documentation;
see @(see concurrent-programs), @(see des), @(see equational), @(see jfkr),
@(see milawa), @(see paco), @(see projects/leftist-trees), @(see sha-2), @(see
taspi), and @(see wp-gen).</p>

<p>Significant documentation has been added for many books and utilities,
including: the @(see cert.pl) build system, the @(see defconsts) macro, the
@(see defrstobj) macro, and the @(see bitops) library.</p>

<p>Numerous miscellaneous documentation improvements.</p>


<h3>New Features and Enhancements</h3>

<p>RTL.  The @('rtl/rel9') library now certifies much faster.  Clarified
licensing information on RTL libraries.</p>

<p>Some functions were renamed in @('coi/generalize') and @('witness-cp') to
avoid name conflicts.</p>

<p>@(see str).  Added a @('str::binify') function, similar to @(see
str::hexify).</p>

<p>@(see regex).  Added some type theorems to @('regex-ui').</p>

<p>@(see std).  The @(see std::deflist) and @(see std::defprojection) macros
now implement a @(see std::define)-like @('///') syntax.  The @(see std/util)
macros now respect @(see xdoc::set-default-parents).  Added @(see read-string)
utility.  The @(see std::defaggregate) macro now has a new
@(':legiblep :ordered') option, which balances performance and legibility.
@(see std::define) now saves some additional information about definitions in
tables.  A new @(see std/basic) library has been added for basic definitions.
Optimized bitset libraries have been pulled out of @(see bitops) and moved into
@(see std/bitsets) and @(see std/sbitsets).</p>

<p>@(see xdoc).  The @(':xdoc') command now shows @(':from') information and
prints parents more nicely.  The fancy viewer now shows what package a topic is
from to avoid confusion.  @(see xdoc::save) more nicely warns about redefined
topics.  New @('@(`...`)') syntax allows for evaluating Lisp forms directly
within documentation strings; see @(see xdoc::preprocessor).  Added link
checking page to help notice broken links to external web pages.  Added
\"download this manual\" and \"printer friendly\" features.</p>

<p>@(see vl).  Expanded @(see always-top) with support for basic @('case')
statements.  Expanded @(see expr-simp) to make more reductions and be more
modular.  Added new support for hierarchical identifiers.  Cleaned up support
for gate instances.</p>

<p>A new @(see def-dag-measure) tool may be useful when writinf functions that
traverse directed acyclic graphs.</p>

<p>@(see esim).  Added a compiler from @(see symbolic-test-vectors) into C++
programs.  Guards are now verified on @('map-aig-vars-fast').</p>

<p>@(see aig).  New @(see aig-constructors) ruleset.  Minor documentation
enhancements.</p>

<p>@(see aignet).  Released aiger file reader/writers.</p>

<p>@(see 4v-sexprs). Add @(see 4v-sexpr-purebool-p) and related functions for
detecting pure Boolean four valued s-expressions.  Reworked @(see
sexpr-rewriting) to work toward a fixpoint to better support decomposition
proofs.</p>

<p>@(see gl).  Aded gl-force-true-strong and gl-force-false-strong.  @(see
logcons) can now unify with integer g-number objects.  Optimized symbolic
subtraction and @(see logeqv).  Added a vacuity check in AIG mode.  Path
condition handling has been made more efficient in AIG mode.  @(see gl-mbe)
has been reimplemented using @(see gl-assert), a more general mechanism.  A
new @(see gl-concretize) utility gives more control over GL in AIG mode.</p>

<p>@('centaur/tutorial').  The multiplier proof by decomposition now has
comments and is done by rewriting instead of by GL, using a special new theory
available in @('esim/stv/stv-decomp-proofs.lisp').</p>

<p>coi/util/defun-support now numbers congruence theorems.</p>

<p>coi/nary/nary tweaked with @(see double-rewrite) and examples; see
@('coi/nary/example2.lisp')</p>

<p>Updated version of @('models/jvm/m1/wormhole-abstraction').</p>

<p>A new tool, @('centaur/misc/outer-local'), lets you mark events as
local to an external context.</p>

<p>A new tool, @('tools/last-theory-change'), lets you see when a rule was last
enabled or disabled.</p>

<p>The Makefile now has many additional targets, which we should document.</p>

<p>@(see testing).  Various changes in Revision 2225.</p>

<p>@(see defrstobj).  Generalized @(see def-typed-record) to support other
kinds of fixing functions, and miscellaneous cleanup.  Reimplemented defrstobj
to be based on abstract stobjs.  Moved old defrstobj code to @(see
legacy-defrstobj).</p>

<p>@(see bitops).  Added fast @(see bitops/fast-logrev) and @(see bitops/merge)
functions.  Reduced dependencies and use of non-local includes.  Added
significant documentation.</p>

<p>@('clause-processors/magic-ev') now has special handling for OR.</p>

<p>The book @('misc/multi-v-uni.lisp') has been added, which includes a result
from <i>A Mechanically Checked Proof of a Multiprocessor Result via a
Uniprocessor View</i> by J Moore, in Formal Methods in System Design, March
1999.</p>

<p>The book @('misc/enumerate.lisp') has been added, which demonstrates a trick
by J Moore to separately consider all possible cases for a particular term
during a proof.</p>

<h3>Bug Fixes</h3>

<p>The Makefile has been made more robust, especially for ACL2(r).</p>

<p>@(see gl). Fixed bug with gl-mbe printing.  Tweaks to counterexample
printing.  Push default @(see gl-bdd-mode) setting lower into the include books
to avoid overwriting user settings.</p>

<p>@(see xdoc). Several bugfixes and cosmetic tweaks.  Moved @(see xdoc::save)
into its own file to make dependency scanning more reliable.  Mostly fix
back-button issues with the fancy browser.  Fixed fancy viewer to work on
Internet Explorer and Safari.  @('xdoc-extend') now requires the topic being
extended to exist.  Clarified the scope of LICENSE files in XDOC manuals.
Broken links now properly lead to the broken-link topic.</p>

<p>@(see satlink).  SATLINK is now somewhat more permissive in parsing prover
output, for compatibility with more SAT solvers.  Implemented a tail-recursive
@(':exec') version of @(see satlink::eval-formula) to avoid stack overflows.</p>

<p>Added a workaround for a program-mode bug in SULFA's
@('sat/local-clause-simp.lisp').</p>

<p>Fixed guard violations in @('workshops/2004/sumners-ray/support/invp.lisp')
and @('workshops/2009/sumners/support/kas.lisp').</p>

<p>@(see milawa).  Integrated Milawa into @('books/Makefile'); fixed some
issues with @('ccl::') prefixes and other non-portable constructs.</p>

<p>Fixed some issues with the @('centaur/misc/intern-debugging') book and
undoing.</p>

<p>@(see std).  @(see std::defaggregate) now prohibits multiple occurrences of
the same key within a @('make') or @('change') macro.</p>

")

