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

; Currently covered: through revision 2167.

  :long "<p>The following is a brief summary of changes made to the <a
href='http://acl2-books.googlecode.com/'>Community Books</a> between the
release of ACL2 6.3 (svn revision 2094) and 6.4 (svn revision ????).  See also
@(see note-6-4) for the changes made to ACL2 itself.</p>

<p>For additional details, you may also see the raw <a
href='http://code.google.com/p/acl2-books/source/list'>commit log</a>.</p>


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


<h3>New Features and Enhancements</h3>

<p>The @('rtl/rel9') library now certifies much faster.</p>

<p>Some functions were renamed in @('coi/generalize') and @('witness-cp') to
avoid name conflicts.</p>

<p>@(see str).  Added a @('str::binify') function, similar to @(see
str::hexify).</p>

<p>@(see vl).  Expanded @(see always-top) with support for basic @('case')
statements.  Expanded @(see expr-simp) to make more reductions and be more
modular.</p>

<p>@(see esim).  Added a compiler from @(see symbolic-test-vectors) into C++
programs.</p>

<p>@(see aig).  New @(see aig-constructors) ruleset.  Minor documentation
enhancements.</p>

<p>@(see aignet).  Released aiger file reader/writers.</p>

<p>@(see 4v-sexprs). Add @(see 4v-sexpr-purebool-p) and related functions for
detecting pure Boolean four valued s-expressions.</p>

<p>@(see gl).  Aded gl-force-true-strong and gl-force-false-strong.  @(see
logcons) can now unify with integer g-number objects.</p>

<p>@(see xdoc).  The @(':xdoc') command now shows from information and prints
parents more nicely.  The fancy viewer now shows what package a topic is from
to avoid confusion.  @(see xdoc::save) more nicely warns about redefined
topics.</p>

<p>The @(see std/util) macros now respect @(see
xdoc::set-default-parents).</p>

<p>@('centaur/tutorial').  The multiplier proof by decomposition now has
comments.</p>

<p>@(see defconsts) now has @(see xdoc) documentation.</p>

<p>Several @(see projects) now have at least minor @(see xdoc) documentation;
see @(see paco), @(see milawa), @(see taspi), @(see jfkr), @(see des), @(see
sha-2), and @(see wp-gen).</p>

<p>coi/util/defun-support now numbers congruence theorems.</p>

<p>coi/nary/nary tweaked with @(see double-rewrite) and examples; see
@('coi/nary/example2.lisp')</p>

<p>Updated version of @('models/jvm/m1/wormhole-abstraction').</p>

<p>A new tool, @('centaur/misc/outer-local'), lets you mark events as
local to an external context.</p>

<p>The Makefile now has many additional targets, which we should document.</p>

<h3>Bug Fixes</h3>

<p>@(see gl). Fixed bug with gl-mbe printing.  Tweaks to counterexample
printing.  Push default @(see gl-bdd-mode) setting lower into the include books
to avoid overwriting user settings.</p>

<p>@(see xdoc). Several bugfixes and cosmetic tweaks.  Moved @(see
xdoc::save) into its own file to make dependency scanning more reliable.
Mostly fix back-button issues with the fancy browser, and fixed up the fancy
viewer to work on Internet Explorer and Safari.</p>

<p>@(see satlink).  SATLINK is now somewhat more permissive in parsing prover
output, for compatibility with more SAT solvers.</p>

<p>Added a workaround for a program-mode bug in SULFA's
@('sat/local-clause-simp.lisp').</p>

<p>Fixed a guard violation in
@('workshops/2004/sumners-ray/support/invp.lisp').</p>


")

