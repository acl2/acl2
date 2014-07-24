; ACL2 Community Books Release Notes
; Copyright (C) 2013-2014 Centaur Technology
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
(include-book "xdoc/top" :dir :system)

;; These books aren't really necessary, but are harmless enough and are useful
;; when debugging the release note markup.
(include-book "centaur/nrev/portcullis" :dir :system)
(include-book "centaur/vl/portcullis" :dir :system)
(include-book "centaur/gl/portcullis" :dir :system)
(include-book "centaur/bed/portcullis" :dir :system)

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

; Currently covered: through revision 2869.

  :long "<p>The following is a brief summary of changes made to the @(see
community-books) between the releases of ACL2 6.4 and 6.5.</p>

<p>The <a
href='https://code.google.com/p/acl2-books/wiki/ReleaseVersionNumbers'>acl2-books
Wiki page on ReleaseVersionNumbers</a> gives SVN revision numbers corresponding
to releases.  See also @(see note-6-5) for the changes made to ACL2 itself.
For additional details, you may also see the raw <a
href='http://code.google.com/p/acl2-books/source/list'>commit log</a>.</p>



<h2>Organization, Build, and Licensing Changes</h2>

<h3>Deleted Stubs</h3>

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


<h3>Book Reorganization</h3>

<p>We've moved several books to new homes in an effort to improve the overall
organization of the books.  Users of these libraries will need to update their
@(see include-book) commands, and in some cases, packages have also
changed.</p>

<p>The table below shows which libraries have moved and where they have moved
to.  Books with stubs may continue to work until the next release, but you'll
need to update your @('include-book')s eventually.</p>


@({
   Stubs?     Previous Location        New Location
  ----------------------------------------------------------------------
    Yes       str/                     std/strings/

    No        memoize/                 centaur/memoize/

    No        centaur/doc.lisp         doc/top.lisp

  ----------------------------------------------------------------------
})

<p>The @(see defpkg) commands for @(see xdoc), @(see std/strings), @(see
std/osets), and @(see std/bitsets) have been merged into a single
@('std/package.lsp') file, with a single corresponding @('std/portcullis.lisp')
file, to simplify package management.</p>


<h3>Name Conflict Resolution</h3>

<p>Preliminary work has been carried out toward unifying coi/std versions of
osets.  In particular:</p>

<ul>
<li>The @(see std/osets) package has been changed from @('SETS') to @('SET').</li>
<li>The @('coi/osets') library now uses the @('std/osets') package files.</li>
<li>Some @('coi/osets') books now merely include the corresponding files from
@('std/osets').</li>
</ul>

<p>The @(see std/lists) function @('repeat') has been renamed to @(see
replicate), and had its arguments reordered, to resolve a name clash with the
coi library.  See <a
href='https://code.google.com/p/acl2-books/issues/detail?id=136'>Issue 136</a>
for additional discussion about this change.</p>

<p>The @('data-structures') library @('STRUCTURES') package has been renamed to
@('DEFSTRUCTURE') to resolve a name conflicts with the COI books.</p>

<p>The @(see bitops) library's @('sign-extend') function has been renamed to
@(see fast-logext) to resolve a name conflict with the @(see rtl) library.</p>

<p>The new @('tools/book-conflicts') tool can be used to detect name conflicts
between books.  See its @('README') file for more information.</p>


<h3>Build System Changes</h3>

<p>Support for ACL2(r) is now directly included in the top-level Makefile.
ACL2(r) users no longer need to use a separate build process and can now make
use of many additional books.  Books that are incompatible with ACL2(r) should
be annotated with @('non-acl2r') @(see cert-param)s, and books that require
ACL2(r) should have a @('uses-acl2r') cert-param.</p>


<p>The top-level Makefile has been made more robust in various ways.</p>

<ul>

<li>Certification of books under @('models/y86') has a cleaner implementation.
These books are no longer certified by the @('make') target @('all') since they
are resource intensive.  For ACL2(h) and host Lisps that can handle this task,
they are certified by using the target @('everything').  Also, the value of the
@('-j') option of the @('make') command is no longer ignored.</li>

<li>It no longer tries to build certain long-running books when USE_QUICKLISP
is set and Hons is not present.</li>

<li>It no longer tries to build the @(see gl) solutions book, as this can
overwhelm modest machines.</li>

<li>A new @('ccl-only') @(see cert-param) can be used for books that require
CCL.  Used this to avoid trying to certify certain books that require, e.g.,
@(see tshell).</li>

<li>The Centaur regression/tutorial books have been removed from
@('doc/top.lisp') to avoid requiring Glucose to build the ACL2+Books
manual.</li>

</ul>


<p>The @(see cert.pl) build system has been enhanced in many ways.  Of
particular note, it now deals more automatically with portcullis files, which
may help to improve the reliability of including uncertified files.  Other
improvements include:</p>

<ul>
 <li>Better support for generated books</li>
 <li>Support for ACL2 images that start up in other packages</li>
 <li>Enhanced @('--help') message with more information</li>
 <li>Added support for @(see add-include-book-dir!)</li>
 <li>More informative error messages in certain cases</li>
 <li>Miscellaneous, minor bug fixes, e.g., support for @('$') in book names.</li>
</ul>


<p>The build speed has been improved in various ways.</p>

<ul>

<li>Many books have reordered @(see include-book) to take advantage of new
optimizations in ACL2.</li>

<li>The performance of the @('tau/bounders/elementary-bounders') book has been
significantly improved, reducing the critical path time for the @('make all')
target.</li>

<li>A computationally expensive proof has been split out of the
@('defung-stress') book, also substantially improving the critical path for
@('make all').</li>

<li>Reduced dependencies in @(see std/util) and @(see xdoc) to speed up
certification.</li>

</ul>

<p>Added a TAGS target to the Makefile.</p>

<p>Added scripts to support using a <a
href='http://jenkins-ci.org/'>Jenkins</a> continuous integration server to
continually rebuild ACL2 and the books on various platforms.</p>


<h3>Licensing Changes</h3>

<p>Books contributed by Centaur Technology are now licensed under a (more
permissive) MIT/X11 style license.  (They were previously licensed under the
GNU General Public License.)</p>

<p>Books contributed by Jared Davis / Kookamara now also have an MIT/X11 style
license instead of the GNU General Public License.</p>

<p>Many books that lacked explicit licensing information have been updated to
include appropriate copyright headers.</p>

<h2>New Libraries, Demos, and Documentation</h2>

<h5>New Libraries and Tools</h5>

<p>The @('workshops/2014') directory contains contributions from the ACL2
Workshop for 2014.</p>

<p>The new @(see remove-hyps) tool may be useful for identifying unnecessary
hypotheses in theorems.</p>

<p>@(see fty::fty) is a new library offers functionality similar to @(see std)
or @(see defdata) libraries.  This library enforces a certain fixing-function
discipline and may help to avoid many type-like hypotheses on theorems.</p>

<p>The new book @('tools/rewrite-with-equality.lisp') is a certified clause
processor that causes certain equality hypotheses to cause massive substitution
of the \"good\" term for the \"bad\" term in clauses that are stable under
simplification.</p>

<p>The new @(see with-supporters) macro can be used to automatically produce
redundant versions of events that are needed from local include books.</p>

<p>The new @(see def-doublevar-induction) macro can be used to create certain
kinds of induction schemes, and may be especially useful for proving @(see
congruence) rules about mutually recursive functions.</p>

<p>The new @(see nrev) book is something like @('nreverse').  It can be used to
implement in-order, tail-recursive list processing functions.  With a trust
tag, these functions can avoid the memory overhead of a final @(see
reverse).</p>

<p>The new @(see fast-alist-pop) function provides something akin to
@('remhash') for fast alists, with various restrictions and limitations.</p>

<p>The new @('system/hons-check') books provide some basic tests for the @(see
hons-and-memoization) code.</p>

<p>The new @('oracle/') directory contains tools and examples from Oracle,
Inc.</p>


<h5>New Demos</h5>

<p>A new demo, @('demos/tutorial-problems/equivalence-of-two-functions'), shows
some ways to prove the equivalence of two functions that recur in different
ways.</p>

<p>A new demo, @('demos/knuth-bendix-problem-1.lisp'), has been added.</p>

<p>COI's @('defung') has a new fractran example: see
@('coi/defung/fractran.lisp').</p>

<p>A new demo, @('demos/gl-and-use-example.lisp'), shows a way to use GL to
establish the crux of an unbounded theorem.</p>


<h5>New Documentation</h5>

<p>The @(see cowles), @(see arithmetic-1), and @(see rtl) libraries now have
some XDOC documentation.</p>

<p>There are now some preliminary recommendations for @(see best-practices) for
developing ACL2 books.</p>

<p>The documentation for portions of the @(see ihs) library and @(see plev) had
been inadvertently excluded from the manual, but are now included.</p>

<p>A new topic describes some noteworthy @(see clause-processors).</p>

<p>The topic hierarchy has received some attention, e.g., all topics that were
formerly listed under the grab-bag @('switches-parameters-and-modes') have been
relocated to more suitable homes.</p>

<p>Converted the documentation for @(see esim), @(see b*), and other topics
into @(see xdoc) format.</p>

<p>Many topics have been improved by eliminating typos, making minor
clarifications, adding appropriate cross-references.</p>



<h2>Changes to Major Libraries</h2>

<h3>XDOC Changes</h3>

<p>The new @(see xdoc::order-subtopics) command can be used to control the
order that subtopics are presented in.</p>

<p>The \"classic\" XDOC viewer is no longer supported.</p>

<p>The XDOC viewers have been improved in many ways.</p>

<ul>

<li>Fancy manuals now produce a clear error message for users of IE8 and IE9,
and will work properly for users of IE11.  (IE10 still works, as before).</li>

<li>Fancy manuals now load much more quickly (faster jump-to box
initialization).</li>

<li>The :doc command and the @(see acl2-doc) tool now show URLs for external
links.</li>

<li>XDOC now includes tools that can create a <a
href='http://www.sitemaps.org/'>sitemap</a> and other \"static\" HTML files,
which may be useful for search engine optimization.</li>

<li>Added .htaccess files to fancy manuals, which can enable server-side
compression for significant file size/performance improvements.</li>

</ul>


<p>Various bugs have also been fixed in the core XDOC system.</p>

<ul>

<li>The @('@(def ...)') directive sometimes printed the wrong event; this has
been fixed.  It also now handles mutually recursive functions more nicely.</li>

<li>The @(see xdoc::save) command should no longer cause an error when trying
to write manuals to paths like @('~/my-manual').</li>

<li>Fixed bugs in XDOC's handling of <tt>@@('...')</tt> and <tt>@@({...})</tt>
directives.</li>

<li>Fixed a problem with @(see xdoc::xdoc-extend) when the topic to extend
lacked a @(':long') string.</li>

</ul>

<p>Other minor changes:</p>

<ul>

<li>XDOC now uses @(see str::pretty) instead of @(see fmt-to-string) and the
preprocessor uses @(see state) less than before.</li>

<li>Factored xdoc tests out of the main directory and excluded them from the
basic build, to improve build times.</li>

</ul>



<h3>@(csee Std) Library Changes</h3>

<h5>@(see std/basic)</h5>

<p>A new book of basic @(see induction-schemes) has been added.</p>

<p>Certain equivalence relations like @(see chareqv) and @(see streqv) have
been factored out of the @(see std/strings) library and moved into
@('std/basic') instead, mainly to improve integration with the new @(see
fty::fty) library.</p>

<p>@(see lnfix) and @(see lifix) are now enabled, inlined functions instead of
macros.  This may help to simplify guard obligations in functions that call
@('lnfix') and @('lifix').</p>


<h5>@(see std/lists)</h5>

<p>An @(see std/lists/update-nth) book has been added.</p>

<p>Added a missing rule about @(see acl2-count) to
@('std/lists/acl2-count').</p>

<p>@(see uniquep) no longer uses @(see equality-variants).  Theorems that
target @('uniquep') should be rewritten in terms of @('no-duplicatesp').</p>

<p>Various books have been reorganized to reduce dependencies.</p>


<h5>@(see std/alists)</h5>

<p>The general purpose alist functions @(see append-alist-vals) and @(see
append-alist-keys) have been moved out of @(see vl) and into @(see
std/alists).</p>

<p>There are new books for @(see alist-fix) and @(see hons-remove-assoc).</p>

<p>The new @('fast-alist-clean') book includes lemmas about @(see
fast-alist-fork) and @(see fast-alist-clean).</p>

<p>Various books have been reorganized to reduce dependencies.</p>


<h5>@(see std/osets)</h5>

<p>Most osets functions are now disabled by default.  They can be re-enabled
using the ruleset @('set::definitions').</p>

<p>Some useful but sometimes expensive rules, including for instance the @(see
set::pick-a-point-subset-strategy) and @(see set::double-containment), and also
including other rules such as the transitivity of @(see set::subset), are now
disabled by default.  They can be re-enabled using the ruleset
@('set::expensive-rules').</p>


<h5>@(see std/util)</h5>

<p>Some new macros have been added.</p>

<ul>

<li>@(see std::defines) can introduce mutually recursive functions, using a
@(see std::define)-like syntax, and features automatic integration with @(see
make-flag).</li>

<li>@(see std::defval) is like @(see defconst) but has @(see xdoc) integration.</li>

<li>@(see std::defsum) is a preliminary macro for tagged union types.</li>

<li>@(see std::defaggrify-defrec) adds @(see std::defaggregate)-style emulation
for structures introduced using @('defrec').</li>

</ul>


<p>The @(see std::define) macro has been improved in many ways.</p>

<ul>

<li>Theorems introduced by @(see std::returns-specifiers) now often have better
names, and the name can also be controlled using @(':name').</li>

<li>The new @(see std::more-returns) macro allows for additional @(see
std::returns-specifiers) style theorems after a @('define').</li>

<li>@(see std::define) now has an option to avoid introducing an
encapsulate.</li>

<li>Refactored @(see std::define) to make it easier to extend, largely in
support of @(see std::defines).</li>

<li>The @(see with-output) macro is now used to avoid printing so much
output.</li>

<li>A performance bug with the @(see var-is-stobj-p) function, notably used by
@('define'), has been fixed.</li>

<li>Experimental <i>post-define hooks</i> can allow for custom actions to be
carried out after submitting a @('define'); such a hook allows for a tight
integration between @('define') and the new @(see fty::fty) library.</li>

</ul>

<p>Other macros have also been improved in various ways.</p>

<ul>

<li>@(see std::defredundant) tool has been expanded to better handle @(see
mutual-recursion) and <see topic='@(url macro-aliases-table)'>macro
aliases</see>.</li>

<li>@(see std::defmvtypes) now has smarter handling of @(see force).</li>

<li>@(see defenum) now automatically produces a fixing function and
forward-chaining rule to give the possible values of the objects.</li>

<li>@(see std::defrule) now has a @(':local') option.</li>

<li>@(see std::deflist) is now smart enough to tell whether functions are
defined; its former @(':already-definedp') option is now useless and, hence,
deprecated.</li>

<li>@(see std::defprojection) now uses @(see nrev::nrev) instead of optimizing
things with @('nreverse') directly, reducing the use of trust tags.</li>

<li>@(see std::defprojection) now accepts @(see std::define)-like syntax for
@(see std::extended-formals) and @(see std::returns-specifiers).</li>

<li>A bug with @(see std::defprojection)'s @('subsetp') theorem has been
fixed.</li>

</ul>

<p>Many macros now have a @(':verbosep') option that can be used to disable
output suppression.</p>

<p>The @('std/util') testing code has been factored out into a new
@('std/util/tests') directory.</p>



<h5>@(see std/typed-lists)</h5>

<p>There are now books for many built-in ACL2 list recognizers that were
previously not covered, e.g., @(see boolean-listp), @(see integer-listp),
etc.</p>


<h5>@(see std/strings)</h5>

<p>Many logical definitions throughout the @(see std/strings) library have been
cleaned up.  Also, many definitions have been changed to use @(see std::define)
for better documentation.</p>

<p>The new book @('std/strings/defs-program') contains @(see program) mode
definitions of most functions in the @('std/strings') library.</p>

<p>The new @(see str::pretty) routine can convert arbitrary ACL2 objects into
pretty-printed strings.  Is a fast, state-free, logic mode reimplementation of
much of ACL2's pretty printer.</p>

<p>There are now a much richer collection of numeric functions, especially for
non-decimal bases; see @(see str::numbers).</p>

<p>The string library now has a very efficient, bitset-like way to represent
sets of characters, and some functions for working with these character
sets. See @(see str::charset-p).</p>


<h5>@(see std/io)</h5>

<p>The @(see read-string) function will now produce better error messages and
can (optionally, via raw Lisp) avoid checking @('bad-lisp-objectp'). </p>


<h3>Defdata Changes</h3>

<p>Defdata's output has been tweaked.</p>

<p>The @(see defdata) library now supports range types.</p>

<p>Counterexample generation has been updated to use tau instead of the former
@('graph-tc') book, and has many other updates.</p>


<h3>COI Changes</h3>

<p>COI's @('def::signature') macro now has support for generalized
congruences.</p>



<h3>@(see Quicklisp) and @(see OSLIB)</h3>

<p>The experimental @(see quicklisp) build has been updated in many ways.
Quicklisp files are now installed under the @('centaur/quicklisp/inst')
directory instead of the user's home directory.</p>

<p>The Quicklisp install can be carried out using a proxy.</p>

<p>The @(see quicklisp) books now include support for the @('bordeaux-threads')
and @('hunchentoot') libraries.</p>

<p>@(see oslib::getpid) has been extended to work on Lisps other than CCL.</p>

<p>Added minimal tests to @(see oslib) functions such as @(see
oslib::file-kind) and @(see oslib::date).</p>

<p>OSLIB has new @(see oslib::lisp-type) and @(see oslib::lisp-version) functions.</p>

<p>A new book, @('centaur/misc/sharedlibs'), may be useful for relocating @(see
save-exec) images that require shared libraries for CCL/Linux systems.</p>

<p>We have remove dependencies on @('iolib') since its build does not seem to
be reliable.</p>


<h2>Changes to Centaur Libraries</h2>


<h3>@(see GL::GL) Changes</h3>

<p>The @('rtl9') library has been updated to better support GL.</p>

<p>GL has better @(see if) handling, and as a result may be better able to cope
with unsatisfiable path conditions (i.e., unreachable code regions) when using
SAT-based @(see gl::modes).</p>

<p>New @(see preferred-definitions) may slightly improve performance of
bit-vector operations like @(see logcar), @(see logcdr), @(see loghead), and
@(see logtail).</p>

<p>Some symbolic arithmetic functions have been changed so as to possibly
improve AIG performance.</p>

<p>GL's rewrites to @(see 4v) constants have been improved.</p>

<p>The new macro @(see gl-thm) is like @(see def-gl-thm), but doesn't store the
theorem.  That is, it's like @(see thm) is to @(see defthm).  Similarly, @(see
gl-param-thm) is to @(see def-gl-param-thm), and @(see def-gl-rule) is similar
to @(see defrule).</p>

<p>The definitions of @('def-gl-thm'), etc., have been simplified, @(see
gl-hint) can now be told which GL clause processor to use.</p>

<p>Minor bugs have been fixed.</p>
<ul>

<li>GL's @(see add-gl-rewrite) macro has been reworked to avoid the possibility
of dropping rules when books are included in different orders.</li>

<li>The GL interpreter now uses the @('clk') from the given @(see
glcp-config).</li>

</ul>

<p>The documentation for GL has been generally improved.</p>


<h3>@(see VL) Verilog Toolkit</h3>

<p>VL has been significantly refactored.  All of the internal @(see vl::syntax)
is now based on @(see fty::fty), which is a major change.  The representation
of @(see vl::statements) is especially different.</p>

<p>VL is beginning to gain support for some limited SystemVerilog constructs.
This is a major change that affects all areas, e.g., lexing, parsing, syntax,
and transformations.</p>

<p>VL now support certain kinds of combinational always blocks.  It also
supports richer edge-triggered always blocks, including, e.g., registers with
asynchronous set/reset signals.</p>

<p>Many bugs have been fixed, some severe.  For instance, VL was incorrectly
translating BUF, NOT, and XNOR gates with \"extra\" terminals.  The new VL
@('systest') directory includes various end-to-end tests of VL's translations
of certain modules.</p>

<p>Warnings have been improved.  For instance, VL now warns about 0-bit
replications since some Verilog tools do not implement them correctly.</p>

<p>Many ttags have been removed from VL, using @(see nrev::nrev).</p>

<p>VL's always/delay transforms can now optionally produce less bitblasted
modules.</p>

<p>The @(see vl::kit) includes new commands such as @('vl gather') and many
commands have additional options.  It also now prints backtraces on errors for
improved debugging.</p>

<p>Numerous other minor bug fixes, extensions, performance improvements,
etc.</p>


<h3>Other Centaur Libraries</h3>

<p>@(see satlink) now uses @('glucose-cert') instead of @('lingeling') as the
default SAT solver.</p>

<p>The default @(see sexpr-rewriting) rules have been expanded and improved.
These changes may improve decomposition proofs and also the performance of
GL-based STV proofs.</p>

<p>@(see tshell) should now handle interrupts more reliably.</p>

<p>The executable counterparts of @(see symbolic-test-vectors) are now disabled
by default.</p>

<p>There is now better support for decomposition proofs of @(see
symbolic-test-vectors), see files such as
@('centaur/esim/stv/stv-decomp-proofs*') and
@('centaur/regression/composed-stv.lisp').</p>

<p>The new @(see stv-run-for-all-dontcares) function is a less conservative
alternative to @(see stv-run).</p>

<p>Some lemmas have been localized in @(see esim).</p>

<p>@(see aignet) now has a basic @(see aignet::aignet-print) function for
debugging.</p>

<p>The @(see bridge::json-encoding) routines now use @(see define) for better
documentation.</p>

<p>Some @(see aignet) functions and @('numlist') are now tail recursive.</p>

<p>The @(see bitops) @('ihsext-basics') book has additional rules about @(see
lognot) and @(see logmask).</p>

<p>Improved and documented the @(see logbitp-reasoning) hint.</p>

<p>Added @(see bit->bool) to the @(see bitops) library.</p>

<p>The new @('centaur/bitops/contrib') directory contains additional lemmas.</p>



<h2>Other Changes</h2>

<p>(File interface/emacs/inf-acl2.el) One now gets a clear error, suggesting a
solution, when Emacs command @('meta-x run-acl2') cannot find an ACL2
executable.  Thanks to Scott Staley for helpful correspondence leading to this
fix.</p>

<p>The @(see make-flag) tool now uses slightly faster, more robust hints.</p>

<p>The @(see witness-cp) clause processor has been made more flexible.</p>

<p>The @('clause-processors/unify-subst') and @('clause-processors/generalize')
books have been reworked to avoid nearly duplicate definitions.</p>

<p>The @(see def-universal-equiv) macro now takes an @('already-definedp')
option.</p>

<p>The @('demos/patterened-congruences.lisp') book has been improved.</p>

<p>The book @('centaur/misc/intern-debugging') book has been modified and
should now be generally unnecessary, thanks to CCL improvements which have
resolved the problems it was intended to warn about.</p>

<p>Something happened to profiling.lisp in r2423.</p>

<p>@(see disassemble$) now supports macro aliases.</p>

<p>Several ordinary files that were incorrectly marked as executable are now
properly non-executable.</p>

<p>The tau @('elementary-bounders') book has been extended with additional
lemmas about @(see expt) for powers of 2.</p>

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
@(see jfkr), @(see milawa), @(see paco), @(see leftist-trees), @(see
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

<h5>@(see std/strings) - string library</h5>
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

<p>A new tool, @('centaur/misc/dag-measure'), may be useful when writing
functions that traverse directed acyclic graphs.</p>

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

<p>Fixed a bug related to undoing inclusion of the @('intern-debugging')
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

