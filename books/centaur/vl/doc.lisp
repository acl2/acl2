; VL Verilog Toolkit
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

(in-package "VL")
(include-book "xdoc/top" :dir :system)

; -----------------------------------------------------------------------------
;
;                   High-Level VL Documentation Topics
;
; -----------------------------------------------------------------------------
;
; This file is just a home for high level documentation topics.  Most of these
; topics could easily be put elsewhere, but keeping them separated from the VL
; source code is convenient because it allows us to edit them without having to
; rebuild any of the rest of VL.

(defxdoc vl
  :parents (hardware-verification)
  :short "The VL Verilog Toolkit is a large ACL2 library for working with <a
href='http://en.wikipedia.org/wiki/SystemVerilog'>SystemVerilog</a> (and also
regular <a href='http://en.wikipedia.org/wiki/Verilog'>Verilog</a>) source
code, developed at Centaur Technology by Jared Davis and Sol Swords.  It serves
as a frontend for many Verilog tools."

  :long "<box><p><b><color rgb='#ff0000'>ALPHA VERSION</color></b>.  The new
development version of VL is not yet ready for public use and may change in
drastic ways without any warning.  Users who want to be on the bleeding edge
should follow the github project to try to keep up to date.  Alternately, see
@(see vl2014::vl2014) for a more stable (but less fully featured) version of
VL.</p></box>

<box><p><b>Note</b>: this documentation is mainly a reference manual.
If you are new to VL, please see @(see getting-started) first.</p></box>")

(defxdoc getting-started
  :parents (vl)
  :short "An introduction to VL, with suggested starting points for how to get
started with evaluating it for use in your own projects."

  :long "<h3>Introduction</h3>

<p><b>VL</b> is an @(see acl2::acl2) library for working with <a
href='http://en.wikipedia.org/wiki/SystemVerilog'>SystemVerilog</a> (and also
regular <a href='http://en.wikipedia.org/wiki/Verilog'>Verilog</a>) source
code, developed at Centaur Technology by Jared Davis and Sol Swords.  At a high
level, VL includes:</p>

<ul>
 <li>An internal representation for Verilog @(see syntax),</li>
 <li>A @(see loader) for parsing Verilog source code into this representation,</li>
 <li>Utilities for inspecting, analyzing, and manipulating these designs,</li>
 <li>Various @(see transforms) that can simplify these designs, and</li>
 <li>Pretty-printing and other report-generation functions.</li>
</ul>

<p>Much of VL is general purpose Verilog processing code that is independent of
particular analysis or back-end tool.  This approach has allowed us to use VL
to implement a family of Verilog-related tools.  Here are some examples:</p>

<ul>

<li>VL can build @(see acl2::sv) models of Verilog modules for formal
verification with ACL2.  This is the basis for much of Centaur's formal
verification efforts.</li>

<li>The VL @(see kit) is a standalone command-line program that you can build
on top of ACL2 and VL.  It provides some high-level commands that you can use
to do things like lint your design directly from the command line.  It also
provides an interactive shell for an instant way to start up ACL2 with VL
already loaded.</li>

<li>VL has been used to build a web-based ``module browser'' that lets you see
the source code for our modules with, e.g., hyperlinks for navigating between
wires and following wires.  This is now integrated into the VL @(see kit); see
@(see vl-server).</li>

<li>(unreleased) We have used VL to implement <i>samev</i>, a sequential
equivalence checking tool with a tick-based timing model that handles both RTL
and transistor-level constructs.</li>

<li>(unreleased) We have used it to implement <i>VL-Mangle</i>, a web-based
Verilog refactoring tool.  A paper describing this tool can be found in: Jared
Davis. <a
href='https://www.kookamara.com/jared/2013-doform-embedding.pdf'>Embedding
ACL Models in End-User Applications</a>.  In <a
href='http://www.cs.bham.ac.uk/research/projects/formare/events/aisb2013/'>Do-Form
2013</a>.  April, 2013, Exeter, UK.</li>

</ul>

<p>We imagine that parts of VL may be useful for implementing other
SystemVerilog processing tools.</p>


<h3>Starting Points</h3>

<p>The first step in using VL for anything is probably to try to get it to
parse your design; see the documentation for the @(see loader).  You may want
to read the notes about @(see supported-constructs).</p>

<p>Once you have parsed your design (or at least some portion of it) you will
have a list of modules.  You might want to at least glance through the
documentation for @(see syntax), which explains how modules are represented.
This may be particularly useful if you are going to write your own analysis
tools.</p>

<p>You may find it useful to pretty-print modules, see for instance @(see
vl-ppcs-module) and perhaps more generally the VL @(see printer).</p>

<p>After getting a feel for how modules are represented, it would be good to
look at the available @(see transforms).  For instance, you might look at the
code for @('run-vl-lint-main') to see a transformation sequence geared toward
linting.  You might also see @(see vl-design->sv-design) to see how the new
@(see sv) flow works.</p>

<p>If you are going to write any Verilog-processing tools of your own, you
should probably read through how VL deals with @(see warnings) and then take a
look at @(see mlib), which provides many functions for working with expressions
and ranges, finding modules and module items, working with the module
hierarchy, generating fresh names, and working with modules at the bit
level.</p>")

(defsection supported-constructs
  :parents (getting-started)
  :short "Notes about the subset of Verilog and SystemVerilog that @(see VL)
  supports."

  :long "<p>VL was originally based on our reading of the <a
href='http://standards.ieee.org/findstds/standard/1364-2005.html'>Verilog-2005
standard, IEEE Std 1364-2005</a>.  When page and section numbers are used
throughout the VL documentation, they are often in reference to this document.
VL now also supports a significant fragment of SystemVerilog, based on our
reading of the <a
href='http://standards.ieee.org/findstds/standard/1800-2012.html'>SystemVerilog-2012
Standard, IEEE 1800-2012</a>.</p>

<p>Verilog and SystemVerilog are huge languages.  Accordingly, VL only supports
a subset of each language.  The precise subset that is supported varies
depending on the particular <i>flow</i> that you are using.  For instance:</p>

<ul>

<li>The older @(see esim) flow was developed primarily to handle Verilog-2005
designs.  It primarily handles RTL-based designs.  It has trouble with
transistor-level constructs, hierarchical identifiers, inout ports, and fancy
procedural statements.  It lacks support for most SystemVerilog features.</li>

<li>The newer @(see acl2::sv) flow provides much better support for
SystemVerilog features like structures, arrays, interfaces, and hierarchical
identifiers.  It does not currently handle transistor-level constructs or
simulation constructs like dynamic arrays, tasks, classes, etc.</li>

<li>The @(see vl-lint) flow can cope with richer SystemVerilog designs.  It is
not especially bothered by transistor-level constructs.  It cannot handle some
simulation constructs, but is able to ignore many constructs when it does not
truly understand them.</li>

</ul>

<p>Regardless of the particular flow you are using, all VL tools reuse the same
loader, internal representation of Verilog @(see syntax).  The loader can read
files as either Verilog-2005 or SystemVerilog-2012.  Regardless of the input
type, we arrive at the same internal representation (essentially
SystemVerilog), and supporting functionality like @(see mlib) and our @(see
printer) all work on this same representation.</p>

<p>VL's @(see preprocessor) is somewhat incomplete.  It basically just supports
@('`define') and @('`ifdef')-related stuff.  It can @('`include') files in the
style of the @('+incdir') options for tools like Verilog-XL, NCVerilog, and
VCS.  It also supports a notion of search paths, which are similar to
@('+libdir') arguments.</p>

<p>The @(see lexer) is essentially complete.</p>

<p>Regarding Veriog-2005, the @(see parser) doesn't currently support specify
blocks and specparams.  In some cases it is smart enough to at least skip over
the unsupported construct.  Depending on what you are doing, this behavior may
be actually appropriate (e.g., skipping specify blocks may be okay if you
aren't trying to deal with low-level timing issues.)</p>

<p>Regarding SystemVerilog-2012, the parser notably lacks support for
SystemVerilog assertions, classes, configs, and probably many other constructs,
and many other particular SystemVerilog extensions may not yet be
implemented.</p>

<p>VL has some ability to tolerate constructs that aren't really supported, and
the general philsophy is that an error in some particular module shouldn't
affect other modules.  If the parser runs into an syntax error or an
unsupported construct, it often only causes that particular module to be
skipped.  When transforms encounter unsupported things or run into problems, we
usually avoid hard errors and instead just add \"fatal @(see warnings)\" to the
module with the problem.</p>")


(defxdoc utilities
  :parents (vl)
  :short "Generic utilities that are unrelated to Verilog processing, but which
are provided by the VL books.")

(defxdoc transforms
  :parents (vl)
  :short "High-level transformations for rewriting and simplifying Verilog
modules.")

(defxdoc mlib
  :parents (vl)
  :short "<b>M</b>odule <b>Lib</b>rary -- A collection of various functions for
working with Verilog modules.")


(defxdoc warning-basics
  :parents (warnings)
  :short "General introduction to @(see vl-warning) objects and error handling
in VL."

  :long "<h3>Introduction</h3>

<p>Many parts of VL can run into situations where we want to issue a warning or
cause an error.  For instance:</p>

<ul>

<li>Our @(see loader) could encounter syntax that is simply malformed, or it
could run into a construct that is legal but that we don't support yet.  It
could also notice valid but strange cases, e.g., @('4'd16') is well-defined but
weird because 16 doesn't fit in 4 bits.</li>

<li>Our @(see transforms) might run into semantically ill-formed constructs,
e.g., perhaps a module declares @('wire [3:0] foo') and then later declares
@('integer foo'), or perhaps we are trying to instantiate a module that is not
defined.</li>

<li>Our @(see vl-lint) checks might notice \"code smells\" where even though
the input Verilog is semantically well-formed, it is somehow strange and looks
like it could be an error.  For instance, perhaps there are multiple
assignments to the same wire, or expressions like @('a & b') where @('a') and
@('b') have different sizes.</li>

</ul>

<p>Handling these many kinds of cases is tricky.  In the earliest days of VL,
our approach to warnings and errors was quite ad-hoc.  We sometimes printed
warning messages to standard output using the @(see cw) function.  For more
serious conditions, we sometimes caused errors using @(see er).  This ad-hoc
approach had a number of problems.  In particular,</p>

<ul>

<li>It led us to see many of the same warnings repeatedly because our various
well-formedness checks were run many times on the same modules in different
stages of the translation.</li>

<li>For some warnings, we did not particularly care about the individual
instances of the warning.  For instance, unless we're interested in fixing the
\"if\" statements to be ?: instead, we don't want to be told about each
occurrence of an if statement.  We just want a higher-level note that hey,
there are 30 if-statements to clean up.</li>

<li>The warnings were not \"attached\" in any way to the modules that they were
actually about.  Practically speaking, this might mean that users might not
even see the warnings that had been generated for the modules they are working
on.</li>

<li>There is no way to recover form an error created with @(see er), so if we
ran into some bad problem with a particular module, it could actually prevent
us from translating <i>any</i> of the modules.  This was particularly
troublesome because Verilog is such a large language that, especially in the
beginning, we often ran into constructs that we did not yet support.</li>

</ul>

<p>These sorts of problems quickly led us to want a more coherent, global
approach to dealing with warnings and errors.</p>


<h3>Warning Objects</h3>

<p>Our new approach to warning and error handling centers around explicit @(see
vl-warning) objects.  These objects are in many ways similar to the <a
href='https://en.wikipedia.org/wiki/Exception_handling'>Exception</a> objects
found in other programming languages.  Each warning has a <b>type</b> and a
<b>message</b> that describes the error.  These messages can conveniently make
use of VL's @(see printer), so you can directly pretty-print arbitrary Verilog
constructs when writing warning messages.</p>

<p>We use @(see vl-warning) objects universally, for all kinds of warnings and
errors.  That is, everything from the most minor of code smells (e.g., @('wire
foo') is never used for anything), to the most severe problems (e.g., the
module you're instantiating isn't defined) results in a warning.  To
distinguish minor oddities from severe problems, our warning objects include a
<b>fatalp</b> field.</p>

<p>As a general philosophy or strategy for using these warning objects:</p>

<ul>

<li>Warning messages should never be printed to standard output.  Instead, we
should create a @(see vl-warning-p) object that provides context and explains
the problem as clearly and concisely as possible.</li>

<li>Errors should not cause sudden, unrecoverable exits.  That is, @(see er)
should never be used for warnings that could plausibly be triggered by
malformed Verilog.  (However, it <i>is</i> reasonable to use @('er') in an <a
href='https://en.wikipedia.org/wiki/Assertion_(software_development)'>assert</a>-like
fashion, to rule out programming problems that we believe are impossible.)</li>

<li>Non-fatal warnings should be used for any issues that are purely stylistic,
\"code smells,\" etc., such as linter-like checks.</li>

<li>Fatal warnings should be used for any issues that are truly errors.  For
instance: malformed syntax, conflicting declarations of some name, references
to undefined modules, etc.</li>

<li>Fatal warnings may also be used when a transform encounters constructs that
are valid but not supported, e.g., because we have simply not yet spent the
time to implement them.</li>

</ul>


<h3>Accumulating Warnings</h3>

<p>Warning objects are simple enough to understand, but what do we actually
<i>do</i> with them?  We adopt another general principle:</p>

<ul>

<li>Every warning object should be associated with the top-level design
elements (e.g., module, package, interface, etc.) where it was caused.</li>

</ul>

<p>This approach allows us to easily do many practically useful things with the
warnings.  For instance, it lets us easily filter out any modules that have
fatal warnings; see @(see propagating-errors).  As another example, we can
create reports such as a @(see vl-reportcard) that summarize the warnings in
our design.  These kinds of capabilities are especially useful in tools like
@(see vl-lint).</p>

<p>Practically implementing this philosophy is slightly tricky.</p>

<p>Deep within some particular transform, we might encounter something that is
wrong and decide to issue a warning.  In a typical object-oriented programming
language, this would be trivial: our module class might have an
@('add-warning') that (destructively) adds a new warning to the module.</p>

<p>But our programming language is truly functional, so we cannot modify
existing modules.  Instead, whenever some subsidiary function wants to produce
a warning, its caller must take measures to ensure that the warning is
eventually added to the appropriate module.</p>

<p>Our usual approach is to add a <b>warnings accumulator</b> as an argument to
our functions.  Typically this argument should be named @('warnings').
Functions that take a warnings accumulator return the (possibly extended)
accumulator as one of their return values.  Macros like @(see ok), @(see warn)
and @(see fatal) can assist with implementing this convention.</p>

<p>At a high level, then, a function that transforms a top-level design
element, e.g., a module, begins by obtaining the current warnings for the
module.  Using these warnings as the initial accumulator, it calls its
subsidiary helpers to carry out its work.  This work transforms various parts
of the module, and meanwhile the warnings are perhaps extended.  Finally, the
function returns a new @(see vl-module-p) which is updated with the extended
list of warnings.</p>")


(defxdoc warnings
  :parents (vl)
  :short "Support for handling warnings and errors."

  :long "<p>Many parts of VL can run into situations where we want to issue
warnings or cause errors.  In these situations, VL creates @(see vl-warning)
objects.  These warnings can be attached to major design elements such as
modules and interfaces.  They can later be collected, examined, filtered,
etc.</p>

<p><b>New users:</b> You may wish to see @(see warning-basics) for a broad
discussion of VL's philosophy toward handling warnings before looking at the
functions below.</p>

<h3>Quick Guide</h3>

<p>VL includes many functions for creating, collecting, printing, filtering,
and otherwise working with warnings.</p>

<ul>

<li>The core warning data structure is a @(see vl-warning), but more often
these are found in a @(see vl-warninglist), which are often called <i>warnings
accumulators</i>.</li>

<li>For <b>creating warnings</b>, there are some convenient macros for extend
warnings accumulators with new warnings; see @(see ok), @(see warn), @(see
fatal).  As a new alternative to warnings accumulators, see also @(see vmsg),
@(see vl-warning-add-ctx), and the special @(see patbind-wmv) binder for @(see
b*).</li>

<li>Functions for <b>displaying, filtering, etc.</b> a warning list include:
<ul>
  <li>@(see vl-warnings-to-string) and @(see vl-print-warnings)</li>
  <li>@(see vl-clean-warnings) and @(see vl-warning-sort)</li>
  <li>@(see vl-keep-warnings) and @(see vl-remove-warnings)</li>
  <li>@(see vl-some-warning-fatalp) and @(see vl-some-warning-of-type-p).</li>
</ul></li>

<li>You can get a @(see vl-reportcard) that <b>summarizes the warnings</b> that
are attached to design elements such as modules, interfaces, etc.  A report
card can also be printed, filtered, etc., see @(see vl-reportcard) for details.
You can alternately extract all of the warnings as a list of @(see
flat-warnings).</li>

<li>Fatal warnings can be <b>propagated</b> throughout a design to transitively
any superior design elements as having fatal warnings somewhere below.  See
@(see propagating-errors).</li>

<li>VL hackers may want to know about @(see vl-trace-warnings), which just
<b>traces warning creation</b> in a nice way so that you can see warnings as
they are created (e.g., between print statements or other kinds of
tracing.)</li>

<li>Warnings are heavily used in @(see vl-lint), which features some special
mechanisms for <b>suppressing warnings</b>; see @(see
lint-warning-suppression).</li>

</ul>")



(defxdoc vl-patternkey-ambiguity
  :parents (vl-patternkey supported-constructs)
  :short "Notes about our handling of @(see vl-patternkey)s."

  :long "<p>The keys in assignment patterns can be expressions (which should
resolve to array indexes, for array patterns), structure member names, type
names, or the special keyword @('default').  Here are some examples:</p>

@({
    '{ 0: a, 1: b, 2: c, default: 0 }    // assign to some array indices, default others...
    '{ foo: 3, bar: 5 }                  // assign to struct members by name (maybe)
    '{ integer: 5, opcode_t: 7 }         // assign to struct members by type (maybe)
})

<p>Simple names are particularly ambiguous here.  For instance, a name like
@('place') might perhaps refer to any of (1) a parameter value to be used as an
array index, as in:</p>

@({
     int arr [3:0];
     parameter place = 0;
     assign arr = '{place: 3, default: 0 };
})

<p>or (2) a structure member name, as in:</p>

@({
     typedef struct { int place; int value; } slot_t;
     slot_t s = '{ place: 3, value: 4 };
})

<p>or (3) the name of some type, as in:</p>

@({
     typedef logic [3:0] place;
     typedef struct { place src; place dest; int data; } msg_t;
     msg_t m = '{ place: 0, data: 0 };
})

<p>This ambiguity is problematic in early parts of @(see annotate), such as
@(see shadowcheck), where we want to check that, e.g., wires are used declared
before they are used.  Here, because of type parameters, we might not be able
to tell the names of a structure's members until elaboration time.  For
example, suppose there is no type named @('place') and that, in some module, we
are have a type parameter @('mytype_t') and an assignment like:</p>

@({
     mytype_t foo = '{ place: 0, ... }
})

<p>In this case, we won't know whether @('place') is the name of a structure
field of @('mytype_t') until elaboration provides us with a definition for
@('mytype_t').  If @('mytype_t') ends up having a member named @('place'), then
it's fine for @('place') not to be declared here.  But if it doesn't have such
a member, then the only way this makes sense is for @('place') to be the name
of some parameter that's being used as an array index, in which case @('place')
needs to be declared here.</p>

<p>Rather than further intertwine shadowcheck and elaborate, our approach is to
avoid this ambiguity by require that all simple names used in assignment
pattern keys <b>must</b> be either the names of types or structure members.
Although NCVerilog doesn't impose this restriction, it appears that our
behavior matches that of VCS.  For instance, when we submit the following to
VCS J-2014.12-SP3-1:</p>

@({
    module foo1 ;
      int arr [3:0];
      parameter place = 0;
      assign arr = '{place: 3, default: 0 };
    endmodule
})

<p>we find that it reports the following error:</p>

@({
    Error-[IAP] Illegal assignment pattern
    test.sv, 5
    foo1, \"place:3\"
      Assignment pattern is illegal due to: Assignment Pattern with named fields
      cannot be assigned to a non-structure target
})

<h3>Implementation notes, disambiguation strategy</h3>

<p>Upon parsing a @(see vl-patternkey) there are four possibilities:</p>

<ol>
<li>It is the @('default') keyword, which is no problem.</li>
<li>It is unambiguously an index expression, e.g., @('3 + 5').</li>
<li>It is unambiguously a built-in type expression, e.g., @('integer').</li>
<li>It is ambiguously a simple name like @('foo'), which might be a structure
member, type name, or parameter name.</li>
</ol>

<p>To reduce insanity we are going to assume that any such @('foo') must not
be a parameter.</p>

<p>At parse time, after dealing with @('default'), we try to parse an
expression and then (to account for core type names like @('integer') which
aren't expressions) fall back to trying to parse a type.  If we get anything
other than a simple name then it's already unambiguous.</p>

<p>On the other hand, if we get an expression which is a simple name, then we
will <b>immediately convert it to a structmem</b> instead of an <b>expr</b>
@(see vl-patternkey).  Note that we don't yet know whether it's a structure
name or a type name; structmems will need to be further disambiguated before
we're sure they aren't types.</p>

<p>During shadowcheck, we have enough information to tell whether a structmem
is actually a type.  We can then check for tricky shadowing as per usual.  Type
disambiguation can then make the final conversion of structmems to types as
necessary.</p>

<p>Later on, in svex conversion: if we encounter a struct pattern, we should
probably also explicitly check that any type keys such as @('foo_t') are NOT
also the names of structure members.  If so, there might be confusion about
what we are assigning to.  We might want this to be smart enough to handle
things like @('struct mystruct { foo foo; bar bar; }'), or maybe those aren't
handled by other Verilog tools anyway.</p>")
