; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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
;
; doc.lisp -- this is a home for high level documentation topics; keeping
; this basically separated from the VL source code is just a way to let me
; edit these topics without having to rebuild stuff as often.

(in-package "VL2014")
(include-book "xdoc/top" :dir :system)

(defxdoc vl2014
  :parents (hardware-verification)
  :short "The VL Verilog Toolkit, 2014 Edition.  This is a \"stable\" fork of
@(see vl::vl) for compatibility with @(see acl2::esim)."

  :long "<h3>What are VL and VL2014?</h3>

<p>The @(see vl::vl) Verilog Toolkit is a large ACL2 library for working with
<a href='http://en.wikipedia.org/wiki/Verilog'>Verilog</a> and <a
href='http://en.wikipedia.org/wiki/SystemVerilog'>SystemVerilog</a> source
code, developed at Centaur Technology by Jared Davis and Sol Swords.</p>

<p>The <u>2014 Edition</u> of VL is a \"stable\" fork of VL that is meant to
provide continuing support for older tools, notably including @(see
acl2::esim), and also including other internal Centaur tools that are based on
earlier versions of VL.</p>

<p>The 2014 Edition is <b>not</b> under active development.  You should
probably not use it for new projects, and it may be best to work toward
eventually transitioning older tools away from it, in favor of the \"main\"
version of @(see vl::vl).</p>

<p>Note that you can tell which version of VL you are using as follows.</p>

<ul>
<li>Main Edition: @('centaur/vl') directory, @('vl') package.</li>
<li>2014 Edition: @('centaur/vl2014') directory, @('vl2014') package.</li>
</ul>

<p>Since each version uses its own package, it is possible to load both
versions into the same ACL2 project simultaneously.  This may be of use when
transitioning code from the 2014 Edition to the main edition.</p>


<h3>Why is there a 2014 Edition?</h3>

<p>VL has a long history.  Its development started in 2008.  At that time, our
goal was only to implement support for Verilog-2005.  Over the next several
years, we used VL to implement many tools, many of which were based around
@(see acl2::esim).  ESIM is a purely bit-level backend.</p>

<p>In 2014, we began extending VL with features from SystemVerilog and also
began work on a new, vector-level backend, @(see acl2::sv).  Throughout 2014,
and into the start of 2015, we made substantial changes to VL and transitioned
our internal projects to SV.</p>

<p>Much of this work was compatible with ESIM and expanded what the VL/ESIM
flow could handle.  For instance: during this time, the ESIM flow gained better
support for ANSI-style ports, SystemVerilog style global parameters, basic
SystemVerilog idioms like @('always_comb') and @('logic') data types, and so
on.  Other certain SystemVerilog features (structs, arrays, etc.) would have
been difficult to support in ESIM, so we only added them to the VL/SV flow.</p>

<p>In February 2015, we began working on a substantial change to VL's
expression representation.  It became apparent that supporting ESIM through
this change would require updating a large body of code.  This would be a major
cost to maintain code that we were no longer using.</p>

<p>In light of this, we decided that it was time to end support for the ESIM
flow in VL, but we did not want to abandon ESIM altogether.  As a compromise,
we decided to create a stable fork of VL, based on the last version of VL that
works with ESIM.  This fork would allow older tools and proofs to continue to
function, while giving us the freedom to move more quickly on the new versions
of VL without having to continually update the ESIM flow.</p>")


(defxdoc getting-started
  :parents (vl2014)
  :short "Getting started with VL2014."

  :long "<h3>Introduction</h3>

<p><b>VL2014</b> (hereafter VL) is an @(see acl2::acl2) library for working
with <a href='http://en.wikipedia.org/wiki/Verilog'>Verilog</a> and <a
href='http://en.wikipedia.org/wiki/SystemVerilog'>SystemVerilog</a> source
code.  It includes:</p>

<ul>
 <li>An internal representation for Verilog @(see syntax),</li>
 <li>A @(see loader) for parsing Verilog source code into this representation,</li>
 <li>Utilities for inspecting and analyzing parsed designs,</li>
 <li>Various @(see transforms) that can simplify these designs, and</li>
 <li>Pretty-printing and other report-generation functions.</li>
</ul>

<p>Much of VL is general purpose Verilog processing code that is independent of
particular analysis or back-end tool.  This approach has allowed us to use VL
to implement a family of Verilog-related tools.  Here are some examples:</p>

<ul>

<li>VL can build @(see esim) models of Verilog modules for formal verification
with ACL2.  This is the basis for much of Centaur's formal verification
efforts.</li>

<li>The VL @(see kit) is a standalone command-line executable that you can
build on top of ACL2 and VL.  It includes commands for @(see lint)ing Verilog
designs, converting Verilog modules into a JSON format, and other
commands.</li>

<li>VL has been used to build a web-based \"module browser\" that lets you see
the source code for our modules with, e.g., hyperlinks for navigating between
wires and following wires.  This is now integrated into the VL @(see kit);
@(see server).</li>

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

<p>We imagine that other users of VL may wish to reuse its parsing and
transformations to easily implement other tools.</p>

<h3>Starting Points</h3>

<p>If you want to use VL to do formal verification of hardware, you might start
with the @(see acl2::esim-tutorial), which is a hands-on guide that will take
you through using VL and @(see esim) to verify some simple circuits.</p>

<p>The first step in using VL in any other capacity on a real project is
probably to try to get it to parse your design; see the documentation for the
@(see loader).  You may want to read the notes about @(see
supported-constructs).</p>

<p>Once you have parsed your design (or at least some portion of it) you will
have a list of modules.  You might want to at least glance through the
documentation for @(see syntax), which explains how modules are represented.
This may be particularly useful if you are going to write your own analysis
tools.</p>

<p>You may find it useful to pretty-print modules, see for instance @(see
vl-ppcs-module) and perhaps more generally the VL @(see printer).</p>

<p>After getting a feel for how modules are represented, it would be good to
look at the available @(see transforms).  For instance, you might look at the
code for @(see vl-simplify) to see the transforms used in the @(see esim) flow.
You could also look at @('run-vl-lint-main') which uses a different
transformation sequence for toward linting.</p>

<p>If you are going to write any Verilog-processing tools of your own, you
should probably read through how VL deals with @(see warnings) and then take a
look at @(see mlib), which provides many functions for working with expressions
and ranges, finding modules and module items, working with the module
hierarchy, generating fresh names, and working with modules at the bit
level.</p>")

(defsection supported-constructs
  :parents (getting-started)
  :short "Notes about the subset of Verilog and SystemVerilog that @(see
  VL2014) supports."

  :long "<p>VL was originally based on our reading of the <a
href='http://standards.ieee.org/findstds/standard/1364-2005.html'>Verilog-2005
standard, IEEE Std 1364-2005</a>.  When page and section numbers are used
throughout the VL documentation, they are often in reference to this document.
VL now also supports some fragment of SystemVerilog, based on our reading of
the <a
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

<li>The @(see lint)er flow can cope with richer SystemVerilog designs.  It is
not especially bothered by transistor-level constructs.  It cannot handle some
simulation constructs, but is able to ignore many constructs when it does not
truly understand them.</li>

</ul>

<p>Regardless of the particular flow you are using, all VL tools reuse the same
loader and internal representation.  The loader can read files as either
Verilog-2005 or SystemVerilog-2012.  Regardless of the input type, we arrive at
the same internal representation (essentially SystemVerilog).</p>

<p>VL's @(see preprocessor) is somewhat incomplete.  It basically just supports
@('`define') and @('`ifdef')-related stuff.  It can @('`include') files in the
style of the @('+incdir') options for tools like Verilog-XL, NCVerilog, and
VCS.  VL also supports a notion of search paths, which are similar to
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
  :parents (vl2014)
  :short "Generic utilities that are unrelated to Verilog processing, but which
are provided by the VL books.")

(defxdoc transforms
  :parents (vl2014)
  :short "High-level transformations for rewriting and simplifying Verilog
modules.")

(defxdoc mlib
  :parents (vl2014)
  :short "<b>M</b>odule <b>Lib</b>rary -- A collection of various functions for
working with Verilog modules.")


(defxdoc warnings
  :parents (vl2014)
  :short "Support for handling warnings and errors."

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

<li>Our @(see lint) checks might notice \"code smells\" where even though the
input Verilog is semantically well-formed, it is somehow strange and looks like
it could be an error.  For instance, perhaps there are multiple assignments to
the same wire, or expressions like @('a & b') where @('a') and @('b') have
different sizes.</li>

</ul>

<p>Handling these many kinds of cases is tricky.  In the early days of VL, our
approach to warnings and errors was quite ad-hoc.  We sometimes printed warning
messages to standard output using the @(see cw) function.  For more serious
conditions, we sometimes caused errors using @(see er).  This approach had a
number of problems.  In particular,</p>

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
vl-warning-p) objects.</p>

<p>These objects are in many ways similar to the <a
href='https://en.wikipedia.org/wiki/Exception_handling'>Exception</a> objects
found in other programming languages.  Each warning has a <b>type</b> and a
<b>message</b> that describes the error.  These messages can conveniently make
use of VL's @(see printer), so you can directly pretty-print arbitrary Verilog
constructs when writing warning messages.</p>

<p>We use @('vl-warning-p') objects universally, for all kinds of warnings and
errors.  That is, everything from the most minor of code smells (@('wire foo')
is never used for anything), to the most severe problems (the module you're
instantiating isn't defined) results in a warning.  Since it is useful to
distinguish minor commentary from severe problems, our warning objects include
a <b>fatalp</b> field.</p>

<p>As a general philosophy or strategy for using these warning objects:</p>

<ul>

<li>Warnings messages should never be printed to standard output.  Instead, we
should create a @(see vl-warning-p) object that gives the context, and explains
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
fatal warnings&mdash;an important operation for @(see vl-simplify).  As another
example, we can create reports, e.g., about all of the warnings for some
particular module, or all the warnings of some particular type throughout all
of the modules, etc.  These capability is used in tools like @(see
vl-lint).</p>

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
