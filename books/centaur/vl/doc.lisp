; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
;
; doc.lisp -- this is a home for high level documentation topics; keeping
; this basically separated from the VL source code is just a way to let me
; edit these topics without having to rebuild stuff as often.

(in-package "VL")
(include-book "xdoc/top" :dir :system)

(defxdoc vl
  :parents (hardware-verification)
  :short "The VL Verilog Toolkit is a large ACL2 library for working with <a
href='http://en.wikipedia.org/wiki/Verilog'>Verilog</a> source code, developed
by <a href='http://www.centtech.com/'>Centaur Technology</a>.  It includes a
Verilog loader and many functions for inspecting and transforming modules, and
serves as a frontend for many Verilog tools."

  :long "<box><p><b>Note</b>: this documentation is mainly a reference manual.
If you are new to VL, please see @(see getting-started) first.</p></box>")


(defxdoc getting-started
  :parents (vl)
  :short "Getting started with VL."

  :long "<h3>Introduction</h3>

<p><b>VL</b> is an @(see acl2::acl2) library for working with <a
href='http://en.wikipedia.org/wiki/Verilog'>Verilog</a> source code.  It
includes:</p>

<ul>
 <li>An internal representation for Verilog @(see syntax),</li>
 <li>A @(see loader) for parsing Verilog source code into this representation,</li>
 <li>Utilities for inspecting and analyzing these modules,</li>
 <li>Various @(see transforms) that can simplify these modules, and</li>
 <li>Pretty-printing and other report-generation functions.</li>
</ul>

<p>Much of VL is general purpose Verilog processing code that is geared toward
simplifying designs independently of any particular analysis or back-end tool.
This approach has allowed us to use VL to implement many Verilog-related tools.
For instance:</p>

<ul>

<li>VL can translate Verilog into E modules (see @(see acl2::esim)) for formal
verification.  This is the basis for a good part of Centaur's formal
verification efforts.  Our overall approach to E translation is to apply
several Verilog-to-Verilog source-code @(see transforms).  Together, these
transforms work to simplify the input Verilog into a form that is very close to
E, where modules consist only of @(see primitives) and submodules.  The final
conversion into E is quite straightforward.</li>

<li>The publicly available VL @(see kit) is a command-line executable built on
top of ACL2 and VL, which includes commands for @(see lint)ing Verilog designs,
converting Verilog modules into a JSON format, and other commands.</li>

<li>We have implemented an equivalence checking tool (which is not yet
released) that has a tick-based timing model and handles transistor-level
constructs.  This tool uses the same parser and most of VL's transforms, but
also has a couple of additional transformation steps.</li>

<li>We have used it to implement a web-based \"module browser\" (which will
probably not be released since it is very Centaur specific) that lets users see
the original and translated source code for our modules, and has several nice
features (e.g., hyperlinks for navigating between wires and following wires,
and integrated linting and warning/error reporting).</li>

<li>We have used it to implement <i>VL-Mangle</i>, a web-based refactoring
tool (which will probably not be released because it is hard to distribute).
To support this tool we also developed the @(see acl2::bridge).  A paper
describing this tool can be found in: Jared Davis. <a
href='http://www.cs.utexas.edu/users/jared/publications/2013-doform-embedding/embedding.pdf'>Embedding
ACL Models in End-User Applications</a>.  In <a
href='http://www.cs.bham.ac.uk/research/projects/formare/events/aisb2013/'>Do-Form
2013</a>.  April, 2013, Exeter, UK.</li>

</ul>

<p>We imagine that other users of VL may wish to use it:</p>

<ul>

<li>As a convenient way to load Verilog files to implement their own static
checks (i.e., as Lisp functions that inspect the parse tree), or</li>

<li>As a frontend to some other kind of tool, e.g., use VL to deal with tricky
Verilog things like expressions so that your tool only has to deal with gates
and hierarchical modules.  (This is really how we use it.)</li>

</ul>


<h3>Supported Constructs</h3>

<p>Verilog is a huge language, and VL supports only part of it.</p>

<p>VL was originally based on our reading of the <a
href='http://standards.ieee.org/findstds/standard/1364-2005.html'>Verilog-2005
standard, IEEE Std 1364-2005</a>.  Page and section numbers given throughout
the VL documentation are in reference to this document.</p>

<p>We are working to extend VL to support some fragment of SystemVerilog.  We
are basing this work on our interpretation of the <a
href='http://standards.ieee.org/findstds/standard/1800-2012.html'>IEEE
1800-2012</a>.  This is early work in progress, and you should not yet expect
VL to support SystemVerilog in any reasonable way.</p>

<p>With respect to the Verilog-2005 standard:</p>

<p>VL's @(see preprocessor) is somewhat incomplete.  It basically just supports
@('`define') and @('`ifdef')-related stuff and can @('`include') files in the
style of the @('+incdir') options for tools like Verilog-XL (but we often use
search paths, which are more similar to @('+libdir') arguments.)</p>

<p>The @(see lexer) is complete.</p>

<p>The @(see parser) doesn't currently support user-defined primitives,
generate statements, specify blocks, specparams, and genvars.  The parser will
just skip over some of these constructs.  Depending on what you are doing, this
behavior may be actually appropriate (e.g., skipping specify blocks may be okay
if you aren't trying to deal with low-level timing issues.)</p>

<p>Each of VL's @(see transforms) have certain capabilities and limitations,
which vary from transform to transform.  As a general rule, VL mainly supports
RTL-level constructs and some of its transforms will not be able to cope
with:</p>

<ul>

<li>transistor-level things like @('tran') gates and @('inout') ports, or</li>

<li>simulation-level things like hierarchical identifiers and @('always')
statements beyond the simplest latches and flops.</li>

</ul>

<p>VL has some ability to tolerate constructs that aren't really supported, and
the general philsophy is that an error in some particular module shouldn't
affect other modules.  If the parser runs into an syntax error or an
unsupported construct, it often only causes that particular module to be
skipped.  When transforms encounter unsupported things or run into problems, we
usually avoid hard errors and instead just add \"fatal @(see warnings)\" to the
module with the problem.</p>



<h3>Starting Points</h3>

<p>The first step in using VL for anything is probably to try to get it to
parse your design; see the documentation for the @(see loader).</p>

<p>Once you have parsed your design (or at least some portion of it) you will
have a list of modules.  You might want to at least glance through the
documentation for @(see syntax), which explains how modules are represented.
This may be particularly useful if you are going to write your own checkers or
transforms.</p>

<p>You may find it useful to pretty-print modules, see for instance @(see
vl-ppcs-module) and perhaps more generally the VL @(see printer).</p>

<p>After getting a feel for how modules are represented, it would be good to
look at the available @(see transforms).  A good way to do this might be to
look at the code for @(see vl-simplify) (see @('centaur/vl/top.lisp')) to see
the order that we normally apply the transforms in.  You could also look at
@('centaur/vl/lint/lint.lisp') which uses a different transformation sequence
that is more geared toward linting.  You should probably also read through how
VL deals with @(see warnings).</p>

<p>If you are going to write any transforms or checkers of your own, you should
probably look at @(see mlib).  This provides many functions for working with
expressions and ranges, finding modules and module items, working with the
module hierarchy, generating fresh names, and working with modules at the bit
level.</p>")


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


(defxdoc checkers
  :parents (vl)
  :short "Light-weight static checks in the spirit of \"lint\" or \"code
smells.\""

  :long "<p>We have implemented a few static checks tools to identify potential
errors in modules.  Most of these checks are relatively simple heuristics: when
they generate warnings, it does not necessarily mean that anything is actually
wrong.  Instead, these tools are mainly intended to point out unusual things
that a human might wish to investigate.</p>")


(defxdoc warnings
  :parents (vl)
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

<li>Our @(see checkers) might notice \"code smells\" where even though the
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

