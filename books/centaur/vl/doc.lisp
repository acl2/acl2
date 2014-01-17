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
 <li>A representation for Verilog @(see modules),</li>
 <li>A @(see loader) for parsing Verilog source code into this representation,</li>
 <li>Utilities for inspecting and analyzing these modules,</li>
 <li>Various @(see transforms) that can simplify these modules, and</li>
 <li>Pretty-printing and other report-generation functions.</li>
</ul>

<p>The original (and still primary) purpose of VL is to translate Verilog
modules into E-language modules for formal verification.  E is a comparatively
simple, hierarchical, register-transfer level hardware description language;
see @(see esim).  An early version of E is described in:</p>

<p>Warren A. Hunt, Jr. and Sol Swords.  <a
href='http://dx.doi.org/10.1007/978-3-642-02658-4_28'>Centaur technology media
unit verification.  Case study: Floating point addition.</a> in Computer Aided
Verification (CAV '09), June 2009.</p>

<p>Our overall approach to E translation is to apply several Verilog-to-Verilog
source-code @(see transforms).  Together, these transforms work to simplify the
input Verilog into a form that is very close to E, where modules consist only
of gates and submodules.  Then, the final conversion into E is quite
straightforward.</p>

<p>A feature of this approach is that the majority of VL has nothing to do with
E, and VL can be used to implement other Verilog tools.  For instance:</p>

<ul>

<li>The publicly available VL @(see kit) is a command-line executable built on
top of ACL2 and VL, which includes commands for @(see lint)ing Verilog designs,
converting Verilog modules into a JSON format, and other commands.</li>

<li>We have implemented an equivalence checking tool (which is not yet
released) that has a tick-based timing model and handles transistor-level
constructs.  This tool uses the same parser and most of VL's transforms, but
also has a couple of additional transformation steps.</li>

<li>We have used it to implement a web-based \"module browser\" (which
will probably not be released since it is very Centaur specific) that lets
users see the original and translated source code for our modules, and has
several nice features (e.g., hyperlinks for navigating between wires and
following wires, and integrated linting and warning/error reporting).</li>

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
documentation for @(see modules), which explains how modules are represented.
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
