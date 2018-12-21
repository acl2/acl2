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
(include-book "util/defs")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)

(defprod vl-simpconfig
  :parents (vl-design->sv-design)
  :short "Options for how to simplify Verilog modules."
  :tag :vl-simpconfig

  ((compress-p
    booleanp
    "Hons the modules at various points.  This takes some time, but can produce
     smaller translation files."
    :rule-classes :type-prescription)

   (problem-mods
    string-listp
    "Names of modules that should thrown out, perhaps because they cause some kind
     of problems."
    :default nil)

   (already-annotated
    booleanp
    "Denotes that we've already annotated the design and shouldn't do it
     again.")

   (unroll-limit
    natp
    "Maximum number of iterations to unroll for loops, etc., when rewriting statements.
      This is just a safety valve."
    :rule-classes :type-prescription
    :default 1000)

   (sc-limit
    natp
    "Recursion limit for compiling statements, e.g., unrolling loops and
     figuring out when they terminate.  You might hit this if loops have
     non-trivial finishing conditions.  Small limits may be preferable for
     applications like linting where you don't want a single troublesome loop
     to waste inordinate amounts of time.  Larger limits may be needed if
     you're trying to model a design that has long-running loops."
    :rule-classes :type-prescription
    :default 1000)

   (elab-limit
    natp
    "Recursion limit for elaboration.  This usually shouldn't matter or need tinkering.
     It's a safety valve against possible loops in elaboration, e.g., to
     resolve parameter P you need to evaluate parameter Q, which might require
     you to resolve R, which might depend hierarchically on P, and so on. So if
     you hit this there's probably something wrong with your design."
    :rule-classes :type-prescription
    :default 10000)

   (uniquecase-conservative
    natp :default 0
    "For @('unique case') and @('unique0 case') statements, a synthesis tool is
     allowed to assume that the cases are mutually exclusive and simplify the logic
     accordingly. For @('unique') they can assume that exactly one of the tests
     will be true.  This configuration flag is a natural number that sets the degree
     of conservativity, as follows: When 0 (the default), the logic we generate
     emulates a simulator, which always executes the first matching case.  When
     1, if uniqueness is violated, then we pretend that all tests that were 1 instead
     evaluated to X, or if all tests were 0 then we pretend all instead evaluated
     to X.  When 2 or greater, when the condition is violated we pretend all tests
     evaluated to X.  When 3 or greater, we additionally pretend that all assignments
     within the case statement write X instead of the given value.  The intention
     behind this is to make it likely that our logic is conservative with respect
     to anything a synthesis tool might produce.")

   (uniquecase-constraints
    booleanp
    "Generate constraints for @('unique case') and @('unique0 case') statements.
      Likely you do not want both this and @('uniquecase-conservative') to be set,
     because they are two different approaches for dealing with a synthesis tool's
     flexibility in dealing with unique and unique0 case statements.  When this
     is set, we separately store a constraint saying that the cases are one-hot
     or one/zero-hot, respectively.  This constraint is stored in the SV modules
     when they are generated by @(see vl-design->sv-design).")

   (enum-constraints
    "Generate constraints for variables of @('enum') datatypes, or compound datatypes
     that have @('enum') subfields. These constraints are saved in the SV modules
     when they are generated by @(see vl-design->sv-design).  Each constraint
     says that an enum field's value is one of the proper values of an enum type.
      If NIL (the default), these constraints are not generated. If T or any nonnil
     object other than the keyword :ALL, then the constraints are generated except
     for port variables. If :ALL, then these are generated for ports as well.")

   (enum-fixups
    "Generate fixups for variables of @('enum') datatypes, or compound datatypes
     that have @('enum') subfields. These cause svex compilation to fix up enum
     values to be X if not one of the allowed values. If NIL (the default), this
     fixing will not be done.  Similar to the @('enum-constraints') option, fixups
     are only done for non-port variables unless this option is set to the keyword
     :ALL.")

   (sv-simplify
    booleanp :default t
    "Apply svex rewriting to the results of compiling procedural blocks.")

   (sv-simplify-verbosep
    booleanp
    "Verbosely report svex rewriting statistics.")

   (sv-include-atts
    string-listp
    "Translate SystemVerilog attributes on variable declarations into sv modules.")

   (nb-latch-delay-hack
    booleanp
    "Artificially add a delay to nonblocking assignments in latch-like contexts.")

   (name-without-default-params 
    booleanp
    "Omit non-overridden parameters from module names generated by unparameterization.")

   (unparam-bad-instance-fatalp
    booleanp :default t
    "Make a fatal warning when a nonexistent parameter is overridden by a module instance.")

   (defer-argresolve
     booleanp :default nil
     "Don't run the argresolve transform before elaborate; instead, do it once
      the parameters for the given module are resolved.  This may avoid errors
      when a module conditionally instantiates another module that hasn't been
      found, but the condition under which it instantiates that module is never
      satisfied.")

   (suppress-fatal-warning-types
    symbol-listp :default nil
    "Treat the listed warnings as non-fatal during vl-design-propagate-errors.
     Such warnings will still show up as fatal, but the modules in which they exist
     will not be labeled \"bad\".")))

(defconst *vl-default-simpconfig*
  (make-vl-simpconfig))

