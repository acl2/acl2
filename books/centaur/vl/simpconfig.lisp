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

(defprod vl-simpconfig
  :parents (vl-design->svex-design)
  :short "Options for how to simplify Verilog modules."
  :tag :vl-simpconfig

  ((compress-p   booleanp
                 "Hons the modules at various points.  This takes some time,
                  but can produce smaller translation files."
                 :rule-classes :type-prescription)

   (problem-mods string-listp
                 "Names of modules that should thrown out, perhaps because they
                  cause some kind of problems."
                 :default nil)

   (already-annotated booleanp
                      "Denotes that we've already annotated the design and shouldn't
                       do it again.")

   (unroll-limit natp
                 "Maximum number of iterations to unroll for loops, etc., when
                  rewriting statements.  This is just a safety valve."
                 :rule-classes :type-prescription
                 :default 1000)

   (uniquecase-conservativep booleanp
                             "For @('unique case') and @('unique0 case') statements,
                              a synthesis tool is allowed to assume that the cases
                              are mutually exclusive and simplify the logic accordingly.
                              For @('unique') they can assume that exactly one
                              of the tests will be true.  When this flag is not
                              set, the logic we generate emulates a simulator,
                              which always executes the first matching case.  When
                              it is set, we instead make our logic conservative
                              in the following way: if no test evaluates to true
                              and there is no default, we pretend that all tests
                              evaluated to X, and if more than one test evalutes
                              to true, we pretend that all tests that were true
                              instead are X.  The intention behind this is to make
                              it likely that our logic is conservative with respect
                              to anything a synthesis tool might produce.")

   (uniquecase-constraints booleanp
                           "Generate constraints for @('unique case') and @('unique0
                            case') statements.  Likely you do not want both this
                            and @('uniquecase-conservative') to be set, because
                            they are two different approaches for dealing with
                            a synthesis tool's flexibility in dealing with unique
                            and unique0 case statements.  When this is set, we
                            separately store a constraint saying that the cases
                            are one-hot or one/zero-hot, respectively.  This constraint
                            is stored in the SV modules when they are generated
                            by @(see vl-design->svex-design).")

   (enum-constraints booleanp
                     "Generate constraints for variables of @('enum') datatypes,
                      or compound datatypes that have @('enum') subfields. These
                      constraints are saved in the SV modules when they are generated
                      by @(see vl-design->svex-design).  Each constraint says that
                      an enum field's value is one of the proper values of an enum
                      type.")

   (enum-constraints-no-ports booleanp
                              "Skip generating enum constraints for port variables.")

   (sv-simplify booleanp :default t
                "Apply svex rewriting to the results of compiling procedural blocks.")

   (sv-simplify-verbosep booleanp
                         "Verbosely report svex rewriting statistics.")

   (nb-latch-delay-hack booleanp
                        "Artificially add a delay to nonblocking assignments in latch-like contexts.")

   (name-without-default-params booleanp
                                "Omit non-overridden parameters from module names generated by unparameterization.")))

(defconst *vl-default-simpconfig*
  (make-vl-simpconfig))

