; SATLINK - Link from ACL2 to SAT Solvers
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; config.lisp -- SAT solver configuration objects

(in-package "SATLINK")
(include-book "std/util/defaggregate" :dir :system)

(defaggregate config
  :parents (satlink)
  :short "Settings for which SAT solver to run, how to invoke it, what output
to print, etc."
  :long "<p>A @('config-p') object controls how routines like @(see sat) will
invoke the SAT solver.</p>"
  :tag :satlink-config

  ((cmdline "Command line to use to invoke the SAT solver, except for the
             filename.  For instance, @('\"lingeling\"') or
             @('\"glucose-cert\"'); see @(see sat-solver-options)."
             stringp :rule-classes :type-prescription)

   (verbose "Should we print excessive output for debugging?"
            booleanp :rule-classes :type-prescription)

   (timing  "Should we print stylized timing messages from the solver?  E.g.,
             \"c Sat solving took 103 seconds.\"
             The verbose setting overrides this."
            booleanp :rule-classes :type-prescription
            :default t)

   (mintime "Minimum amount of time that is worth reporting for the overall run.
              This gets passed to @(see time$) as we do, e.g., our export to DIMACS
             and invoke the SAT solver.")

   (remove-temps "Should temporary files (e.g., DIMACS files) be removed after
                  we're done calling SAT?  Usually you will want to remove
                  them, but occasionally they may be useful for debugging, or
                  for comparing SAT solvers' performance.  Note that these
                  files are created with @(see oslib::tempfile), see its
                  documentation for details about their paths and filenames."
                  booleanp :rule-classes :type-prescription)

   (lrat-check  "Should we check an LRAT proof output by the solver? When this
                 is set, SATLINK will use the Heule/Hunt/Kaufmann checker from
                 projects/sat/lrat/stobj-based to check an LRAT proof which should
                 be output to file [input filename].lrat."
                booleanp :rule-classes :type-prescription)))

(defsection *default-config*
  :parents (config-p)
  :short "Default SAT solver configuration for routines like @(see sat)."
  :long "<p>See @(see config-p) to understand these settings.</p>
@(def *default-config*)"

  (defconst *default-config*
    (make-config :cmdline "glucose -model"
                 :verbose t
                 :mintime 1/2
                 :remove-temps t)))

