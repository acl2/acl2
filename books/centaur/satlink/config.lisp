; SATLINK - Link from ACL2 to SAT Solvers
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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>

; config.lisp -- SAT solver configuration objects

(in-package "SATLINK")
(include-book "cutil/defaggregate" :dir :system)

(defaggregate config
  :parents (satlink)
  :short "Settings for which SAT solver to run, how to invoke it, what output
to print, etc."
  :long "<p>A @('config-p') object controls how routines like @(see sat) will
invoke the SAT solver.</p>"
  :tag :satlink-config

  ((cmdline "Command line to use to invoke the SAT solver, except for the
             filename.  For instance, @('\"lingeling\")."
            stringp :rule-classes :type-prescription)

   (verbose "Should we print excessive output for debugging?"
            booleanp :rule-classes :type-prescription)

   (mintime "Minimum amount of time that is worth reporting.  This gets passed
             to @(see time$) as we do, e.g., our export to DIMACS and invoke
             the SAT solver.")

   (remove-temps "Should temporary files (e.g., DIMACS files) be removed after
                  we're done calling SAT?  Usually you will want to remove
                  them, but occasionally they may be useful for debugging, or
                  for comparing SAT solvers' performance."
                  booleanp :rule-classes :type-prescription)))

(defsection *default-config*
  :parents (config-p)
  :short "Default SAT solver configuration for routines like @(see sat)."
  :long "<p>See @(see config-p) to understand these settings.</p>
@(def *default-config*)"

  (defconst *default-config*
    (make-config :cmdline "lingeling"
                 :verbose t
                 :mintime 1/2
                 :remove-temps t)))
