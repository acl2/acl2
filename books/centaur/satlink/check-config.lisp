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

(in-package "SATLINK")
(include-book "top")

(define simple-sat ((formula lit-list-listp) &key (config config-p))
  :parents (check-config)
  "Just returns STATUS, not env."
  (progn$
   (tshell-ensure)
   (with-local-stobj env$
     (mv-let (status env$)
       (sat formula env$ :config config)
       status))))

(define assert-sat ((formula lit-list-listp) &key ((config config-p) 'config))
  :parents (check-config)
  (or (equal (simple-sat formula :config config) :sat)
      (raise "Expected formula ~x0 to be satisfiable!" formula)))

(define assert-unsat ((formula lit-list-listp) &key ((config config-p) 'config))
  :parents (check-config)
  (or (equal (simple-sat formula :config config) :unsat)
      (raise "Expected formula ~x0 to be unsatisfiable!" formula)))

(define check-config ((config config-p))
  :returns nil
  :parents (sat-solver-options)
  :short "Run some quick checks of your SAT solver configuration."

  :long "<p>This is a quick check to try to ensure that ACL2 can communicate
with your SAT solver correctly.  If it notices any problems, it will just cause
a @(see hard-error).  A basic way to use it would be, e.g.,:</p>

@({
    (include-book \"centaur/satlink/check-config\" :dir :system)
    (defconst *my-config* (satlink::make-config ...))
    (value-triple (satlink::check-config *my-config*))
})

<p>It's a good idea to run this check when you install a new SAT solver, to
ensure that your paths, command-line options, etc., are being handled
correctly.  It should catch basic problems such as:</p>

<ul>
 <li>Your solver isn't in your PATH</li>
 <li>Your solver is crashing because it wants some other @('libc')</li>
 <li>Your solver doesn't like some option you're passing to it</li>
 <li>Your solver doesn't understand what file to process</li>
 <li>Your solver isn't printing counterexamples</li>
 <li>Your solver isn't producing DIMACS formatted output</li>
</ul>

<p>This is <b>not</b> any kind of comprehensive stress test of the SAT solver
itself.  We just run @(see sat) on a few small formulas to see if your solver
is producing the expected results.</p>"

  (b* ((la      (make-lit 0   0)) ;; a few literals, "literal a, literal b, ..."
       (~la     (make-lit 0   1))
       (lb      (make-lit 1   0))
       (~lb     (make-lit 1   1))
       (lc      (make-lit 2   0))
       (~lc     (make-lit 2   1))
       (ld      (make-lit 100 0))
       (~ld     (make-lit 100 1)))
    (progn$
     (cw "*** Checking that the empty list of clauses is SAT. ***~%")
     (assert-sat nil)

     (cw "*** Checking that an empty clause is UNSAT. ***~%")
     (assert-unsat (list nil))

     (cw "*** Checking that some singleton clauses are SAT. ***~%")
     (assert-sat (list (list la)))
     (assert-sat (list (list lb)))
     (assert-sat (list (list lc)))
     (assert-sat (list (list ld)))
     (assert-sat (list (list ~la)))
     (assert-sat (list (list ~lb)))
     (assert-sat (list (list ~lc)))
     (assert-sat (list (list ~ld)))

     (cw "*** Checking that clauses (A) and (!A) are UNSAT. ***~%")
     (assert-unsat (list (list la) (list ~la)))
     (assert-unsat (list (list lb) (list ~lb)))
     (assert-unsat (list (list lc) (list ~lc)))
     (assert-unsat (list (list ld) (list ~ld)))
     (assert-unsat (list (list ~la) (list la)))
     (assert-unsat (list (list ~lb) (list lb)))
     (assert-unsat (list (list ~lc) (list lc)))
     (assert-unsat (list (list ~ld) (list ld)))

     (cw "*** A few more tests ***~%")

     (assert-sat (list (list la ~la)
                       (list lb)
                       (list lc ~lc)
                       (list ld ~ld)))

     (assert-unsat (list (list la ~la)
                         (list lb)
                         (list lc ~la)
                         (list ld ~ld)
                         (list ~lb)))

     (assert-sat (list (list la)
                       (list ~la lb)
                       (list ~lb lc)
                       (list ~lc ld)))

     (assert-unsat (list (list la)
                         (list ~la lb)
                         (list ~lb lc)
                         (list ~lc ld)
                         (list ~ld)))

     (cw "*** Good deal -- this SATLINK configuration seems OK. ***~%")
     )))

(value-triple
 (check-config
  (make-config :cmdline "glucose"
               :verbose t
               :mintime nil
               :remove-temps t)))

