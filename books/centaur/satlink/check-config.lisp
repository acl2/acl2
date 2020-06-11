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

(in-package "SATLINK")
(include-book "top")
(include-book "system/hl-addr-combine" :dir :system)
(local (include-book "cnf-basics"))

(local (defthm lit-list-listp-of-append
         (implies (and (lit-list-listp a)
                       (lit-list-listp b))
                  (lit-list-listp (append a b)))))


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


; For a more thorough than hand test, we will generate pigeonhole problems.

(define bird-in-hole ((bird natp)
                      (hole   natp))
  :parents (pigeon-hole)
  :returns (lit litp "This bird is in this hole.")
  :guard-hints (("goal" :in-theory (enable varp)))
  (b* ((var (lnfix (acl2::hl-nat-combine bird hole))))
    (make-lit var 0)))

(define bird-in-some-hole ((bird natp "Fixed")
                           (hole natp "Counts down from max hole."))
  :parents (pigeon-hole)
  :returns (clause lit-listp "This bird is in some hole.")
  (b* (((when (zp hole))
        nil)
       (hole (- hole 1)))
    (cons (bird-in-hole bird hole)
          (bird-in-some-hole bird hole))))

(define every-bird-in-hole ((bird     natp "Counts down from max bird")
                            (max-hole natp "Fixed"))
  :parents (pigeon-hole)
  :returns (clauses lit-list-listp "Every bird is in some hole.")
  (b* (((when (zp bird))
        nil)
       (bird (- bird 1)))
    (cons (bird-in-some-hole bird max-hole)
          (every-bird-in-hole bird max-hole))))


(define not-both-in-hole ((bird1 natp)
                          (bird2 natp)
                          (hole  natp))
  :parents (pigeon-hole)
  :returns (clause lit-listp "These two birds do not share this hole.")
  (list (lit-negate (bird-in-hole bird1 hole))
        (lit-negate (bird-in-hole bird2 hole))))

(define no-others-in-hole ((tweety natp "Fixed")
                           (birds  natp "Counts down from max birds.")
                           (hole   natp "Fixed"))
  :parents (pigeon-hole)
  :returns (clauses lit-list-listp "No other bird shares hole with tweety.")
  (b* (((when (zp birds))
        nil)
       (birds (- birds 1))
       ((when (eql tweety birds))
        (no-others-in-hole tweety birds hole)))
    (cons (not-both-in-hole tweety birds hole)
          (no-others-in-hole tweety birds hole))))

(define no-two-in-hole-aux ((tweety    natp "Counts down from max birds.")
                            (max-birds natp "Fixed")
                            (hole      natp "Fixed"))
  :parents (pigeon-hole)
  :returns (clauses lit-list-listp "No two birds share this one hole.")
  (b* (((when (zp tweety))
        nil)
       (tweety (- tweety 1)))
    (append (no-others-in-hole tweety max-birds hole)
            (no-two-in-hole-aux tweety max-birds hole))))

(define no-two-in-hole ((max-birds natp "Fixed")
                        (hole      natp "Fixed"))
  :parents (pigeon-hole)
  :returns (clauses lit-list-listp "No two birds share this hole.")
  (no-two-in-hole-aux max-birds max-birds hole))

(define no-two-in-any-hole ((max-birds natp "Fixed")
                            (hole      natp "Counts down from max hole"))
  :parents (pigeon-hole)
  :returns (clauses lit-list-listp "No two birds share any hole.")
  (b* (((when (zp hole))
        nil)
       (hole (- hole 1)))
    (append (no-two-in-hole max-birds hole)
            (no-two-in-any-hole max-birds hole))))

(define pigeon-hole ((num-birds natp)
                     (num-holes natp))
  :parents (check-config)
  :returns (clauses lit-list-listp)
  (append (every-bird-in-hole num-birds num-holes)
          (no-two-in-any-hole num-birds num-holes)))


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


     ;; I decided to add something a little harder because the above didn't
     ;; seem sufficient to exercise unsat proof checking mechanisms.

     (cw "*** Some basic pigeon-hole problems ***~%")

     (assert-unsat (pigeon-hole 3 1)) ;; 3 pigeons don't fit in 1 hole
     (assert-unsat (pigeon-hole 3 2)) ;; They don't fit into 2 holes
     (assert-sat   (pigeon-hole 3 3)) ;; They do fit in 3 holes
     (assert-sat   (pigeon-hole 3 4)) ;; They do fit in 4 holes

     (assert-unsat (pigeon-hole 4 1)) ;; 4 pigeons don't fit in 1 hole
     (assert-unsat (pigeon-hole 4 2)) ;; They don't fit into 2 holes
     (assert-unsat (pigeon-hole 4 3)) ;; They don't fit into 3 holes
     (assert-sat   (pigeon-hole 4 4)) ;; They do fit in 4 holes
     (assert-sat   (pigeon-hole 4 5)) ;; They do fit in 4 holes

     (assert-unsat (pigeon-hole 7 6)) ;; 7 pigeons don't fit in 6 holes
     (assert-sat   (pigeon-hole 7 7)) ;; They do fit into 7 holes

     (cw "*** Good deal -- this SATLINK configuration seems OK. ***~%")
     )))




#||

; I no longer do this here, because
;   (1) it lets us keep the documentation for this file in doc/top.lisp
;       without requiring glucose, and
;   (2) we now have the whole solvers/ directory, with scripts for many
;       SAT solvers, and we probably want to check all of them.

(value-triple
 (check-config
  (make-config :cmdline "glucose -model"
               :verbose t
               :mintime nil
               :remove-temps t)))

||#
