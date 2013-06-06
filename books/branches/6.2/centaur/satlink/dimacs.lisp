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

; dimacs.lisp -- Writer to export CNF formulas into DIMACS files

(in-package "SATLINK")
(include-book "cnf")
(include-book "str/natstr" :dir :system)
(include-book "str/strnatless" :dir :system)
(include-book "std/io/base" :dir :system)

(defsection dimacs
  :parents (satlink)
  :short "DIMACS format is a standard interface to SAT solvers."

  :long "<p>Many SAT solvers accept a common format for input and output that
is used in SAT solving competititons.  The most canoncial description of this
format <b>might</b> be the following:</p>

<p><a
href='ftp://dimacs.rutgers.edu/pub/challenge/satisfiability/doc/satformat.dvi'>satformat.dvi</a>
-- Suggested Satisfiability Format, last revision May 8, 1993.</p>

<p>The basic input format is as follows.  At the top you can have <i>comment
lines</i> that start with a @('c'), like this:</p>

@({
    c This line is a comment.
})

<p>Then comes the <i>problem line</i>, which starts with a @('p') and then says
how many variables and clauses there are.  For instance, here is a problem line
that says this is a CNF problem with 3 variables and 4 clauses:</p>

@({
    p cnf 3 4
})

<p>Finally the clauses are listed.  Each clause is represented as a list of
numbers like @('3') and @('-42').  A positive number like @('3') represents a
positive occurrence of variable 3.  A negative number like @('-42') represents
a negated occurrence of variable 42.</p>

<p>The number @('0') is treated in a special way: it is not a variable, but
instead marks the end of each clause.  This allows a single clause to be split
up over multiple lines.</p>


<h3>Input Format Questions and <i>Clean</i> Formulas</h3>

<p>If we could be sure the above document was the standard, we could very
easily convert from our @(see cnf) representation into it.  The only twist is
that 0 isn't a valid identifier in DIMACS format, but it is a valid identifier
in our representation.  To get around this, we can just add one to every
variable number throughout the problem.</p>

<p>However, the SAT competitions generally use a simplified version of the
DIMACS format.  For instance, the 2012 SAT competititon used the same <a
href='http://www.satcompetition.org/2011/rules.pdf'>rules</a> as the 2011
competititon and for previous years, and restrict the format so that the
solver may assume:</p>

<ul>

<li>Each variable, from 1 to the number of variables specified on the problem
line, is used at least once in some clause.</li>

<li>The clauses are distinct and may not simultaneously contain opposite
literals.</li>

<li>There are exactly the right number of clauses given in the problem
line.</li>

<li>Clauses are kept on the same line.</li>

</ul>

<p>It appears that the rules do not rule out empty clauses.</p>

<p><b>BOZO</b> Eventually, we would like to make sure we produce DIMACS files
that conform to these more stringent requirements, since otherwise a SAT solver
that believes it can make these assumptions may make a mistake.  We may
eventually add a cleaning phase to our SAT integration, to ensure that we only
call the SAT solver on \"clean\" formulas.</p>"

; Basic idea: ACC is a character list with the output we have "printed" in
; reverse order.  This means (cons char acc) is the same as printing a char,
; (str::revappend-chars str acc) is the same as printing str, etc.

  (define dimacs-write-lit ((lit litp) (acc character-listp))
    :returns (acc character-listp :hyp :guard)
    :inline t
    (b* ((negatedp (int= (lit->neg lit) 1))
         ;; Increment all IDs to account for 0 not being a valid DIMACS variable.
         (id+1     (+ 1 (var->index (lit->var lit))))
         (acc      (if negatedp (cons #\- acc) acc)))
      (str::revappend-natchars id+1 acc)))

  (define dimacs-write-clause ((clause lit-listp) (acc character-listp))
    :returns (acc character-listp :hyp :guard)
    (b* (((when (atom clause))
          ;; End of clause, write the terminating 0 and a newline.
          (cons #\Newline (cons #\0 acc)))
         (acc (dimacs-write-lit (car clause) acc))
         (acc (cons #\Space acc)))
      (dimacs-write-clause (cdr clause) acc)))

  (define dimacs-write-clauses ((clauses lit-list-listp) (acc character-listp))
    :returns (acc character-listp :hyp :guard)
    (b* (((when (atom clauses))
          acc)
         (acc (dimacs-write-clause (car clauses) acc)))
      (dimacs-write-clauses (cdr clauses) acc)))

  (define dimacs-write-formula ((formula lit-list-listp))
    :returns (mv (dimacs-text stringp :hyp :guard)
                 (max-index   (equal max-index (max-index-formula formula))))
    (b* ((max-index (max-index-formula formula))
         ;; Increment all IDs to account for 0 not being a valid DIMACS variable
         (dimacs-num-vars (+ 1 max-index))
         (acc nil)
         (acc (str::revappend-chars
               "c CNF problem in DIMACS format, exported from ACL2."
               acc))
         (acc (cons #\Newline acc))
         ;; P CNF NUM-VARS NUM-CLAUSES
         (acc (str::revappend-chars "p cnf " acc))
         (acc (str::revappend-natchars dimacs-num-vars acc))
         (acc (cons #\Space acc))
         (acc (str::revappend-natchars (len formula) acc))
         (acc (cons #\Newline acc))
         (acc (dimacs-write-clauses formula acc)))
      (mv (str::rchars-to-string acc) max-index)))

  (define dimacs-export ((formula lit-list-listp)
                         &key
                         (filename stringp)
                         (state 'state))
    :returns (mv (successp "We can fail, e.g., due to file permissions."
                           booleanp :rule-classes :type-prescription)
                 (max-index "Maximum index used in the formula."
                            (equal max-index (max-index-formula formula)))
                 (state state-p1 :hyp (force (state-p1 state))))
    (b* ((filename (mbe :logic (if (stringp filename)
                                   filename
                                 "")
                        :exec filename))
         ((mv channel state) (open-output-channel filename :character state))
         ((unless channel)
          (mv nil (max-index-formula formula) state))
         ((mv str max-index) (dimacs-write-formula formula))
         (state (princ$ str channel state))
         (state (close-output-channel channel state)))
      (mv t max-index state))))