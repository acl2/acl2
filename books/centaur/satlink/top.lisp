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

; top.lisp -- Main file to include to use SATLINK.

(in-package "SATLINK")
(include-book "cnf")
(include-book "dimacs")
(include-book "str/natstr" :dir :system)
(include-book "str/strnatless" :dir :system)
(include-book "oslib/tempfile" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "config")
(local (include-book "std/lists/nthcdr" :dir :system))

(defxdoc satlink
  :parents (acl2::boolean-reasoning)
  :short "A simple representation for Boolean formulas in <see topic='@(url
cnf)'>conjunctive normal form</see>, and a mechanism for calling SAT solvers
from within ACL2 and trusting what they say. (CCL Only)"

  :long "<p>SAT solvers are programs that can solve the <a
href='https://en.wikipedia.org/wiki/Boolean_satisfiability_problem'>Boolean
satisfiability problem</a>.  Modern solvers implement clever algorithms in fast
languages like C and C++, so they can quickly solve many large problems.
Developing faster SAT solvers is an active area of research with frequent <a
href='http://www.satcompetition.org/'>competitions</a>.</p>

<p>SAT solvers are useful because many problems can be recast as SAT problems.
For instance, the @(see gl::gl) framework can translate many ACL2 proof goals,
e.g., bounded arithmetic problems, into SAT problems.  This allows for a large
class of theorems to be solved quickly and automatically by the SAT solver.
This is especially useful in @(see acl2::hardware-verification).</p>

<p><b>Satlink</b> is an interfacing library that allows ACL2 to make use of
off-the-shelf SAT solvers like <a
href='http://fmv.jku.at/lingeling/'>lingeling</a>, <a
href='https://www.lri.fr/~simon/?page=glucose'>glucose</a>, and so on.  It
provides:</p>

<ul>

<li>A (trivial) representation and semantics for Boolean formulas in
conjunctive normal form; see @(see cnf).</li>

<li>A function, @(see sat), that can invoke a SAT solver on a formula and
interpret its output.  This is done via @(see acl2::tshell), so the integration
is very smooth, e.g., you can interrupt the SAT solver.</li>

<li>A @(see logical-story) that allows us to <color rgb='#ff0000'><b>assume,
using a <see topic='@(url defttag)'>trust tag</see></b></color>, that when the
SAT solver claims the formula is unsatisfiable, it's correct.</li>

</ul>

<p>We don't have to assume anything when the SAT solver claims that a formula
is satisfiable, since we can just check the alleged satisfying assignment it
produces.</p>


<h3>Loading the Library</h3>

<p>Satlink is a low-level library.  It would be a bit weird to want to use it
directly.  Instead, it is typically used indirectly through other tools, such
as the @(see gl::gl) framework, or @(see acl2::aig-sat), or the @(see
aignet::aignet-cnf) translation.  These other approaches are likely to be more
convenient than using Satlink directly.</p>

<p>If you want to include Satlink directly for some reason, the book to include
is:</p>

@({
 (include-book \"centaur/satlink/top\" :dir :system)
})

<p>Once you load this book, you generally need to construct your input @(see
cnf) formula in some way, and then call @(see sat).</p>




<h3>Copyright Information</h3>

<p>Satlink &mdash; Link from ACL2 to SAT Solvers<br/>
Copyright (C) 2013 <a href=\"http://www.centtech.com\">Centaur Technology</a>.</p>

<p>Contact:</p>
@({
Centaur Technology Formal Verification Group
7600-C N. Capital of Texas Highway, Suite 300
Austin, TX 78731, USA.
})

<p>Satlink is free software; you can redistribute it and/or modify it under the
terms of the GNU General Public License as published by the Free Software
Foundation; either version 2 of the License, or (at your option) any later
version.</p>

<p>This program is distributed in the hope that it will be useful but WITHOUT
ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS
FOR A PARTICULAR PURPOSE.  See the GNU General Public License for more
details.</p>

<p>You should have received a copy of the GNU General Public License along with
this program; if not, write to the Free Software Foundation, Inc., 51 Franklin
Street, Suite 500, Boston, MA 02110-1335, USA.</p>")


(defsection dimacs-interp
  :parents (dimacs)
  :short "How we interpret the DIMACS formatted output from the SAT solver.")

(define satlink-skip-ws
  :parents (dimacs-interp)
  ((x  stringp               "String we're processing")
   (n  natp                  "Current position in @('x').")
   (xl (equal xl (length x)) "Pre-computed length of @('x')."))
  :guard (<= n xl)
  :returns (new-n natp "New position after skipping whitespace.")
  :measure (nfix (- (nfix xl) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix xl) (nfix n)))
                   :exec (int= xl n) ;; It's *really* fast
                   ))
        (lnfix n))
       (char (char x n))
       ((when (or (eql char #\Space)
                  (eql char #\Tab)))
        (satlink-skip-ws x (+ 1 (lnfix n)) xl)))
    (lnfix n))
  ///
  (defthm lower-bound-satlink-skip-ws
    (implies (natp n)
             (<= n (satlink-skip-ws x n xl)))
    :rule-classes ((:rewrite) (:linear)))
  (defthm lower-bound-satlink-skip-ws-nfix
    (<= (nfix n) (satlink-skip-ws x n xl))
    :rule-classes (:rewrite :linear))
  (defthm upper-bound-satlink-skip-ws
    (implies (and (natp n)
                  (natp xl)
                  (<= n xl))
             (<= (satlink-skip-ws x n xl) xl))
    :rule-classes ((:rewrite) (:linear))))

(define satlink-parse-variable-line
  :parents (dimacs-interp)
  ((x          stringp                "String we're processing.")
   (n          natp                   "Current position in @('x').")
   (xl         (equal xl (length x))  "Pre-computed length of @('x').")
   (saw-zero-p booleanp               "Have we seen a 0 yet?")
   (env$                              "Satisfying assignment we're populating."))
  :guard (<= n xl)
  :returns (mv (error      "True if there is an error parsing this line.")
               (saw-zero-p "Did we ever see 0?  (checked later).")
               (env$       "Updated satisfying assignment."))
  :measure (nfix (- (nfix xl) (nfix n)))
  (b* ((n (satlink-skip-ws x n xl))
       ((when (mbe :logic (zp (- (nfix xl) n))
                   :exec  (int= xl n)))
        ;; Reached end of line, all done.
        (mv nil saw-zero-p env$))
       ;; Should find a number here or a minus sign.
       (minus-p (eql (char x n) #\-))
       (n       (if minus-p (+ n 1) n))
       ((when (int= xl n))
        (cw "SATLINK: Error parsing variable line: ends with minus? ~s0" x)
        (mv t saw-zero-p env$))

       ((mv val len) (str::parse-nat-from-string x 0 0 n xl))
       ((when (zp len))
        ;; Expected a number here.
        (cw "SATLINK: Error parsing variable line: ~s0" x)
        (mv t saw-zero-p env$))
       ((when (and (zp val) saw-zero-p))
        (cw "SATLINK: Error: saw zero multiple times: ~s0" x)
        (mv t saw-zero-p env$))
       (saw-zero-p (or saw-zero-p (zp val)))
       (index (1- val)) ;; Adjusted for dimacs encoding
       (env$ (cond ((zp val)
                    env$)
                   ((< index (bits-length env$))
                    (set-bit index (if minus-p 0 1) env$))
                   (t
                    (prog2$
                     (raise "Assignment to out-of-bounds variable: ~x0" index)
                     env$)))))
    (satlink-parse-variable-line x (+ n len) xl saw-zero-p env$)))

(define satlink-handle-line
  :parents (dimacs-interp)
  ((line        "one line of sat solver output" stringp)
   (saw-unsat-p "have we seen an 's UNSATISFIABLE' line?")
   (saw-sat-p   "have we seen an 's SATISFIABLE' line?")
   (saw-zero-p  "have we seen a 0 in a 'v' line?")
   (env$        "evolving variable bindings"))
  :returns
  (mv (error-p "did we see something we don't understand?")
      saw-unsat-p
      saw-sat-p
      saw-zero-p
      env$)

  (b* ((len (length line))
       ((when (< len 2))
        ;; We'll ignore blank lines and lines that don't have a "x " at the
        ;; beginning, where x is "s" or "v".
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       (char (char line 0))
       ((unless (and (or (eql char #\s)  ;; Result
                         (eql char #\v)) ;; Variable assignment
                     (eql (char line 1) #\Space)))
        ;; Ignore it
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       ((when (eql char #\s))
        (cond ((str::strprefixp "s SATISFIABLE" line)
               (mv nil saw-unsat-p t saw-zero-p env$))
              ((str::strprefixp "s UNSATISFIABLE" line)
               (mv nil t saw-sat-p saw-zero-p env$))
              (t
               (prog2$
                (cw "SATLINK: Unrecognized result line: ~s0~%" line)
                (mv nil saw-unsat-p saw-sat-p saw-zero-p env$)))))
       ;; Else it's a variable line
       ((when saw-zero-p)
        (cw "SATLINK: Variable lines after already saw zero: ~s0~%" line)
        (mv t saw-unsat-p saw-sat-p saw-zero-p env$))
       ((mv error saw-zero-p env$)
        (satlink-parse-variable-line line 1 len nil env$)))
    (mv error saw-unsat-p saw-sat-p saw-zero-p env$)))

(define satlink-handle-lines
  :parents (dimacs-interp)
  ((lines string-listp)
   (saw-unsat-p "have we seen an 's UNSATISFIABLE' line?")
   (saw-sat-p   "have we seen an 's SATISFIABLE' line?")
   (saw-zero-p  "have we seen a 0 in a 'v' line?")
   (env$        "evolving variable bindings"))
  :returns
  (mv (error-p "did we see something we don't understand?")
      saw-unsat-p
      saw-sat-p
      saw-zero-p
      env$)
  (b* (((when (atom lines))
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       ((mv error-p saw-unsat-p saw-sat-p saw-zero-p env$)
        (satlink-handle-line (car lines) saw-unsat-p saw-sat-p saw-zero-p env$))
       ((when error-p)
        (mv error-p saw-unsat-p saw-sat-p saw-zero-p env$)))
    (satlink-handle-lines (cdr lines) saw-unsat-p saw-sat-p saw-zero-p env$)))

(define satlink-parse-output
  :parents (dimacs-interp)
  ((out  string-listp "output lines from the SAT solver.")
   (env$              "empty env to populate, should be sized already."))
  :returns (mv (status "Either :failed, :sat, or :unsat")
               (env$   "Variable assignment, in the :sat case."))
  (b* (((mv error-p saw-unsat-p saw-sat-p saw-zero-p env$)
        (satlink-handle-lines out nil nil nil env$))
       ((when error-p)
        ;; Already printed a warning
        (mv :failed env$))
       ;; There are a couple of other weird things to detect.
       ((when (and saw-unsat-p saw-sat-p))
        (cw "SATLINK: solver says both SAT and UNSAT?   Uh... guys?")
        (mv :failed env$))
       ((when (and saw-sat-p (not saw-zero-p)))
        (cw "SATLINK: solver says SAT but we didn't find a 0 in variable lines?")
        (mv :failed env$))
       ((when (and saw-unsat-p saw-zero-p))
        (cw "SATLINK: solver says UNSAT but is giving us variables?")
        (mv :failed env$))
       ((when saw-unsat-p)
        (mv :unsat env$))
       ((when saw-sat-p)
        (mv :sat env$)))
    ;; Didn't see either sat or unsat.
    (mv :failed env$)))


(define satlink-run-impl
  :parents (logical-story)
  :short "Core function used to run the SAT solver."
  ((config config-p       "Which solver to call, etc.")
   (cnf    lit-list-listp "The formula to solve.")
   (env$   "Empty env to populate, will usually be resized")
   &key
   (state 'state))
  :returns (mv (status ":sat, :unsat, or :failed")
               (env$ "Variable assignment, in the :sat case.")
               (state state-p1 :hyp (state-p1 state)))
  :long "<p>This function actually runs the SAT solver: it exports the formula
into a @(see dimacs) file, invokes the SAT solver on it, and interprets the
answer.  This function is typically never used directly; instead see @(see
satlink-run).</p>"

  (b* (((config config) config)

       ((mv filename state) (oslib::tempfile "satlink"))
       ((unless filename)
        (cw "SATLINK: Error generating temporary filename.~%")
        (mv :failed env$ state))

       ((mv okp max-index state)
        (time$ (dimacs-export cnf :filename filename)
               :msg "; SATLINK: writing ~s0: ~st sec, ~sa bytes~%"
               :args (list filename)
               :mintime config.mintime))

       ((unless okp)
        (cw "SATLINK: Error writing dimacs file ~s0~%" filename)
        (mv :failed env$ state))

       (cmd (str::cat config.cmdline " " filename))
       ((mv finishedp & lines)
        (time$ (acl2::tshell-call cmd
                                  :print config.verbose
                                  :save t)
               :msg "; SATLINK: `~s0`: ~st sec, ~sa bytes~%"
               :args (list cmd)
               :mintime config.mintime))

       (- (or (not config.remove-temps)
              (b* (((mv & & &)
                    (acl2::tshell-call (str::cat "rm " filename))))
                nil)))

       ((unless finishedp)
        (cw "SATLINK: Call of ~s0 somehow did not finish.~%" cmd)
        (mv :failed env$ state))
       ((unless (string-listp lines))
        (cw "SATLINK: Tshell somehow didn't give us a string list.~%")
        (mv :failed env$ state))
       ((mv status env$)
        (time$ (b* ((env$ (resize-bits (1+ max-index) env$))
                    ((mv status env$) (satlink-parse-output lines env$)))
                 (mv status env$))
               :msg "; SATLINK: interpreting output: ~st sec, ~sa bytes~%"
               :mintime config.mintime)))
    (mv status env$ state)))


(defsection logical-story
  :parents (satlink)
  :short "How we logically assume that the SAT solver's claims of unsat are
correct."

  :long "<p>The whole point of Satlink is to be able to call an external SAT
solver, written in C or C++, and trust its results.  Here, we explain exactly
how we do that.</p>

<p>Our assumptions about the SAT solver will be expressed as constraints about
a new function, @('satlink-run-fn').  Informally, the idea behind this function
is that it will have the following signature:</p>

<code>
 (satlink-run-fn config formula env$) &rarr; (status env$)
</code>

<dl>

<dt>Inputs</dt>

<dd>@('config') is a @(see config-p) that says which SAT solver to run and how
to run it.</dd>

<dd>@('formula') is the @(see cnf) formula to solve.</dd>

<dd>@('env$') is @(see env$), a bit array that will be used to store the
satisfying assignment from the SAT solver, in the SAT case.</dd>

<dt>Outputs</dt>

<dd>@('status') is the answer we get back from the SAT solver; in practice it
will either be @(':sat') or @(':unsat'), or perhaps @(':failed') if we run into
some kind of gross error&mdash;for instance, perhaps the SAT solver produces
output that we weren't expecting, like \"Segmentation fault\" or
\"Killed\".</dd>

<dd>@('env$') is the updated @(see env$) bit array; in the @(':sat') case it
should contain the satisfying assignment.</dd>

</dl>

<h3>Axiomatization</h3>

<p>We use ACL2's @(see define-trusted-clause-processor) @(':partial-theory')
feature to assume that the function satisfies certain constraints.</p>

<p>To make our story as tight as possible, we would like to assume very little
about @('satlink-run-fn').  It turns out we only need three constraints, with
the first two constraints just saying that the function returns two values:</p>

@(thm true-listp-of-satlink-run-fn)
@(thm len-of-satlink-run-fn)

<p>The final constraint is the real one.  The idea here is to express:</p>

<box><p>
   if @('satlink-run-fn') returns @(':unsat'),<br/>
   then the formula evaluates to false under every environment.
</p></box>

<p>But the quantification here isn't quite right for a rewrite rule, so
instead we assume the contrapositive:</p>

<box><p>
   if NOT(the formula evaluates to false under every environment),<br/>
   then NOT( @('satlink-run-fn') returns @(':unsat') )
</p></box>

<p>Which simplifies down to:</p>

<box><p>
   if the formula evaluates to true under any environment,<br/>
   then @('satlink-run-fn') does not return @(':unsat')
</p></box>

<p>So the real constraint looks like this:</p>

@(thm satlink-run-fn-unsat-claim)


<p>And that's it.  We don't need to assume anything about what happens in the
@(':sat') case, because our top-level @(see sat) wrapper can just check any
@(':sat') answers.</p>")

(defun satlink-useless-clauseproc (clause)
  (list clause))

(defttag :satlink)

(define-trusted-clause-processor
  satlink-useless-clauseproc
  (satlink-run-fn)
  :partial-theory
  (encapsulate
    (((satlink-run-fn * * env$) => (mv * env$)
      :formals (config formula env$)
      :guard (and (config-p config)
                  (lit-list-listp formula))))
    (local (defun satlink-run-fn (config formula env$)
             (declare (ignore config formula)
                      (xargs :stobjs env$))
             (mv :failed env$)))

    (defthm true-listp-of-satlink-run-fn
      (true-listp (satlink-run-fn config formula env$))
      :rule-classes :type-prescription)

    (defthm len-of-satlink-run-fn
      (equal (len (satlink-run-fn config formula env$)) 2))

    (defthm satlink-run-fn-unsat-claim
      (implies (equal (eval-formula formula arbitrary-env) 1)
               (not (equal (mv-nth 0 (satlink-run-fn config formula env$))
                           :unsat))))))

(defsection satlink-run
  :parents (logical-story)
  :short "Connection between the implementation and the logical story."

  :long "<p>In the logic, this function does nothing more than call
@('satlink-run-fn'), the constrained function that is the basis of our @(see
logical-story).</p>

<p>Under the hood, through a trust tag, we smash its definition and have it
invoke @(see satlink-run-impl), which actually calls the SAT solver.</p>"

  (defun satlink-run (config formula env$)
    "Returns (MV STATUS ENV$)"
    (declare (xargs :stobjs env$
                    :guard (and (config-p config)
                                (lit-list-listp formula))))
    (satlink-run-fn config formula env$))

  (progn!
   (set-raw-mode t)
   (defun satlink-run (config formula env$)
     (b* ((state acl2::*the-live-state*)
          (prev-okp            (f-get-global 'acl2::writes-okp state))
          (state               (f-put-global 'acl2::writes-okp t state))
          ((mv res env$ state) (satlink-run-impl config formula env$))
          (?state              (f-put-global 'acl2::writes-okp prev-okp state)))
       (mv res env$)))))

(define sat
  :parents (satlink)
  :short "Top-level function for running a SAT solver."

  ((formula "A @(see cnf) formula to solve." lit-list-listp)
   (env$    "Environment to populate with a satisfying assignment, in the case
             of SAT.  Will be emptied, in any case.")
   &key
   ((config "Configuration for running a SAT solver." config-p)
    '*default-config*))
  :returns (mv (status "@(':sat'), @(':unsat'), or @(':failed').")
               (env$   "Satisfying assignment, in the case of @(':sat')."))

  :long "<p>This is the top-level wrapper for calling SAT.  It handles the
details of clearing out the @(see env$) and checking the SAT solver's answers
in the SAT case.</p>"

  (b* (((config config) config)
       (env$ (mbe :logic (non-exec nil) :exec (resize-bits 0 env$)))
       ((mv status env$)
        (time$ (satlink-run config formula env$)
               :msg "; SATLINK: round trip: ~st sec, ~sa bytes.~%"
               :mintime config.mintime))
       ((unless (eq status :sat))
        (mv status env$))
       ((when (time$ (int= 0 (eval-formula formula env$))
                     :msg "; SATLINK: verifying assignment: ~st sec, ~sa bytes~%"
                     :mintime config.mintime))
        (cw "SAT: Supposedly satisfiable, but assignment is wrong~%")
        (mv :failed env$)))
    (mv :sat env$))
  ///
  (defthm sat-normalize-env
    (implies (syntaxp (not (equal env$ ''nil)))
             (equal (sat formula env$ :config config)
                    (sat formula nil :config config))))

  (defthm sat-when-sat
    (b* (((mv status new-env$) (sat formula env$ :config config)))
      (implies (equal status :sat)
               (equal (eval-formula formula new-env$) 1))))

  (defthm sat-when-unsat
    (b* (((mv status &) (sat formula env$ :config config)))
      (implies (equal (eval-formula formula env) 1)
               (not (equal status :unsat))))
    :hints (("goal" :use ((:instance satlink-run-fn-unsat-claim
                                     (env$ nil)))))))


#||

(tshell-ensure)

(sat '((1 2)) env$)

;; This is a good check to make sure writes-okp stuff is working.
(make-event
 (b* (((mv ans env$) (sat '((1 2)) env$)))
   (mv nil `(value-triple ,ans) state env$)))

||#
