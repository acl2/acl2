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

(defxdoc satlink
  :short "A way to call SAT solvers from within ACL2, and trust what they say."

  :long "<p>SATLINK is a basic connection to SAT solvers from within ACL2.  At
a high level, it provides:</p>

<ul>

<li>A (trivial) representation and semantics for Boolean formulas in <a
href='http://en.wikipedia.org/wiki/Conjunctive_normal_form'>conjunctive normal
form</a>; see @(see cnf).</li>

<li>A function, @(see sat), that can call an off-the-shelf SAT solver (e.g., <a
href='http://fmv.jku.at/lingeling/'>lingeling</a>) on a formula, and interpret
its output.</li>

<li>A logical story that allows us to assume, using a <see topic='@(see
defttag)'>trust tag</see>, that the SAT solver only claims that formulas are
unsatisfiable when this is indeed the case.  (When the SAT solver claims that a
formula is satisfiable, we can just check the alleged satisfying assignment it
produces.)</li>

</ul>")


; Parser for reading DIMACS output from the SAT solver...

(define satlink-skip-ws ((x stringp)
                         (n natp)
                         (xl (equal xl (length x))))
  :guard (<= n xl)
  :measure (nfix (- (nfix xl) (nfix n)))
  :returns (new-n natp)
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
  ((x stringp)
   (n natp "current position")
   (xl (equal xl (length x)))
   saw-zero-p
   env$)
  :guard (<= n xl)
  :returns (mv error saw-zero-p env$)
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
                     (er hard? __function__ "Assignment to out-of-bounds variable: ~x0" index)
                     env$)))))
    (satlink-parse-variable-line x (+ n len) xl saw-zero-p env$)))

(define satlink-handle-line
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
       ((when (zp len))
        ;; We'll just ignore blank lines
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       (char (char line 0))
       ((when (or (eql char #\c) ;; Comment line
                  (eql char #\t) ;; Timing line
                  ))
        ;; Ignore it
        (mv nil saw-unsat-p saw-sat-p saw-zero-p env$))
       ((when (eql char #\s))
        (cond ((str::strprefixp "s SATISFIABLE" line)
               (mv nil saw-unsat-p t saw-zero-p env$))
              ((str::strprefixp "s UNSATISFIABLE" line)
               (mv nil t saw-sat-p saw-zero-p env$))
              (t
               (prog2$
                (cw "SATLINK: Don't recognize this line: ~s0~%" line)
                (mv t saw-unsat-p saw-sat-p saw-zero-p env$)))))
       ((unless (eql char #\v))
        (cw "SATLINK: Don't recognize this line: ~s0~%" line)
        (mv t saw-unsat-p saw-sat-p saw-zero-p env$))
       ;; Else it's a variable line
       ((when saw-zero-p)
        (cw "SATLINK: Variable lines after already saw zero: ~s0~%" line)
        (mv t saw-unsat-p saw-sat-p saw-zero-p env$))
       ((mv error saw-zero-p env$)
        (satlink-parse-variable-line line 1 len nil env$)))
    (mv error saw-unsat-p saw-sat-p saw-zero-p env$)))

(define satlink-handle-lines
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
  ((out  string-listp)
   (env$ "empty env to populate, should be sized already."))
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
        (mv :unsat env$)))
    (mv :sat env$)))


; Core function to use to run the SAT solver.

(define satlink-run-impl ((config config-p)
                          (cnf    lit-list-listp)
                          (env$   "empty env to populate, will usually be resized")
                          &key
                          (state 'state))
  :returns (mv status
               (env$ "Variable assignment, in the :sat case.")
               (state state-p1 :hyp (state-p1 state)))
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


; Logical Story

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

(defun satlink-run (config formula env$)
  "Returns (MV STATUS ENV$)"
  (declare (xargs :stobjs env$
                  :guard (and (config-p config)
                              (lit-list-listp formula))))
  (satlink-run-fn config formula env$))

(progn!
 (set-raw-mode t)
 (defun satlink-run (config formula env$)
   (mv-let (res env$ state)
     (satlink-run-impl config formula env$ :state acl2::*the-live-state*)
     (declare (ignore state))
     (mv res env$))))


(define sat ((formula "A CNF formula to solve." lit-list-listp)
             (env$    "Environment to populate with a satisfying assignment,
                       in the case of SAT.  Will be emptied, in any case.")
             &key
             ((config "Configuration for running a SAT solver." config-p)
              '*default-config*))
  :parents (satlink)
  :short "Top-level function for running a SAT solver."
  :returns (mv (status "@(':sat'), @(':unsat'), or @(':failed').")
               (env$   "Satisfying assignment, in the case of @(':sat')."))
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
    (implies (eq (mv-nth 0 (sat formula env$ :config config)) :sat)
             (equal (eval-formula formula (mv-nth 1 (sat formula env$ :config config))) 1)))
  (defthm sat-when-unsat
    (implies (equal (eval-formula formula env) 1)
             (not (equal (mv-nth 0 (sat formula env$ :config config)) :unsat)))
    :hints (("goal" :use ((:instance satlink-run-fn-unsat-claim
                                     (env$ nil)))))))

