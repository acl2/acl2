; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "MILAWA")
(include-book "rule")
(include-book "compact-write-file")
(include-book "centaur/misc/seed-random" :dir :system)
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(ACL2::make-event
 (let ((proofs-dir (ACL2::extend-pathname ACL2::*path-to-milawa-acl2-directory*
                                          "../Proofs/"
                                          ACL2::state)))
   `(defconst *proofs-dir* ',proofs-dir)))

(defun get-current-libdir (ACL2::state)
  ;; The "libdir" is the immediate name of the directory this book resides in, i.e.,
  ;; if the full path to the book is "/foo/bar/baz/sets", then the libdir is "sets".
  ;; Ugh, ACL2 string manipulation is so shitty.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((cbd        (ACL2::cbd))
         (cbd-rev    (ACL2::reverse cbd))
         (cbd-rchars (STR::explode cbd-rev))
         (chop1      (if (equal (car cbd-rchars) ACL2::*directory-separator*)
                         (cdr cbd-rchars)
                       cbd-rchars))
         (pos        (ACL2::position ACL2::*directory-separator* chop1))
         (rdirchars  (ACL2::take pos chop1))
         (dirstr     (STR::implode (ACL2::reverse rdirchars))))
    dirstr))

(defun generate-filename (prefix name suffix ACL2::state)
  ;; We generate files of the form "libdir/prefix-name.suffix"
  ;;
  ;; Previously we also generated the path name for the proofs/ directory relative
  ;; to the current location for the book being certified, and some of the commented
  ;; out lines below implement this.
  ;;
  ;; Our new approach is that generate-filename only creates the filename and not
  ;; the directory.  The idea is to store everything into a single directory so we
  ;; can zip it up and move it around, and refer to things only relatively so it is
  ;; easy to move proofs.
  ;;
  ;; If you want to put the directory back into this function, you'll need to search
  ;; for uses of generate-filename and modify them appropriately.
  (declare (xargs :mode :program :stobjs ACL2::state)
           (ACL2::ignorable ACL2::state))
  (acl2::prog2$
   ;; HACK -- we now seed the random number generator here because if we're
   ;; generating a filename then we're probably about to write a file, and in
   ;; CCL the :supersede mode of open-file is based on a random filename that
   ;; derives from the current random seed, and if we have a bunch of ACL2
   ;; processes all writing to the same directory then we can easily get
   ;; clashes when they try to write their files.
   (ACL2::seed-random$ 'generate-filename)
   (let* ((libdir   (get-current-libdir ACL2::state))
          (partname (STR::cat (ACL2::mangle-filename (ACL2::string-downcase (ACL2::symbol-name name)))
                              "."
                              (ACL2::string-downcase (ACL2::symbol-name suffix))))
          (basename (if prefix
                        (STR::cat (ACL2::string-downcase (ACL2::symbol-name prefix)) "-" partname)
                      partname)))
     (ACL2::extend-pathname libdir basename ACL2::state))))

(defun logic.flag-warn-term-atblp (flag x atbl)
  ;; This is the same as logic.term-atblp, but it usefully prints a warning to
  ;; explain which subterm in particular is undefined or of improper arity.
  (declare (xargs :mode :program))
  (if (equal flag 'term)
      (cond ((logic.constantp x) t)
            ((logic.variablep x) t)
            ((logic.functionp x)
             (let ((name (logic.function-name x))
                   (args (logic.function-args x)))
               (and (or (equal (len args) (cdr (lookup name atbl)))
                        (if (lookup name atbl)
                            (ACL2::cw ";; Warning: found a call of the undefined function ~x0.~%" name)
                          (ACL2::cw ";; Warning: found a call of ~x0 with ~x1 args, but it takes ~x2 args.~%" name (len args) (cdr (lookup name atbl)))))
                    (logic.flag-warn-term-atblp 'list args atbl))))
            ((logic.lambdap x)
             (let ((body (logic.lambda-body x))
                   (actuals (logic.lambda-actuals x)))
               (and (logic.flag-warn-term-atblp 'term body atbl)
                    (logic.flag-warn-term-atblp 'list actuals atbl))))
            (t nil))
    (if (consp x)
        (and (logic.flag-warn-term-atblp 'term (car x) atbl)
             (logic.flag-warn-term-atblp 'list (cdr x) atbl))
     t)))

(defun logic.warn-term-atblp (x atbl)
  (declare (xargs :mode :program))
  (logic.flag-warn-term-atblp 'term x atbl))





;; Core proof checker emulation
;;
;; We manage an evolving list of axioms, theorems, definitions, and an evolving
;; arity table.  This basically emulates the Milawa core proof checker, except
;; that we're pretty permissive and don't require termination proofs, etc.  The
;; user could obviously tinker with these, and we do nothing to prevent that.
;; To really check your proofs, you need to use the external Milawa checker.

(ACL2::table tactic-harness 'axioms nil)
(ACL2::table tactic-harness 'thms nil)
(ACL2::table tactic-harness 'atbl (logic.initial-arity-table))

(ACL2::table tactic-harness 'world
             (tactic.world
              0 ;; initial index
              t ;; forcingp
              t ;; betamode  NIL, T, or 'ONCE
              1 ;; liftlimit
              0 ;; splitlimit
              50 ;; blimit
              100 ;; rlimit
              20 ;; rwn - still used?
              20 ;; urwn - still used?
              nil ;; noexec
              nil ;; theories
              nil ;; defs
              500 ;; depth
              nil ;; allrules
              t ;; assm-primaryp
              t ;; assm-secondaryp
              t ;; assm-directp
              t ;; assm-negativep
              ))

(defun tactic.harness->axioms (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'axioms (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->thms (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'thms (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->atbl (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'atbl (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->world (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'world (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->defs (acl2-world)
  (declare (xargs :mode :program))
  (tactic.world->defs (tactic.harness->world acl2-world)))

(defun tactic.harness->depth (acl2-world)
  (declare (xargs :mode :program))
  (tactic.world->depth (tactic.harness->world acl2-world)))

(defun tactic.world-wrapper (INDEX FORCINGP BETAMODE LIFTLIMIT SPLITLIMIT BLIMIT RLIMIT RWN URWN
                                      NOEXEC THEORIES DEFS DEPTH ALLRULES ASSM-PRIMARYP
                                      ASSM-SECONDARYP ASSM-DIRECTP ASSM-NEGATIVEP)
  (declare (xargs :mode :program))
  (tactic.world INDEX FORCINGP BETAMODE LIFTLIMIT SPLITLIMIT BLIMIT RLIMIT RWN URWN
                NOEXEC THEORIES DEFS DEPTH ALLRULES
                ASSM-PRIMARYP ASSM-SECONDARYP ASSM-DIRECTP ASSM-NEGATIVEP))

(defun tactic.world->index-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->index x))

(defun tactic.world->forcingp-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->forcingp x))

(defun tactic.world->betamode-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->betamode x))

(defun tactic.world->liftlimit-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->liftlimit x))

(defun tactic.world->splitlimit-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->splitlimit x))

(defun tactic.world->blimit-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->blimit x))

(defun tactic.world->rlimit-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->rlimit x))

(defun tactic.world->rwn-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->rwn x))

(defun tactic.world->urwn-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->urwn x))

(defun tactic.world->noexec-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->noexec x))

(defun tactic.world->theories-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->theories x))

(defun tactic.world->defs-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->defs x))

(defun tactic.world->depth-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->depth x))

(defun tactic.world->allrules-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->allrules x))

(defun tactic.world->assm-primaryp-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->assm-primaryp x))

(defun tactic.world->assm-secondaryp-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->assm-secondaryp x))

(defun tactic.world->assm-directp-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->assm-directp x))

(defun tactic.world->assm-negativep-wrapper (x)
  (declare (xargs :mode :program))
  (tactic.world->assm-negativep x))

(defun change-tactic.world-fn-wrapper (x alist)
  (declare (xargs :mode :program))
  (CONS 'TACTIC.WORLD-WRAPPER
        (LIST (IF (LOOKUP :INDEX ALIST)
                  (CDR (LOOKUP :INDEX ALIST))
                  (LIST 'TACTIC.WORLD->INDEX-wrapper X))
              (IF (LOOKUP :FORCINGP ALIST)
                  (CDR (LOOKUP :FORCINGP ALIST))
                  (LIST 'TACTIC.WORLD->FORCINGP-wrapper X))
              (IF (LOOKUP :BETAMODE ALIST)
                  (CDR (LOOKUP :BETAMODE ALIST))
                  (LIST 'TACTIC.WORLD->BETAMODE-wrapper X))
              (IF (LOOKUP :LIFTLIMIT ALIST)
                  (CDR (LOOKUP :LIFTLIMIT ALIST))
                  (LIST 'TACTIC.WORLD->LIFTLIMIT-wrapper X))
              (IF (LOOKUP :SPLITLIMIT ALIST)
                  (CDR (LOOKUP :SPLITLIMIT ALIST))
                  (LIST 'TACTIC.WORLD->SPLITLIMIT-wrapper X))
              (IF (LOOKUP :BLIMIT ALIST)
                  (CDR (LOOKUP :BLIMIT ALIST))
                  (LIST 'TACTIC.WORLD->BLIMIT-wrapper X))
              (IF (LOOKUP :RLIMIT ALIST)
                  (CDR (LOOKUP :RLIMIT ALIST))
                  (LIST 'TACTIC.WORLD->RLIMIT-wrapper X))
              (IF (LOOKUP :RWN ALIST)
                  (CDR (LOOKUP :RWN ALIST))
                  (LIST 'TACTIC.WORLD->RWN-wrapper X))
              (IF (LOOKUP :URWN ALIST)
                  (CDR (LOOKUP :URWN ALIST))
                  (LIST 'TACTIC.WORLD->URWN-wrapper X))
              (IF (LOOKUP :NOEXEC ALIST)
                  (CDR (LOOKUP :NOEXEC ALIST))
                  (LIST 'TACTIC.WORLD->NOEXEC-wrapper X))
              (IF (LOOKUP :THEORIES ALIST)
                  (CDR (LOOKUP :THEORIES ALIST))
                  (LIST 'TACTIC.WORLD->THEORIES-wrapper X))
              (IF (LOOKUP :DEFS ALIST)
                  (CDR (LOOKUP :DEFS ALIST))
                  (LIST 'TACTIC.WORLD->DEFS-wrapper X))
              (IF (LOOKUP :DEPTH ALIST)
                  (CDR (LOOKUP :DEPTH ALIST))
                  (LIST 'TACTIC.WORLD->DEPTH-wrapper X))
              (IF (LOOKUP :ALLRULES ALIST)
                  (CDR (LOOKUP :ALLRULES ALIST))
                  (LIST 'TACTIC.WORLD->ALLRULES-wrapper X))
              (IF (LOOKUP :ASSM-PRIMARY ALIST)
                  (CDR (LOOKUP :ASSM-PRIMARY ALIST))
                  (LIST 'TACTIC.WORLD->ASSM-PRIMARYp-wrapper X))
              (IF (LOOKUP :ASSM-SECONDARY ALIST)
                  (CDR (LOOKUP :ASSM-SECONDARY ALIST))
                  (LIST 'TACTIC.WORLD->ASSM-SECONDARYp-wrapper X))
              (IF (LOOKUP :ASSM-DIRECTP ALIST)
                  (CDR (LOOKUP :ASSM-DIRECTP ALIST))
                  (LIST 'TACTIC.WORLD->ASSM-DIRECTP-wrapper X))
              (IF (LOOKUP :ASSM-NEGATIVEP ALIST)
                  (CDR (LOOKUP :ASSM-NEGATIVEP ALIST))
                  (LIST 'TACTIC.WORLD->ASSM-NEGATIVEP-wrapper X))
              )))

(defmacro change-tactic.world-wrapper (x &rest args)
  (CHANGE-TACTIC.WORLD-FN-WRAPPER
   X
   (CHANGER-ARGS-TO-ALIST ARGS
                          '(:INDEX :FORCINGP :BETAMODE
                                      :LIFTLIMIT :SPLITLIMIT
                                      :BLIMIT :RLIMIT
                                      :RWN :URWN :NOEXEC
                                      :THEORIES :DEFS
                                      :DEPTH :ALLRULES
                                      :ASSM-PRIMARY :ASSM-SECONDARY
                                      :ASSM-DIRECTP :ASSM-NEGATIVEP))))




;; Adding axioms to the database
;;
;; We add a formula using (%axiom formula).  We don't really do any checking on
;; axioms as we check them.  Instead, we expect that the axioms will be hard
;; coded into the standalone proof checker.

(defmacro %axiom (formula)
  `(ACL2::make-event (%axiom-fn ,formula (ACL2::w ACL2::state))))

(defun %axiom-fn (formula acl2-world)
  (declare (xargs :mode :program))
  (let ((axioms (tactic.harness->axioms acl2-world)))
    (cond ((not (logic.formulap formula))
           (ACL2::er hard '%axiom "~x0 is not even a formula.~%" formula))
          ((memberp formula axioms)
           `(ACL2::value-triple :redundant))
          (t
           (ACL2::prog2$
            (ACL2::cw "Adding axiom: ~x0~%" formula)
            `(ACL2::progn (ACL2::table tactic-harness 'axioms
                                       (cons ',formula (tactic.harness->axioms ACL2::world)))
                          (ACL2::value-triple :invisible)))))))




;; Adding theorems to the database
;;
;; We want to record every theorem we add, and the order that we add them, and
;; remember the proofs that we used to admit them.
;;
;; Below, when we save proofs, we write out ".proof" files.  We remember which
;; proof files we have written using the thmfiles table, which is a list of
;; tuples of the form (type filename conclusion), and which are kept in the
;; reverse order of when we added them because we cons onto the front of the
;; list.
;;
;; We do not do any checking here to ensure that the proof has been checked
;; and saved.  Hence, the "raw"-ness of %raw-add-theorem.

(ACL2::table tactic-harness 'thmfiles nil)

(defun tactic.harness->thmfiles (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'thmfiles (ACL2::table-alist 'tactic-harness acl2-world))))

(defun %raw-add-theorem-fn (name formula)
  (declare (xargs :mode :program))
  `(ACL2::progn
    (ACL2::table tactic-harness 'thms
                 (cons ,formula (tactic.harness->thms ACL2::world)))
    (ACL2::make-event
     ;; We use a relative file name here so that the proofs directory can be
     ;; moved around easily.
     (let ((filename  (STR::cat "Proofs/" (generate-filename 'thm ',name 'proof ACL2::state)))
           (formula  ,formula)
           (name     ',name))
       `(ACL2::table tactic-harness 'thmfiles
                     (cons (list 'VERIFY ',name ',formula ',filename)
                           (tactic.harness->thmfiles ACL2::world)))))))

(defmacro %raw-add-theorem (name formula)
  (%raw-add-theorem-fn name formula))




;; Support for multiple proof checking layers
;;
;; We can transition the tactic harness from using logic.proofp to instead
;; using a higher-level proof checker.  We store the name of the currently
;; loaded proof checker in this table entry.  As with the lists of axioms and
;; theorems, a user could tinker with this.  Use the external Milawa checker to
;; really have confidence in your proofs.

(ACL2::table tactic-harness 'current-proofp 'logic.proofp)
(ACL2::table tactic-harness 'current-adapter '%initial-adapter)

(defun tactic.harness->current-proofp (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'current-proofp (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->current-adapter (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'current-adapter (ACL2::table-alist 'tactic-harness acl2-world))))

(defun %current-proofp (proof axioms thms atbl)
  (declare (xargs :mode :program)
           (ignore proof axioms thms atbl))
  (ACL2::er hard '%current-proofp "Under-the-hood definition not properly installed."))

(defun %current-adapter (proof defs initial-world all-worlds)
  (declare (xargs :mode :program)
           (ignore proof defs initial-world all-worlds))
  ;; Adapter gets to look at the defs, initial world, and list of all compiled worlds.
  ;; Note that initial-world and all-worlds MAY BE NIL when functions are admitted.  See
  ;; the horrible mess in %admit-finalize-fn for details.
  (ACL2::er hard '%current-adapter "Under-the-hood definition not properly installed."))

(defun %initial-adapter (proof defs initial-world all-worlds)
  ;; In the initial steps, we don't need any kind of adaptation.
  (declare (xargs :mode :program)
           (ignore defs initial-world all-worlds))
  proof)

(encapsulate
 ()
 (ACL2::defttag %current-proofp)
 (ACL2::progn!
  (ACL2::set-raw-mode t)

  (ACL2::defun %current-proofp (proof axioms thms atbl)
               (let* ((acl2-world     (ACL2::w ACL2::*the-live-state*))
                      (current-proofp (tactic.harness->current-proofp acl2-world)))
                 (ACL2::funcall current-proofp proof axioms thms atbl)))

  (ACL2::defun %current-adapter (proof defs initial-world all-worlds)
               (let* ((acl2-world      (ACL2::w ACL2::*the-live-state*))
                      (current-adapter (tactic.harness->current-adapter acl2-world)))
                 (ACL2::funcall current-adapter proof defs initial-world all-worlds)))))

(defun %current-adapter-list (proofs defs initial-world all-worlds)
  (declare (xargs :mode :program))
  (if (consp proofs)
      (cons (%current-adapter (car proofs) defs initial-world all-worlds)
            (%current-adapter-list (cdr proofs) defs initial-world all-worlds))
    nil))

(defun %current-proof-listp (proofs axioms thms atbl)
  (declare (xargs :mode :program))
  (if (consp proofs)
      (and (%current-proofp (car proofs) axioms thms atbl)
           (%current-proof-listp (cdr proofs) axioms thms atbl))
    t))



;; Interactive proof management
;;
;; We manage an evolving proof skeleton for the "current proof attempt".  This
;; is implicitly operated on by all our tactics.

(ACL2::table tactic-harness 'skeleton nil)

(defun tactic.harness->skeleton (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'skeleton (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->goals (acl2-world)
  (declare (xargs :mode :program))
  (tactic.skeleton->goals (tactic.harness->skeleton acl2-world)))




(ACL2::table tactic-harness 'quiet nil)

(defun tactic.harness->quiet (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'quiet (ACL2::table-alist 'tactic-harness acl2-world))))

(defmacro %quiet (&optional (quietp 't))
  ;; Control whether (%print) should make any output
  ;;
  ;;   (%quiet)      Turns on quiet mode, suppressing %print's output
  ;;   (%quiet nil)  Turns off quiet mode
  `(ACL2::table tactic-harness 'quiet ,quietp))

(defun %print-choose-goals (args goals i)
  ;; Args are the list of arguments given to %print.  We walk through the list
  ;; of goals, and keep the ith goal only if it is mentioned in args or if * is
  ;; mentioned.  We produce a list of (index . goal) pairs for all of the goals
  ;; we're supposed to keep.
  (declare (xargs :mode :program))
  (if (consp goals)
      (if (or (memberp i args)
              (memberp 'all args))
          (cons (cons i (car goals))
                (%print-choose-goals args (cdr goals) (+ 1 i)))
        (%print-choose-goals args (cdr goals) (+ 1 i)))
    nil))

(defun %print-negate-hyps (hyps)
  ;; Given a list of terms, we "negate" them by wrapping them in "not" or
  ;; stripping the "not" as appropriate.
  (declare (xargs :mode :program))
  (if (consp hyps)
      (let* ((hyp1 (car hyps))
             (hyp1-negated (if (and (logic.functionp hyp1)
                                    (equal (logic.function-name hyp1) 'not)
                                    (equal (len (logic.function-args hyp1)) 1))
                               (first (logic.function-args (car hyps)))
                             (logic.function 'not (list hyp1)))))
        (cons hyp1-negated (%print-negate-hyps (cdr hyps))))
    nil))

(defun %print-make-implication (goal)
  ;; Turn a clause into an analagous implies statement.
  (declare (xargs :mode :program))
  (if (consp (cdr goal))
      ;; More than one disjunct, make an implies.
      (let* ((hyps  (firstn (- (len goal) 1) goal))
             (nhyps (%print-negate-hyps hyps))
             (concl (car (restn (- (len goal) 1) goal))))
        `(implies (and ,@nhyps) ,concl))
    ;; Only one disjunct, the goal is this disjunct alone.
    (car goal)))

(defun %print-write-goals (chosen rawp ACL2::state)
  ;; Print out each of the chosen goals.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (if (not (consp chosen))
      ACL2::state
    (let ((number (car (car chosen)))
          (goal   (cdr (car chosen))))
      (ACL2::mv-let (col ACL2::state)
                    (ACL2::fmt "  ~s0~x1.~s2 " (list (cons #\0 *green*)
                                                     (cons #\1 number)
                                                     (cons #\2 *black*))
                               ACL2::*standard-co* ACL2::state nil)
                    (ACL2::mv-let (col ACL2::state)
                                  (ACL2::fmt1 "~q0~%"
                                              (list (cons #\0 (if rawp goal (%print-make-implication goal))))
                                              ;; We have to subtract the "lengths" of the character codes, which
                                              ;; fixes ugly stairstepped output and makes it look right
                                              (- col (+ (ACL2::length *green*)
                                                        (ACL2::length *black*)))
                                              ACL2::*standard-co* ACL2::state nil)
                                  (declare (ignore col))
                                  (%print-write-goals (cdr chosen) rawp ACL2::state))))))

(defun %print-core (args goals ACL2::state)
  ;; Decide which goals to print out and then print them.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((numgoals   (len goals))
         (rawp       (memberp 'raw args))
         (args-prime (if rawp (remove-all 'raw args) args))
         (choose-us  (if (consp args-prime)
                         args-prime
                       (list 1 2 3)))
         (chosen     (%print-choose-goals choose-us goals 1)))
    (ACL2::prog2$
     (cond ((equal numgoals 0) (ACL2::cw "All goals have been proven.~%"))
           ((equal numgoals 1) (ACL2::cw "One goal remains.~%"))
           (t                  (ACL2::cw "~N0 goals remain.~%" numgoals)))
     (%print-write-goals chosen rawp ACL2::state))))

(defun %print-fn (args ACL2::state)
  ;; Decide which goals to print out and then print them.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world (ACL2::w ACL2::state)))
    (if (tactic.harness->quiet acl2-world)
        (ACL2::mv nil '(ACL2::value-triple :invisible) ACL2::state)
      (let ((ACL2::state (%print-core args (tactic.harness->goals acl2-world) ACL2::state)))
        (ACL2::mv nil '(ACL2::value-triple :invisible) ACL2::state)))))

(defmacro %print (&rest args)
  ;; Prints out the current goals
  ;;
  ;; By default, only the first three goals is shown, and each clause is
  ;; printed as a more friendly "implies" statement.  But you can override
  ;; these defaults by passing some parameters.  For example:
  ;;
  ;;   (%print all)         Prints all the goals.
  ;;   (%print 2 5 7 ...)   Prints goals 2, 5, 7, ...
  ;;   (%print raw ...)     Prints as clauses instead of "implies" terms
  `(local (ACL2::make-event (%print-fn ',args ACL2::state))))

(defmacro %interactive ()
  ;; Hide ugly ACL2 output generated by other % commands.
  '(ACL2::make-event
    (ACL2::er-progn (ACL2::set-inhibit-output-lst '(ACL2::event ACL2::summary ACL2::proof-tree))
                    (ACL2::value '(ACL2::value-triple nil)))))

(defmacro %noninteractive ()
  ;; Switch back to normal ACL2 output.
  '(ACL2::make-event
    (ACL2::er-progn (ACL2::set-inhibit-output-lst '(ACL2::proof-tree))
                    (ACL2::value '(ACL2::value-triple nil)))))

(ACL2::table tactic-harness 'warnp t)

(defun tactic.harness->warnp (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'warnp (ACL2::table-alist 'tactic-harness acl2-world))))

(defmacro %warn (&optional (warnp 't))
  ;; %warn can be used to suppress the output of some tactics when they
  ;; fail.
  ;;
  ;; Usage:
  ;;   (%warn)       Turn on warnings
  ;;   (%warn nil)   Turn off warnings
  ;;
  `(ACL2::table tactic-harness 'warnp ,warnp))




;; Saving proofs.
;;
;; By default, we build the proof objects upon %qed and %admit, and save them
;; to a file using the compact-write-file system.  You can turn this off if
;; you don't care about building the proofs by running (%building nil), or
;; re-enable it using (%building t).
;;
;; We also allow you to specify a maximum acceptable proof size, which is
;; really useful for discovering that some change to a tactic has caused a
;; proof to break, using (%max-proof-size n).  The default is 500 million
;; conses, at which point proofs are taking several minutes to check.  If
;; you set this to zero, it won't be checked.
;;
;; Typically we do not bother to check the proof before we write it to the
;; file, because this would slow us down during bootstrapping.  However,
;; dynamic checking can be turned on or off using (%checking t) and (%checking
;; nil), in case you're worried about some proofs.

(ACL2::table tactic-harness 'building t)
(ACL2::table tactic-harness 'checking nil)
(ACL2::table tactic-harness 'saving t)
(ACL2::table tactic-harness 'max-proof-size 500000000)

(defun tactic.harness->building (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'building (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->checking (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'checking (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->saving (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'saving (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->max-proof-size (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'max-proof-size (ACL2::table-alist 'tactic-harness acl2-world))))

(defmacro %checking (arg)
  (declare (xargs :guard (booleanp arg)))
  `(ACL2::table tactic-harness 'checking ,arg))

(defmacro %building (arg)
  (declare (xargs :guard (booleanp arg)))
  `(ACL2::table tactic-harness 'building ,arg))

(defmacro %saving (arg)
  (declare (xargs :guard (booleanp arg)))
  `(ACL2::table tactic-harness 'saving ,arg))

(defmacro %max-proof-size (&optional (n '500000000))
  `(ACL2::table tactic-harness 'max-proof-size ,n))

(defun %theorem-check (name formula proof ACL2::state)
  ;; Check that proof proves formula; write out the proof to a file.
  ;; Causes an ACL2 error if any errors are encountered.  Always returns nil.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world    (ACL2::w ACL2::state))
         (filename      (generate-filename 'thm name 'proof ACL2::state))
         (full-filename (ACL2::extend-pathname *proofs-dir* filename ACL2::state))
         (axioms        (tactic.harness->axioms acl2-world))
         (thms          (tactic.harness->thms acl2-world))
         (atbl          (tactic.harness->atbl acl2-world))
         (checking      (tactic.harness->checking acl2-world))
         (maxsize       (tactic.harness->max-proof-size acl2-world))
         (size          (unbounded-rank proof)))
    (ACL2::prog2$
     (ACL2::cw "; Preparing to check ~x0.~%" name)
     (ACL2::prog2$
      ;; Previously I also reported the number of unique conses with ACL2::number-subtrees,
      ;; but for large proof this was causing unacceptable delays.  And, in retrospect, it's
      ;; not really a very interesting number.
      (ACL2::cw ";; Proof size: ~s0~s1 conses~s2.~%"
                *green* (STR::pretty-number size) *black*)
      (if (and (not (ACL2::zp maxsize))
               (ACL2::< maxsize size))
          (ACL2::er hard '%theorem-check "The proof exceeds the maximum permitted proof size. ~
                                          Use (%max-proof-size n) to override this check.~%")
        (ACL2::prog2$
         (ACL2::cw "; ~s0 the proof.~%" (if checking "Checking" "Not checking"))
         (let ((proof-okp (if checking
                              (ACL2::time$ (%current-proofp proof axioms thms atbl))
                            t)))
           (cond ((not (equal (logic.conclusion proof) formula))
                  (ACL2::er hard '%theorem-check "The proof does not have the right conclusion.~%~
                                                  Want: ~x0~%~
                                                  Concludes: ~x1~%"
                            formula (logic.conclusion proof)))
                 ((not proof-okp)
                  (ACL2::er hard '%theorem-check "The proof was rejected by current-proofp.~%"))
                 ((tactic.harness->saving acl2-world)
                  ;; We're supposed to save the proof
                  (ACL2::prog2$ (ACL2::cw ";; Proof accepted.  Saving as ~s0~%" filename)
                                (compact-write-file proof full-filename)))
                 (t
                  (ACL2::cw ";; Proof saving is disabled, so we are done.~%"))))))))))





;; Defining functions
;;
;; NO NO NO.  There is now only one kind of definitions.  syndefs are gone.
;;
;; There are two kinds of definitions, and we keep them in separate lists.
;;
;;   - Defs are functions that have been properly introduced in the logic,
;;     exist in the arity table, and have their corresponding axioms available.
;;     These definitions are introduced using %defun and %admit.
;;
;;   - Syndefs are functions that have not been properly introduced, but yet
;;     can be used heuristically by our rewriter, etc.  These functions cannot
;;     be reasoned about, but don't need to terminate.

;; (defmacro %syntax-defun (name formals body)
;;   ;; Introduce a function for the syndefs list
;;   ;;
;;   ;; There is no admission obligation, and only minimal checking is performed:
;;   ;; the formals must be unique, the body may only mention the formals, it must
;;   ;; not conflict with some previous definition, etc.
;;   `(ACL2::make-event (%syntax-defun-fn ',name ',formals ',body (ACL2::w ACL2::state))))

(defmacro %defun (name formals body &key measure)
  ;; Introduce a function for the defs list (Part 1 of 2)
  ;;
  ;; In addition to the %syntax-defun requirements, the function may only call
  ;; previously %defun'ed functions and must be shown to terminate with the
  ;; given measure.  The termination obligations are loaded as the current
  ;; proof goals.  Once established, you should call (%admit) to finish
  ;; introducing the function.
  `(ACL2::make-event (%defun-fn ',name ',formals ',body ',measure (ACL2::w ACL2::state))))

(defmacro %admit ()
  ;; Introduce a function for the defs list (Part 2 of 2)
  ;;
  ;; This should be called once all the proof goals introduced by %defun have
  ;; been discharged; it saves the proofs and updates the thmfiles table with
  ;; the function introduction.
  `(ACL2::progn
    (local (ACL2::memoize 'unbounded-rank))
    (local (ACL2::make-event (%admit-check-fn ACL2::state)))
    (local (ACL2::unmemoize 'unbounded-rank))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))
    (ACL2::make-event (%admit-update-fn ACL2::state))
    (ACL2::make-event (%admit-finalize-fn ACL2::state))))

(ACL2::table tactic-harness 'goaldef     nil)
(ACL2::table tactic-harness 'goalmeasure nil)
(ACL2::table tactic-harness 'goalbody    nil)
(ACL2::table tactic-harness 'goalworld   nil)
; (ACL2::table tactic-harness 'separate-syndefsp t)

;; (defun tactic.harness->separate-syndefsp (acl2-world)
;;   (declare (xargs :mode :program))
;;   (cdr (lookup 'separate-syndefsp (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->goaldef (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'goaldef (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->goalmeasure (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'goalmeasure (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->goalbody (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'goalbody (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.harness->goalworld (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'goalworld (ACL2::table-alist 'tactic-harness acl2-world))))

(defun tactic.find-def (name defs)
  (declare (xargs :mode :program))
  (if (consp defs)
      (if (equal (logic.function-name (logic.=lhs (car defs))) name)
          (car defs)
        (tactic.find-def name (cdr defs)))
    nil))

;; (defun %syntax-defun-fn (name formals body acl2-world)
;;   (declare (xargs :mode :program))
;;   (cond ((not (logic.function-namep name))
;;          (ACL2::er hard '%syntax-defun "The proposed name, ~x0, is invalid.~%" name))
;;         ((not (logic.variable-listp formals))
;;          (ACL2::er hard '%syntax-defun "The proposed formals for ~x0 are invalid.~%" name))
;;         ((not (uniquep formals))
;;          (ACL2::er hard '%syntax-defun "The proposed formals for ~x0 are not unique.~%" name))
;;         ((not (tactic.harness->separate-syndefsp acl2-world))
;;          `(ACL2::value-triple :invisible))
;;         (t
;;          (let ((body (logic.translate body)))
;;            (cond ((not body)
;;                   (ACL2::er hard '%syntax-defun "The proposed body for ~x0 is not translatable to a term.~%" name))
;;                  ((not (subsetp (logic.term-vars body) formals))
;;                   (ACL2::er hard '%syntax-defun "The proposed body for ~x0 mentions free variable(s) ~&1.~%"
;;                             name (difference (logic.term-vars body) formals)))
;;                  (t
;;                   (let ((proposed-def (logic.pequal (logic.function name formals) body))
;;                         (existing-def (tactic.find-def name (tactic.harness->syndefs acl2-world))))
;;                     (if existing-def
;;                         (if (not (equal proposed-def existing-def))
;;                             (ACL2::er hard '%syntax-defun "The function ~x0 already has a different syndef.~%" name)
;;                           `(ACL2::value-triple :redundant))
;;                       `(ACL2::progn
;;                         (ACL2::table tactic-harness 'world
;;                                      (change-tactic.world-wrapper
;;                                       (tactic.harness->world ACL2::world)
;;                                       :syndefs
;;                                       ;; This one probably doesn't need to be a hons, but we do it anyway.  See the
;;                                       ;; comment in %admit-update-fn to see why.
;;                                       (ACL2::hons ',proposed-def
;;                                                   (tactic.harness->syndefs ACL2::world)))))))))))))



(defun %defun-fn (name formals body measure acl2-world)
  (declare (xargs :mode :program))
  (cond ((not (logic.function-namep name))
         (ACL2::er hard '%defun "The proposed name, ~x0, is invalid.~%" name))
        ((not (logic.variable-listp formals))
         (ACL2::er hard '%defun "The proposed formals are invalid.~%"))
        ((not (uniquep formals))
         (ACL2::er hard '%defun "The proposed formals are not unique.~%"))
        (t
         (let ((body-trans    (logic.translate body))
               (measure-trans (logic.translate measure))
               (new-atbl      (update name (len formals) (tactic.harness->atbl acl2-world))))
           (cond ((not body-trans)
                  (ACL2::er hard '%defun "The proposed body is not translatable to a term.~%"))
                 ((not measure-trans)
                  (ACL2::er hard '%defun "The proposed measure is not translatable to a term.~%"))
                 ((not (subsetp (logic.term-vars body-trans) formals))
                  (ACL2::er hard '%defun "The proposed body mentions free variable(s) ~&0.~%"
                            (difference (logic.term-vars body-trans) formals)))
                 ((not (subsetp (logic.term-vars measure-trans) formals))
                  (ACL2::er hard '%defun "The proposed measure mentions free variable(s) ~&0.~%"
                            (difference (logic.term-vars measure-trans) formals)))
                 ((not (logic.warn-term-atblp body-trans new-atbl))
                  (ACL2::er hard '%defun "The proposed body is invalid w.r.t. the current arity table.~%"))
                 (t
                  (let* ((proposed-def (logic.pequal (logic.function name formals) body-trans))
                         ;; We check the existing def in the syndefs, since anything in the actual defs
                         ;; should also occur in the syndefs.
                         (existing-def (tactic.find-def name (tactic.harness->defs acl2-world)))
                         (obligations  (logic.termination-obligations name formals body-trans measure-trans))
                         (ob-clauses   (clause.make-clauses-from-arbitrary-formulas obligations)))
                    (if (and existing-def (not (equal existing-def proposed-def)))
                        (ACL2::er hard '%defun "The function ~x0 is already defined differently.~%" name)
                      `(ACL2::progn
                        ;; We store the proposed definition and measure in the goaldef/goalmeasure variables.
                        (ACL2::table tactic-harness 'goaldef ',proposed-def)
                        (ACL2::table tactic-harness 'goalbody ',body)
                        (ACL2::table tactic-harness 'goalmeasure ',measure)
                        ;; We add the function to the arity table.  Why do we need to do this?  Well, consider
                        ;; a function like
                        ;;   (foo x) = (if (foo (car x)) (foo (cdr x)) nil)
                        ;; This isn't too contrived; for example, the "list" case in a typical mutual-recursion
                        ;; will have this form.  Then, (foo (car x)) is a ruler of the recursive call (foo (cdr x)),
                        ;; so we are allowed to assume it (foo (car x)) in the proof that (foo (cdr x)) is smaller.
                        ;; Of course, we won't "know" anything about foo because we don't add the axioms about foo
                        ;; until the admission proof is done.  But we still need to know that foo is an okay term
                        ;; during the admission proof, so we add it to the arity table even though it hasn't been
                        ;; properly admitted yet.  I am certain this is sound, since we could always do the same
                        ;; thing with an uninterpreted function in ACL2.
                        (ACL2::table tactic-harness 'atbl
                                     (update ',name ,(len formals) (tactic.harness->atbl ACL2::world)))
                        (local (ACL2::table tactic-harness 'goalworld
                                            (tactic.harness->world acl2::world)))
                        (local (ACL2::table tactic-harness 'skeleton (tactic.initial-skeleton ',ob-clauses)))
                        (local (%print)))))))))))



(defun %admit-check-fn (ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world    (ACL2::w ACL2::state))
         (skeleton      (tactic.harness->skeleton acl2-world))
         (goals         (tactic.skeleton->goals skeleton))
         (goaldef       (tactic.harness->goaldef acl2-world))
         (goalworld     (tactic.harness->goalworld acl2-world))
         (name          (logic.function-name (logic.=lhs goaldef)))
         (formals       (logic.function-args (logic.=lhs goaldef)))
         (defs          (tactic.harness->defs acl2-world))
         (body-trans    (logic.=rhs goaldef))
         (measure-trans (logic.translate (tactic.harness->goalmeasure acl2-world)))
         (filename      (generate-filename 'admit name 'proofs ACL2::state))
         (full-filename (ACL2::extend-pathname *proofs-dir* filename ACL2::state))
         (obligations   (logic.termination-obligations name formals body-trans measure-trans)))

    (cond ((consp goals)
           (ACL2::er hard '%admit "(%admit) called but there are outstanding goals.~%"))

          ((not (tactic.harness->building acl2-world))
           ;; We aren't building, saving, or checking proofs.
           (ACL2::prog2$ (ACL2::cw "; Skipping proof-compiling since (%building nil) is set.~%")
                         '(ACL2::value-triple :invisible)))

          (t
           ;; We need to at least build the proofs.
           (let* ((worlds (ACL2::prog2$
                           (ACL2::cw "; Compiling worlds for ~x0...~%" name)
                           (tactic.compile-worlds skeleton goalworld)))
                  (proofs (%current-adapter-list
                           (ACL2::prog2$
                            (ACL2::cw "; Compiling proofs for ~x0...~%" name)
                            (ACL2::time$
                             (clause.prove-arbitrary-formulas-from-their-clauses
                              obligations
                              (tactic.compile-skeleton skeleton worlds nil))))
                           defs goalworld worlds))
                  (axioms (tactic.harness->axioms acl2-world))
                  (thms   (tactic.harness->thms acl2-world))
                  (atbl   (tactic.harness->atbl acl2-world)))
             (ACL2::progn$
              (ACL2::cw ";; Preparing to admit ~x0.~%" name)
              (ACL2::cw ";; Proof sizes total: ~s0 conses (with ~s1 unique conses).~%"
                        (STR::pretty-number (unbounded-rank proofs))
                        (STR::pretty-number (ACL2::number-subtrees proofs)))
              ;; Check the proofs if checking is set.
              (if (not (tactic.harness->checking acl2-world))
                  (ACL2::cw "; Skipping proof-checking since (%checking nil) is set.~%")
                (let ((proofs-okp (ACL2::progn$
                                   (ACL2::cw "; Checking the proofs...~%")
                                   (ACL2::time$ (%current-proof-listp proofs axioms thms atbl)))))
                  (cond ((not proofs-okp)
                         (ACL2::er hard '%admit-check "Some proof was rejected by current-proofp.~%"))
                        ((not (equal (logic.strip-conclusions proofs)
                                     (logic.termination-obligations name formals body-trans measure-trans)))
                         (ACL2::er hard '%admit-check "The proofs do not have the right conclusions.~%"))
                        (t
                         (ACL2::cw "; Proof-checking completed.~%")))))
              ;; Save the proof is saving is set.
              (if (not (tactic.harness->saving acl2-world))
                  (ACL2::cw "; Skipping proof-saving since (%saving nil) is set.~%")
                (ACL2::progn$
                 (ACL2::cw ";; Proofs accepted.  Saving as ~s0~%" filename)
                 (compact-write-file proofs full-filename)))
              ;; All done.
              '(ACL2::value-triple :invisible)))))))

(defun %admit-update-fn (ACL2::state)
  ;; This is Part 1 of 2 after successfully checking the proofs of termination.
  ;;
  ;; We add the axiom, definition, and syntax definition for the function.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world (ACL2::w ACL2::state))
         (goaldef    (tactic.harness->goaldef acl2-world)))
    `(ACL2::progn
      (ACL2::table tactic-harness 'axioms
                   (cons ',goaldef (tactic.harness->axioms ACL2::world)))
      (ACL2::table tactic-harness 'world
                   (change-tactic.world-wrapper
                    (tactic.harness->world ACL2::world)
                    :defs
                    ;; BOZO this comment is outdated since magic-evaluator is no longer used.  I leave
                    ;; it in, in case we want to add it.
                    ;;
                    ;; It is VITALLY IMPORTANT that this be a hons, but the reason is obscure.  We need
                    ;; to make sure that "defs" stay the same as we pass them around, so magic-evaluator
                    ;; and magic-evaluator-bldr will be happy (it wants the defs it's passed to be literally
                    ;; EQ to the harness defs).  But the defs get put into urewrite/crewrite traces via
                    ;; the function rw.try-ground-simplify, which in turn calls rw.trace.  And in the file
                    ;; hons-proofs, we make rw.trace use hons instead of cons.  So, if the harness defs
                    ;; aren't in the hons space, they'll be re-consed then and put into the hons space.
                    ;; The easy fix is just to make sure the defs are always honsed.
                    (ACL2::hons ',goaldef (tactic.harness->defs ACL2::world))

                    ;; :syndefs
                    ;; ;; It probably doesn't matter that this is a hons, but we do it anyway.
                    ;; (if (tactic.harness->separate-syndefsp ACL2::world)
                    ;;     (ACL2::hons ',goaldef (tactic.harness->syndefs ACL2::world))
                    ;;  (tactic.harness->syndefs ACL2::world))

                    )))))

(defun %admit-finalize-fn (ACL2::state)
  ;; This is Part 2 of 2 after successfully checking the proofs of termination.
  ;;
  ;; We add the theorem and axiom for this function's definition.  We do this
  ;; separately from Part 1, because the theorem relies upon the axiom for the
  ;; function, and we want to check the theorem using theorem-check (so that it
  ;; gets written to a file, etc.)
  ;;
  ;; Note: this gets used non-locally, so do the work in the local make-event
  ;; rather than in the let* statement at the beginning here.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world (ACL2::w ACL2::state))
         (goaldef    (tactic.harness->goaldef acl2-world))
         (name       (logic.function-name (logic.=lhs goaldef)))
         (formals    (logic.function-args (logic.=lhs goaldef)))
         (body       (tactic.harness->goalbody acl2-world))
         (body-trans (logic.=rhs goaldef))
         (measure    (tactic.harness->goalmeasure acl2-world))
         ;; Relative file name for easy proofs-dir moving
         (filename   (STR::cat "Proofs/" (generate-filename 'admit name 'proofs ACL2::state)))
         (theorem    (logic.pnot (logic.pequal (logic.function 'equal (list (logic.function name formals) body-trans)) ''nil))))
    `(ACL2::progn
      (local (ACL2::make-event
              (let* ((proof (%current-adapter
                             (let* ((line1 (build.axiom ',goaldef)) ;; (fn args) = body
                                    (line2 (build.equal-from-pequal line1)) ;; (equal (fn args) body) = t
                                    (line3 (build.not-nil-from-t line2))) ;; (equal (fn args) body) != nil
                               line3)
                             (tactic.harness->defs (ACL2::w ACL2::state))
                             nil nil))
                     (proof-ok (%theorem-check ',name ',theorem proof ACL2::state)))
                (declare (ignore proof-ok))
                '(ACL2::value-triple :invisible))))
      (ACL2::table tactic-harness 'thmfiles
                   (cons (list 'DEFINE ',name ',formals ',body ',measure ',filename)
                         (tactic.harness->thmfiles ACL2::world)))
      (%raw-add-theorem ,name ',theorem)
      (%raw-add-rule (%rule ,name
                            :lhs ,(logic.function name formals)
                            :rhs ,body)))))






;; Introducing choice functions
;;
;; We have a defchoose facility like ACL2's.  This causes no proof obligation,
;; but several syntactic criteria must be met for the defchoose to be
;; acceptable.

(defmacro %defchoose (name bound-var free-vars body)
  `(ACL2::make-event (%defchoose-fn ',name ',bound-var ',free-vars ',body (ACL2::w ACL2::state))))

(defun %defchoose-fn (name bound-var free-vars body world)
  (declare (xargs :mode :program))
  (let ((atbl       (tactic.harness->atbl world))
        (body-trans (logic.translate body)))
    (cond ((not (logic.function-namep name))
           (ACL2::er hard '%defchoose "The name must be a function name, but is ~x0.~%" name))
          ((lookup name atbl)
           (ACL2::er hard '%defchoose "The name, ~x0, is already in use.~%" name))
          ((not (logic.variablep bound-var))
           (ACL2::er hard '%defchoose "The bound-var must be a variable, but is ~x0.~%" bound-var))
          ((not (logic.variable-listp free-vars))
           (ACL2::er hard '%defchoose "The free-vars must be a list of variables, but are ~x0.~%" free-vars))
          ((not (uniquep free-vars))
           (ACL2::er hard '%defchoose "The free-vars must be unique, but are ~x0.~%" free-vars))
          ((memberp bound-var free-vars)
           (ACL2::er hard '%defchoose "The bound-var, ~x0, unacceptably occurs among the free vars.~%" bound-var))
          ((not body-trans)
           (ACL2::er hard '%defchoose "The body cannot be translated into a term.~%"))
          ((not (subsetp (logic.term-vars body-trans) (cons bound-var free-vars)))
           (ACL2::er hard '%defchoose "The body mentions variable(s) which are not among the bound and free vars: ~&0~%"
                     (difference (logic.term-vars body-trans) (cons bound-var free-vars))))
          ((not (logic.warn-term-atblp body-trans atbl))
           (ACL2::er hard '%defchoose "The body is not valid w.r.t. the current arity table.~%"))
          (t
           ;; In ACL2, the new axiom is:
           ;;   (implies body (let ((bound-var (fn free-vars))) body))
           ;;
           ;; In other words:
           ;;   (implies body ((lambda (bound-var :: free-vars) body) (fn free-vars) free-vars))
           ;;
           ;; Which is equivalent to:
           ;;    body = nil v ((lambda (bound-var :: free-vars) body) (fn free-vars) free-vars) != nil
           (let ((new-axiom (logic.por (logic.pequal body-trans ''nil)
                                       (logic.pnot (logic.pequal (logic.lambda (cons bound-var free-vars)
                                                                               body-trans
                                                                               (cons (logic.function name free-vars) free-vars))
                                                                 ''nil)))))
             `(ACL2::progn
               (defun ,(ACL2::mksym 'defchoose-axiom-for- name) ()
                 ',new-axiom)
               (ACL2::table tactic-harness 'atbl
                            (update ',name ,(len free-vars) (tactic.harness->atbl ACL2::world)))
               (ACL2::table tactic-harness 'axioms
                            (cons ',new-axiom (tactic.harness->axioms ACL2::world)))
               (ACL2::table tactic-harness 'thmfiles
                            (cons (list 'SKOLEM ',name ',bound-var ',free-vars ',body)
                                  (tactic.harness->thmfiles ACL2::world)))))))))







;; Theories (rewrite rule collections)
;;
;; We provide a system for using named theories, and we can add and remove
;; rules from these theories.  Theories and rules "share a namespace" and
;; their names must be unique.

;; bleh -- what can we do to keep the rules separate but still in the same
;; named theory structure?

(defun tactic.harness->allrules (acl2-world)
  (declare (xargs :mode :program))
  (tactic.world->allrules (tactic.harness->world acl2-world)))

(defun tactic.harness->theories (acl2-world)
  (declare (xargs :mode :program))
  (tactic.world->theories (tactic.harness->world acl2-world)))

(defun tactic.create-theory-wrapper (newtheoryname copyofname world)
  (declare (xargs :mode :program))
  (tactic.create-theory newtheoryname copyofname world))

(defun tactic.create-theory-tac-wrapper (skelly newtheoryname copyofname)
  (declare (xargs :mode :program))
  (tactic.create-theory-tac skelly newtheoryname copyofname))


(defmacro %create-theory (theoryname &key copy-of)
  ;; %create-theory introduces a new theory.
  ;;
  ;; Usage:
  ;;   (%create-theory foo)                   Adds foo as the empty theory.
  ;;   (%create-theory foo :copy-of target)   Adds foo as a copy of the target theory.
  ;;
  ;; We can call %create-theory in two different contexts.
  ;;
  ;;  (1) During a proof, in which case the theory is (probably) local to the
  ;;      current proof attempt and we need to update the skeleton to reflect
  ;;      that the new theory is being added.
  ;;
  ;;      In this case, we need to update the world and also extend the skeleton
  ;;      so that the compiler knows to update its world.
  ;;
  ;;  (2) Outside of any proof attempt, in which case all we need to do is
  `(ACL2::progn
    ;; Step 1: Update the global world.
    (ACL2::table tactic-harness 'world
                 (let* ((theoryname ',theoryname)
                        (copy-of    ',copy-of)
                        (world      (tactic.harness->world ACL2::world)))
                   (tactic.create-theory-wrapper theoryname copy-of world)))
    ;; Step 2: Update the skeleton, if there currently is one.
    (ACL2::table tactic-harness 'skeleton
                 (let* ((theoryname ',theoryname)
                        (copy-of    ',copy-of)
                        (skelly     (tactic.harness->skeleton ACL2::world)))
                   (and skelly
                        (tactic.create-theory-tac-wrapper skelly theoryname copy-of))))))

(%create-theory default)

(defun tactic.e/d-wrapper (theoryname enables disables world)
  ;; Prevent guard checking for %e/d
  (declare (xargs :mode :program))
  (tactic.e/d theoryname enables disables world))

(defun tactic.e/d-tac-wrapper (x theoryname enables disables)
  ;; Prevent guard checking for %e/d-tac
  (declare (xargs :mode :program))
  (tactic.e/d-tac x theoryname enables disables))

(defmacro %e/d (theoryname enables disables)
  ;; %e/d enables and disables some rules
  ;;
  ;; Usage:
  ;;   (%e/d foo
  ;;         (rule theory (%gather ...) rule theory ...)  ;; <--- "enable these"
  ;;         (rule theory (%gather ...) rule theory ...)) ;; <--- "disable these"
  ;;
  ;; Like %create-theory we handle enables and disables globally or within proof
  ;; attempts, so we need to update the world and perhaps the skeleton.
  `(ACL2::progn
    ;; Step 1: Update the global world
    (ACL2::table tactic-harness 'world
                 (let* ((theoryname ',theoryname)
                        (enables    ',enables)
                        (disables   ',disables)
                        (world      (tactic.harness->world ACL2::world)))
                   (tactic.e/d-wrapper theoryname enables disables world)))
    ;; Step 2: Update the skeleton, if there currently is one
    (ACL2::table tactic-harness 'skeleton
                 (let* ((theoryname ',theoryname)
                        (enables    ',enables)
                        (disables   ',disables)
                        (skelly     (tactic.harness->skeleton ACL2::world)))
                   (and skelly
                        (tactic.e/d-tac-wrapper skelly theoryname enables disables))))
    (ACL2::value-triple :invisible)))

(defmacro %enable (theoryname &rest what)
  ;; %enable adds some rules to a theory.
  ;;
  ;; Usage:
  ;;   (%enable foo
  ;;            rule theory (%gather ...) rule theory ...)
  ;;
  `(%e/d ,theoryname ,what nil))

(defmacro %disable (theoryname &rest what)
  ;; %disable removes some rules from a theory.
  `(%e/d ,theoryname nil ,what))

(defmacro %pr (name)
  ;; (%pr name) tries to look up the rule of the given name.
  `(tactic.find-rule ',name (tactic.harness->world (ACL2::w ACL2::state))))


(defmacro %raw-add-rule (rule)
  `(ACL2::make-event (%raw-add-rule-fn ,rule (ACL2::w ACL2::state))))

(defun %raw-add-rule-fn (rule acl2-world)
  (declare (xargs :mode :program))
  (if (not (rw.rulep rule))
      (ACL2::er hard '%raw-add-rule "The proposed rule, ~x0, is invalid.~%" rule)
    (let* ((world         (tactic.harness->world acl2-world))
           (existing-rule (tactic.find-rule (rw.rule->name rule) world)))
      (cond ((tactic.find-theory (rw.rule->name rule) world)
             (ACL2::er hard '%raw-add-rule "The proposed name, ~x0, is already in use as a theory.~%"
                       (rw.rule->name rule)))
            ((and existing-rule
                  (equal existing-rule rule))
             `(ACL2::value-triple :redundant))
            (existing-rule
             (ACL2::er hard '%raw-add-rule
                       "The proposed name, ~x0, is already in use as a different rule.~%"
                       (rw.rule->name rule)))
            ((not (memberp (clause.clause-formula (rw.rule-clause rule))
                           (tactic.harness->thms acl2-world)))
             (ACL2::er hard '%raw-add-rule "The rule's formula, ~x0, is not currently a member of thms.~%"
                       (clause.clause-formula (rw.rule-clause rule))))
            (t
             (ACL2::prog2$
              (ACL2::cw! "New rule: ~s0~%" (rw.rule->name rule))
              `(ACL2::table tactic-harness 'world
                            (let* ((world    (tactic.harness->world ACL2::world))
                                   (allrules (tactic.world->allrules-wrapper world)))
                              (change-tactic.world-wrapper
                               world
                               :allrules (cons ',rule allrules))))))))))


(defun tactic.restrict-wrapper (theoryname rulename syntax world)
  (declare (xargs :mode :program))
  (tactic.restrict theoryname rulename syntax world))

(defun tactic.restrict-tac-wrapper (skelly theoryname rulename syntax)
  (declare (xargs :mode :program))
  (tactic.restrict-tac skelly theoryname rulename syntax))

(defmacro %restrict (theoryname rulename &rest syntax)
  (let ((syntax-trans (logic.translate-list syntax)))
    (if (not (car syntax-trans))
        (ACL2::er hard '%restrict
                  "Syntactic restrictions were not translateable.~%")
      `(ACL2::progn
         ;; Step 1: Update the global world
        (ACL2::table tactic-harness 'world
                     (let* ((theoryname ',theoryname)
                            (rulename   ',rulename)
                            (syntax     ',(cdr syntax-trans))
                            (world      (tactic.harness->world ACL2::world)))
                       (tactic.restrict-wrapper theoryname rulename syntax world)))
        ;; Step 2: Update the skeleton, if there currently is one
        (ACL2::table tactic-harness 'skeleton
                     (let* ((theoryname ',theoryname)
                            (rulename   ',rulename)
                            (syntax     ',(cdr syntax-trans))
                            (skelly     (tactic.harness->skeleton ACL2::world)))
                       (and skelly
                            (tactic.restrict-tac-wrapper skelly theoryname rulename syntax))))
        (ACL2::value-triple :invisible)))))



(defun tactic.cheapen-wrapper (theoryname what world)
  (declare (xargs :mode :program))
  (tactic.cheapen theoryname what world))

(defun tactic.cheapen-tac-wrapper (skelly theoryname what)
  (declare (xargs :mode :program))
  (tactic.cheapen-tac skelly theoryname what))

(defmacro %cheapen (theoryname &rest what)
  `(ACL2::progn
    ;; Step 1: Update the global world
    (ACL2::table tactic-harness 'world
                 (let* ((theoryname ',theoryname)
                        (what       ',what)
                        (world      (tactic.harness->world ACL2::world)))
                   (tactic.cheapen-wrapper theoryname what world)))
    ;; Step 2: Update the skeleton, if there currently is one
    (ACL2::table tactic-harness 'skeleton
                 (let* ((theoryname ',theoryname)
                        (what        ',what)
                        (skelly     (tactic.harness->skeleton ACL2::world)))
                   (and skelly
                        (tactic.cheapen-tac-wrapper skelly theoryname what))))
    (ACL2::value-triple :invisible)))




;; Proving lemmas
;;
;;  -- We can load up our skeleton with a conjecture using %prove.
;;  -- We then apply tactics until all the goals are relieved.
;;  -- We finally call %qed to compile the skeleton and submit the proof.

(ACL2::table tactic-harness 'goalrule nil)

(defun tactic.harness->goalrule (world)
  (declare (xargs :mode :program))
  (cdr (lookup 'goalrule (ACL2::table-alist 'tactic-harness world))))

(defmacro %prove (rule)
  `(ACL2::make-event (%prove-fn ,rule (ACL2::w ACL2::state))))

(defmacro %qed ()
  `(ACL2::progn
    (local (ACL2::memoize 'unbounded-rank))
    (local (ACL2::make-event (%qed-check-fn ACL2::state)))
    (ACL2::make-event (%qed-finalize-fn ACL2::state))
    (local (ACL2::unmemoize 'unbounded-rank))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))))

(defun %prove-fn (rule acl2-world)
  (declare (xargs :mode :program))
  (if (not (rw.rulep rule))
      (ACL2::er hard '%prove "The proposed rule, ~x0, is not valid.~%" rule)
    (let* ((world (tactic.harness->world acl2-world))
           (atbl  (tactic.harness->atbl acl2-world)))
      (cond ((not (rw.rule-atblp rule atbl))
             (ACL2::er hard '%prove "The proposed rule, ~x0, is not valid w.r.t. the current atbl.~%" rule))
            ((tactic.find-theory (rw.rule->name rule) world)
             (ACL2::er hard '%prove "The proposed name, ~x0, is already in use as the name of a theory.~%"
                       (rw.rule->name rule)))
            ((tactic.find-rule (rw.rule->name rule) world)
             (ACL2::er hard '%prove "The proposed name, ~x0, is already in use as the name of a rule.~%"
                       (rw.rule->name rule)))
            (t
             `(ACL2::progn
               (ACL2::table tactic-harness 'goalrule ',rule)
               (local (ACL2::table tactic-harness 'goalworld
                                   (tactic.harness->world ACL2::world)))
               (local (ACL2::table tactic-harness 'skeleton
                                   (tactic.initial-skeleton (list ',(rw.rule-clause rule)))))
               (local (%print))))))))

(defun %qed-check-fn (ACL2::state)
  ;; This is Part 1 of 2 for accepting a theorem.  We check the proof and write
  ;; its file.  If the proof is not acceptable, we cause an error.  Else we do
  ;; not change the state.  This operation is "local" inside %qed, so that it
  ;; will not be run while including uncertified files.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world   (ACL2::w ACL2::state))
         (skeleton  (tactic.harness->skeleton acl2-world))
         (goals     (tactic.skeleton->goals skeleton))
         (goalrule  (tactic.harness->goalrule acl2-world))
         (goalworld (tactic.harness->goalworld acl2-world))
         (defs      (tactic.harness->defs acl2-world))
         (name      (rw.rule->name goalrule))
         (formula   (clause.clause-formula (rw.rule-clause goalrule))))
    (cond ((consp goals)
           (ACL2::er soft '%qed "(%qed) called but there are outstanding goals.~%"))

          ((not (tactic.harness->building acl2-world))
           ;; We aren't building or checking proofs.
           (ACL2::prog2$ (ACL2::cw "; Skipping proof-compiling since (%building nil) is set.~%")
                         (ACL2::mv nil `(ACL2::value-triple :invisible) ACL2::state)))

          (t
           (let* ((worlds (ACL2::prog2$
                           (ACL2::cw "; Compiling worlds for ~x0...~%" name)
                           (tactic.compile-worlds skeleton goalworld)))
                  (proof  (%current-adapter
                           (ACL2::prog2$ (ACL2::cw "Compiling skeleton for ~x0.~%" name)
                                         (car (ACL2::time$ (tactic.compile-skeleton skeleton worlds nil))))
                           defs goalworld worlds))
                  (proof-okp (%theorem-check name formula proof ACL2::state)))
             (declare (ignore proof-okp))
             ;; NOTE: it is vitally important that ",proof" not occur in the
             ;; return-value immediately below.  If it does, then the proof
             ;; will be visible in the output of a make-event, and will be
             ;; saved in the .cert file.  This will make the cert files balloon
             ;; to hundreds of megabytes and slow our system down.
             (ACL2::mv nil `(ACL2::value-triple :invisible) ACL2::state))))))

(defun %qed-finalize-fn (ACL2::state)
  ;; This is Part 2 of 2 for accepting a theorem.  We do no proof checking, but
  ;; we update the thms and rules tables.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world (ACL2::w ACL2::state))
         (goalrule   (tactic.harness->goalrule acl2-world))
         (name       (rw.rule->name goalrule))
         (formula    (clause.clause-formula (rw.rule-clause goalrule))))
    (ACL2::mv nil
              `(ACL2::progn
                (%raw-add-theorem ,name ',formula)
                (%raw-add-rule ',goalrule))
              ACL2::state)))






;; Transitioning to a new proof checker
;;
;;  -- We can create a skeleton for the soundness theorem using (%install-new-proofp [new-proofp-function]).
;;  -- We then apply tactics until the goal is proven
;;  -- We finally call (%qed-install) to finalize the transition and install the new checker.
;;
;; Then, to start using higher-level builder functions,
;;  -- We call (%switch-builder old-name new-name) for each such builder

(ACL2::table tactic-harness 'new-proofp-name nil)

(defun tactic.harness->new-proofp-name (acl2-world)
  (declare (xargs :mode :program))
  (cdr (lookup 'new-proofp-name (ACL2::table-alist 'tactic-harness acl2-world))))

(defmacro %install-new-proofp (new-proofp)
  `(ACL2::make-event (%install-new-proofp-fn ',new-proofp ACL2::state)))

(defmacro %qed-install ()
  `(ACL2::progn
    (local (ACL2::memoize 'unbounded-rank))
    (local (ACL2::make-event (%qed-install-check ACL2::state)))
    (ACL2::make-event (%qed-install-finalize ACL2::state))
    (local (ACL2::unmemoize 'unbounded-rank))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))))

(defun %install-new-proofp-fn (name ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world  (ACL2::w ACL2::state))
         (atbl        (tactic.harness->atbl acl2-world)))
    (cond ((not (logic.function-namep name))
           (ACL2::er soft '%install-new-proofp "Expected ~x0 to be a function name.~%" name))
          ((not (equal 4 (cdr (lookup name atbl))))
           (ACL2::er soft '%install-new-proofp "Expected ~x0 to have arity 4.~%" name))
          (t
           (ACL2::value
            `(ACL2::progn
              (ACL2::table tactic-harness 'new-proofp-name ',name)
              (local (ACL2::table tactic-harness 'goalworld (tactic.harness->world ACL2::world)))
              (local (ACL2::table tactic-harness 'skeleton
                                  (tactic.initial-skeleton
                                   (list (list (logic.compile-formula (logic.soundness-claim ',name)))))))
              (local (%print))))))))

(defmacro %qed-install ()
  `(ACL2::progn
    (local (ACL2::memoize 'unbounded-rank))
    (local (ACL2::make-event (%qed-install-check ACL2::state)))
    (ACL2::make-event (%qed-install-finalize ACL2::state))
    (local (ACL2::unmemoize 'unbounded-rank))
    (local (ACL2::value-triple (ACL2::clear-memoize-tables)))))

(defun %qed-install-check (ACL2::state)
  ;; This is part 1 of 2 for transitioning to a new proof checker.  We compile
  ;; the skeleton and check the proof.  It must have the obligation for this
  ;; new-proofp.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((acl2-world  (ACL2::w ACL2::state))
         (skeleton    (tactic.harness->skeleton acl2-world))
         (goals       (tactic.skeleton->goals skeleton))
         (goalworld   (tactic.harness->goalworld acl2-world))
         (new-proofp  (tactic.harness->new-proofp-name acl2-world))
         (defs        (tactic.harness->defs acl2-world))
         (obligation  (logic.soundness-claim new-proofp)))
    (cond
     ((consp goals)
      (ACL2::er soft '%qed-install "There are still remaining goals.~%"))

     ((not (tactic.harness->building acl2-world))
      ;; We aren't building or checking proofs.
      (ACL2::prog2$ (ACL2::cw "; Skipping proof-compiling since (%building nil) is set.~%")
                    (ACL2::mv nil `(ACL2::value-triple :invisible) ACL2::state)))

     (t
      (let* ((worlds (ACL2::prog2$
                      (ACL2::cw "; Compiling worlds for installing ~s0...~%" new-proofp)
                      (tactic.compile-worlds skeleton goalworld)))
             (PROOF-BEFORE-ADAPTER
              (ACL2::prog2$ (ACL2::cw "Compiling skeleton for installing ~s0.~%" new-proofp)
                                   (car (ACL2::time$ (tactic.compile-skeleton skeleton worlds nil)))))
             (line-1 (second (build.compile-formula obligation)))   ;; OBLIG v (COMP OBLIG) = NIL
             (line-2 (build.commute-or line-1))                     ;; (COMP OBLIG) = NIL v OBLIG
             (line-3 (build.modus-ponens-2 proof-BEFORE-ADAPTER line-2))
             (proof  (%current-adapter line-3 defs goalworld worlds))
             ;; PROOF: (COMP OBLIG) != NIL
             (proof-okp (%theorem-check (ACL2::mksym 'install-new-proofp- new-proofp)
                                        obligation proof ACL2::state)))
        (declare (ignore proof-okp))
        (ACL2::mv nil `(ACL2::value-triple :invisible) ACL2::state))))))

(defun %qed-install-finalize (ACL2::state)
  ;; This is part 2 of 2 for transitioning to a new proof checker.  We assume
  ;; the proof has been accepted and everything is okay.  We need to change the
  ;; current-proofp to our new-proofp.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((world      (ACL2::w ACL2::state))
         (new-proofp (tactic.harness->new-proofp-name world))
         (obligation (logic.soundness-claim new-proofp)))
    `(ACL2::progn
      (%raw-add-theorem ,(ACL2::mksym 'install-new-proofp- new-proofp) ',obligation)
      (ACL2::table tactic-harness 'current-proofp ',new-proofp)
      (ACL2::table tactic-harness 'thmfiles
                   (cons (list 'SWITCH ',new-proofp)
                         (tactic.harness->thmfiles ACL2::world))))))



;; After switching proofp-levels, it's convenient to just slip in new
;; definitions for the builders that are introduced at that level under the
;; hood, using the same name as the previous builders.  We don't do any sanity
;; checking here, so the user must be very careful to use this command
;; correctly and only when appropriate.

(defmacro %switch-builder (old-name new-name)
  (declare (xargs :guard (and (logic.function-namep old-name)
                              (logic.function-namep new-name))))
  `(ACL2::make-event (let ((temp (%switch-builder-fn ',old-name ',new-name)))
                       (declare (ignore temp))
                       '(ACL2::value-triple :invisible))
                     ;; We need this to run even when books are being included.
                     :check-expansion t))

(defun %switch-builder-fn (old-name new-name)
  ;; This redefines the old-name function to new-name.
  (declare (xargs :mode :program))
  (declare (ignore old-name new-name))
  (ACL2::er hard '%switch-builder "Under the hood definition not installed."))

(encapsulate
 ()
 (ACL2::defttag %switch-builder)
 (ACL2::progn!
  (ACL2::set-raw-mode t)
  (ACL2::defun %switch-builder-fn (old-name new-name)
               (let* ((state       ACL2::*the-live-state*)
                      (world       (ACL2::w state))
                      (old-formals (cdr (lookup 'ACL2::formals (ACL2::getprops old-name 'ACL2::current-acl2-world world))))
                      (new-formals (cdr (lookup 'ACL2::formals (ACL2::getprops new-name 'ACL2::current-acl2-world world)))))
                 (cond ((memberp old-name (ACL2::get-functions-to-inline world))
                        (ACL2::er hard '%switch-builder "Refusing to switch-builder for inlined function ~x0.  (Since the ~
                                                         function was inlined our attempt at redefinition may miss some ~
                                                         calls, which could result in the old function being used.)~%"
                                  old-name))
                       ((not (equal old-formals new-formals))
                        (ACL2::er hard '%switch-builder "The formals for ~s0 and ~s1 are incompatible." old-formals new-formals))
                       (ACL2::progn
                        (ACL2::cw! "Switching ~s0 ==> ~s1~|" old-name new-name)
                        (ACL2::eval `(ACL2::defun ,old-name ,old-formals
                                                  (,new-name ,@new-formals)))))))))





; %save-events filename

(defmacro %save-events (filename)
  `(local (ACL2::make-event (%save-events-fn ,filename acl2::state))))

(defun print-list-of-objects (objects channel ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (if (not (consp objects))
      ACL2::state
    (let ((ACL2::state (ACL2::print-object$ (car objects) channel ACL2::state)))
      (print-list-of-objects (cdr objects) channel ACL2::state))))

(ACL2::defttag save-list-of-objects)

(defun save-list-of-objects (filename objects ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (ACL2::mv-let
   (channel ACL2::state)
   (ACL2::open-output-channel! filename :object ACL2::state)
   (let ((ACL2::state (print-list-of-objects objects channel ACL2::state)))
     (ACL2::close-output-channel channel ACL2::state))))

(defun thmfiles-to-events (thmfiles functions-to-inline)
  (declare (xargs :mode :program))
  (if (consp thmfiles)
      (cons (let ((entry (car thmfiles)))
              (cond ((equal (first entry) 'VERIFY)
                     (let ((name     (second entry))
                           (formula  (third entry))
                           (filename (fourth entry)))
                       (list 'VERIFY name formula filename)))
                    ((equal (first entry) 'DEFINE)
                     (let* ((name     (second entry))
                            (formals  (third entry))
                            (body     (fourth entry))
                            (measure  (fifth entry))
                            (inlinep  (memberp name functions-to-inline))
                            (filename (ACL2::sixth entry)))
                       (list 'DEFINE name formals body measure inlinep filename)))
                    ((equal (first entry) 'SKOLEM)
                     (let* ((name      (second entry))
                            (bound-var (third entry))
                            (free-vars (fourth entry))
                            (body      (fifth entry)))
                       (list 'SKOLEM name bound-var free-vars body)))
                    ((equal (first entry) 'SWITCH)
                     (let* ((name     (second entry)))
                       (list 'SWITCH name)))
                    ((equal (first entry) 'FINISH)
                     (let* ((name     (second entry)))
                       (list 'FINISH name)))
                    (t
                     (ACL2::er hard 'thmfiles-to-events "Unknown event type: ~x0.~%" (first entry)))))
            (thmfiles-to-events (cdr thmfiles) functions-to-inline))
    nil))

(defun %save-events-fn (filename ACL2::state)
  (declare (xargs :stobjs ACL2::state
                  :mode :program))
  (let ((ACL2::state
         (save-list-of-objects (ACL2::extend-pathname *proofs-dir* filename ACL2::state)
                               (thmfiles-to-events
                                (fast-rev (tactic.harness->thmfiles (ACL2::w ACL2::state)))
                                (ACL2::get-functions-to-inline (ACL2::w ACL2::state)))
                               ACL2::state)))
    (ACL2::value `(ACL2::value-triple ,filename))))



(defmacro %finish (name)
  `(ACL2::table tactic-harness 'thmfiles
                (cons (list 'FINISH ',name)
                      (tactic.harness->thmfiles ACL2::world))))


(defun %ngoals-fn (wrld)
  (declare (xargs :mode :program))
  (len (tactic.skeleton->goals (tactic.harness->skeleton wrld))))

(defmacro %ngoals ()
  `(%ngoals-fn (acl2::w acl2::state)))


(defun break ()
  (declare (xargs :guard t))
  (acl2::cw "break has not been redefined!~%"))

(acl2::defttag break)
(acl2::progn!
 (acl2::set-raw-mode t)
 (acl2::defun break ()
   (acl2::cw "(break) was called.~%")
   (common-lisp::break)
   nil))

;; :q

;; (CCL::advise tactic.crewrite-all-tac
;;              (let* ((arglist CCL::arglist)
;;                     (control (fourth arglist))
;;                     (defs    (rw.control->defs control)))
;;                (ACL2::cw "$$$ crewrite-all-tac: defs are same? ~x0.~%"
;;                          (ACL2::eq defs (tactic.harness->defs (ACl2::w ACL2::*the-live-state*)))))
;;              :when :before)

;; (CCL::advise tactic.crewrite-all-compile
;;              (let* ((arglist CCL::arglist)
;;                     (control (nth 2 (tactic.skeleton->extras (car arglist))))
;;                     (defs    (rw.control->defs control)))
;;                (ACL2::cw "$$$ crewrite-all-compile: defs are same? ~x0.~%"
;;                          (ACL2::eq defs (tactic.harness->defs (ACl2::w ACL2::*the-live-state*)))))
;;              :when :before)

;; (CCL::advise rw.crewrite-clause-list-bldr
;;              (let* ((arglist CCL::arglist)
;;                     (control (fourth arglist))
;;                     (defs    (rw.control->defs control)))
;;                (ACL2::cw "$$$ crewrite-clause-list-bldr: defs are same? ~x0.~%"
;;                          (ACL2::eq defs (tactic.harness->defs (ACl2::w ACL2::*the-live-state*)))))
;;              :when :before)

;; (CCL::advise rw.crewrite-clause-bldr
;;              (let* ((arglist CCL::arglist)
;;                     (control (fourth arglist))
;;                     (defs    (rw.control->defs control)))
;;                (ACL2::cw "$$$ crewrite-clause-bldr: defs are same? ~x0.~%"
;;                          (ACL2::eq defs (tactic.harness->defs (ACl2::w ACL2::*the-live-state*)))))
;;              :when :before)

;; (CCL::advise rw.compile-ground-trace
;;              (let* ((arglist CCL::arglist)
;;                     (defs    (rw.trace->extras (car arglist))))
;;                (ACL2::cw "$$$ compile-ground-trace: defs are same? ~x0.~%"
;;                          (ACL2::eq defs (tactic.harness->defs (ACl2::w ACL2::*the-live-state*)))))
;;              :when :before)

;; (CCL::advise rw.try-ground-simplify
;;              (let* ((arglist CCL::arglist)
;;                     (control (fourth arglist))
;;                     (defs    (rw.control->defs control)))
;;                (ACL2::cw "$$$ rw.try-ground-simplify: defs are same? ~x0.~%"
;;                          (ACL2::eq defs (tactic.harness->defs (ACl2::w ACL2::*the-live-state*)))))
;;              :when :before)
