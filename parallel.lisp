; ACL2 Version 4.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2011  University of Texas at Austin

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the GNU General Public License as published by
; the Free Software Foundation; either version 2 of the License, or
; (at your option) any later version.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; GNU General Public License for more details.

; You should have received a copy of the GNU General Public License
; along with this program; if not, write to the Free Software
; Foundation, Inc., 675 Mass Ave, Cambridge, MA 02139, USA.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; We thank David L. Rager for contributing an initial version of this file.

(in-package "ACL2")

; Section: To Consider.  The following might be good to address as time
; permits.

;   Change the piece of work list to an array (perhaps result in a faster
;   library because of less garbage.

;   Make removing closures from the queue destructive, in particular with
;   regard to early termination.

;   Recycle locks, perhaps for example in wait-on-condition-variable-lockless.
;   See this same comment in parallel-raw.lisp.

;   Provide a way for the user to modify *core-count*, including inside the
;   ACL2 loop.  If we allow for changing *core-count*, then we need to think
;   about allowing for changing variables that depend on it, e.g.,
;   *unassigned-and-active-work-count-limit* (perhaps by changing them to
;   zero-ary functions).

;   Modify the coefficient (currently 2) in the definition of
;   *unassigned-and-active-work-count-limit*.  Evaluate such modifications with
;   testing, of course.

; End of Section "To Consider".

; Parallelism wart: cleanup the implementation and documentation of deflock.

; Parallelism wart: in the event that the just mentioned cleanup of deflock is
; not finished, insert the script that Kaufmann sent Rager in email.

(defdoc deflock

  ":Doc-Section ACL2::Parallel-programming

  define a wrapper macro that provides mutual exclusion in ACL2(p)~/

  This ~il[documentation] topic relates to the experimental extension of
  ACL2 supporting parallel evaluation and proof; ~pl[parallelism].

  ~bv[]
  Example Form:
  (deflock *my-lock*)

  General Form:
  (deflock *symbol*)
  ~ev[]
  where ~c[*symbol*] is a symbol whose first and last characters are both the
  character ~c[#\\*].

  A call of this macro generates a definition of another macro, named
  ~c[with-<modified-lock-symbol>], where ~c[<modified-lock-symbol>] is the
  given symbol with the leading and trailing ~c[*] characters removed.  This
  newly defined macro will guarantee mutually exclusive execution when called
  in the body of the raw Lisp definition of a function, as is typically the
  case for ~il[guard]-verified functions, for ~c[:]~ilc[program] mode
  functions, and for calls of macro ~ilc[top-level].
  (~l[guard-evaluation-table] for details of how raw Lisp code might not be
  invoked when guard-checking (~pl[set-guard-checking]) has value ~c[:none] or
  ~c[:all].)

  To see how mutual exclusion is guaranteed, consider the raw Lisp code
  generated for the macro, ~c[with-<modified-lock-symbol>], that is introduced
  by a call of ~c[deflock].  This code uses a lock (with the given ~c[*symbol*]
  as its name), which guarantees that for any two forms that are each in the
  scope of a call of ~c[with-<modified-lock-symbol>], the forms do not execute
  concurrently.

  Note that a call of ~c[deflock] expands into the application of ~c[progn] to
  two events, as illustrated below.
  ~bv[]
  ACL2 !>:trans1 (deflock *my-cw-lock*)
   (PROGN (TABLE LOCK-TABLE '*MY-CW-LOCK* T)
          (DEFMACRO WITH-MY-CW-LOCK (&REST ARGS)
                    (LIST* 'WITH-LOCK '*MY-CW-LOCK* ARGS)))
  ACL2 !>
  ~ev[]
  Thus, ~c[deflock] forms are legal embedded event forms
  (~pl[embedded-event-form]) for ~il[books] as well as ~ilc[encapsulate] and
  ~ilc[progn] ~il[events].

  The following log shows a lock in action.  Recall that locks work as expected
  in ~il[guard]-verified and ~c[:]~ilc[program] mode functions; they do not,
  however, work in ~c[:]~ilc[logic] mode functions that have not been
  guard-verified, as illustrated below.

  ~bv[]
  ACL2 !>(deflock *my-cw-lock*)
  [[.. output omitted ..]]
   WITH-MY-CW-LOCK
  ACL2 !>(defun foo (n)
           (declare (xargs :guard (natp n) :verify-guards nil))
           (plet ((x1 (with-my-cw-lock (cw \"~~x0\" (make-list n))))
                  (x2 (with-my-cw-lock (cw \"~~x0\" (make-list n)))))
                 (and (null x1) (null x2))))
  [[.. output omitted ..]]
   FOO
  ACL2 !>(foo 20)
  (NIL NIL NIL NIL( NIL NIL NIL NIL NIL NILNIL  NIL NILNIL  NIL NILNIL 
       NIL NILNIL NIL  NIL NILNIL  NIL NIL
  NIL      NILNIL  NIL NILNIL )
  NIL NIL NIL NIL NIL NIL NIL NIL)
  T
  ACL2 !>(verify-guards foo)
  [[.. output omitted ..]]
   FOO
  ACL2 !>(foo 20)
  (NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
       NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL)
  (NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL
       NIL NIL NIL NIL NIL NIL NIL NIL NIL NIL)
  T
  ACL2 !>
  ~ev[]~/~/")

(defdoc compiling-acl2p

; Keep this documentation in sync with comments above the error in
; acl2-init.lisp about it being "illegal to build the parallel
; version", and also with the error message about supported Lisps in
; set-parallel-execution-fn.

  ":Doc-Section ACL2::Parallelism

  compiling ACL2(p)~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].  ~l[parallel] and
  ~pl[parallelism-tutorial] for an introduction to parallel programming in
  ACL2.

  You can build an experimental version of ACL2 that supports parallel
  execution in the following host Common Lisp implementations:
  ~bq[]
  * CCL (OpenMCL)

  * Lispworks 6.0

  * SBCL with threads (feature ~c[:sb-thread])~eq[]

  The command below will compile ACL2 to support parallel execution, including
  parallel execution during proofs.  Any non-empty string may be used in place
  of ~c[t], and the value of ~c[LISP] (shown here as ~c[ccl]) is any Lisp
  executable on which one can build ACL2(p) (~pl[parallelism]).
  ~bv[]
  make ACL2_PAR=t LISP=ccl
  ~ev[]

  So for example, to make an executable image and also documentation (which
  will appear in subdirectories ~c[doc/EMACS] and ~c[doc/HTML]), using the Lisp
  executable ~c[ccl]:
  ~bv[]
  make large DOC ACL2_PAR=t LISP=ccl
  ~ev[]~/~/")

(defdoc parallel

; Just in case someone types :doc parallel.

  ":Doc-Section Miscellaneous

  evaluating forms in parallel~/

  ~l[parallelism].~/~/")

(defdoc parallelism-build

  ":Doc-Section Miscellaneous

  building an ACL2 executable with parallel execution enabled~/

  ~l[compiling-acl2p].~/~/")

(defun set-parallel-execution-fn (val ctx state)
  (declare (xargs :guard (member-eq val '(t nil :bogus-parallelism-ok))))
  (cond
   ((eq (f-get-global 'parallel-execution-enabled state)
        val)
    (pprogn (observation ctx
                         "No change in enabling of parallel execution.")
            (value nil)))
   (t
    #-acl2-par
    (er soft ctx
        "Parallelism can only be enabled in CCL, threaded SBCL, or Lispworks. ~
         ~ Additionally, the feature :ACL2-PAR must be set when compiling ~
         ACL2 (for example, by using `make' with argument `ACL2_PAR=t').  ~
         Either the current Lisp is neither CCL nor threaded SBCL nor ~
         Lispworks, or this feature is missing.  Consequently, parallelism ~
         will remain disabled.  Note that you can submit parallelism ~
         primitives at the top level when parallel execution is disabled, ~
         although they will not result in any parallel execution.~%")
    #+acl2-par
    (let ((observation-string
           (case val
             ((nil)
              "Disabling parallel execution.  Parallelism primitives may ~
               still be used, but during execution they will degrade to ~
               their serial equivalents.")
             ((t)
              "Parallel execution is enabled, but parallelism primitives may ~
               only be called within function definitions or macro top-level, ~
               not at the top level of the ACL2 read-eval-print loop.  See ~
               :DOC parallelism-at-the-top-level.")
             (otherwise ; :bogus-parallelism-ok
              "Parallel execution is enabled.  Parallelism primitives may be ~
               called directly in the top-level loop, but without use of the ~
               macro top-level, they will execute serially.  See :DOC ~
               parallelism-at-the-top-level."))))
      (pprogn
       (f-put-global 'parallel-execution-enabled val state)
       (observation ctx observation-string)
       (value val))))))

(defmacro set-parallel-execution (value)

; Parallelism blemish: cause an error if the user tries to go into a state
; where waterfall-parallelism is enabled but parallel-execution is disabled.

  ":Doc-Section switches-parameters-and-modes

  enabling parallel execution for four of the parallelism primitives~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].  ~l[parallel] and
  ~pl[parallelism-tutorial] for an introduction to parallel execution in ACL2.

  ~bv[]
  General Forms:
  (set-parallel-execution nil) ; default for images not built for parallelism
  (set-parallel-execution t)   ; default for images built for parallelism
  (set-parallel-execution :bogus-parallelism-ok)
  ~ev[]
  ~/

  ~c[Set-parallel-execution] takes an argument that specifies the enabling or
  disabling of ~il[parallel] execution for the primitives ~ilc[pand],
  ~ilc[por], ~ilc[plet], and ~ilc[pargs] (but not ~ilc[spec-mv-let], whose
  parallel execution remains enabled).  However, without using
  ~ilc[top-level], calls of parallelism primitives made explicitly in the ACL2
  top-level loop, as opposed to inside function bodies, will never cause
  parallel execution; ~pl[parallelism-at-the-top-level].  Parallel execution
  is determined by the value of the argument to ~c[set-parallel-execution], as
  follows.

  Value ~c[t]:~nl[]
  All parallelism primitives used in bodies of function definitions are given
  the opportunity to execute in parallel.  However, the use of parallelism
  primitives directly in the ACL2 top-level loop causes an error.

  Value ~c[:bogus-parallelism-ok]:~nl[]
  Parallel execution is enabled, as for value ~c[t].  However, the use of
  parallelism primitives directly in the ACL2 top-level loop does not cause an
  error, but rather, simply results in serial execution for these primitives.

  Value ~c[nil]:~nl[]
  All parallelism primitives degrade to their serial equivalents, including
  their calls made directly in the ACL2 top-level loop.  Thus, uses of
  parallelism primitives do not in themselves cause errors.~/

  :cited-by parallel-programming"

  (declare (xargs :guard (member-equal value
                                       '(t 't nil 'nil
                                           :bogus-parallelism-ok
                                           ':bogus-parallelism-ok))))
  `(let ((val ,value)
         (ctx 'set-parallel-execution))
     (set-parallel-execution-fn
      (cond ((consp val) (cadr val))
            (t val))
      ctx
      state)))

(defdoc parallel-execution

  ":Doc-Section Parallel-programming

  for ACL2(p): configure parallel execution~/

  ~l[set-parallel-execution] for how to configure parallel execution for calls
  of ~ilc[plet], ~ilc[pargs], ~ilc[pand], ~ilc[por] (but not
  ~ilc[spec-mv-let]).~/~/")

(defun waterfall-printing-value-for-parallelism-value (value)

; Warning: We assume the the value of this function on input nil is :full.  If
; that changes, then we will need to replace the definition of
; waterfall-printing-full in front of the defproxy event below for
; waterfall-printing, as well as the corresponding defattach event in
; boot-strap-pass-2.lisp.

  (declare (xargs :guard (member-eq value *waterfall-parallelism-values*)))
  (cond ((eq value nil)
         :full)
        ((eq value :full)
         :very-limited)
        ((eq value :top-level)
         :very-limited)
        ((eq value :resource-based)
         :very-limited)
        ((eq value :resource-and-timing-based)
         :very-limited)
        (t 
         (assert$ (eq value :pseudo-parallel)
                  :very-limited))))

; Parallelism wart: figure out if :bdd hints are supported.  Given the call of
; error-in-parallelism-mode@par in waterfall-step, it seems that they might not
; be; yet, regressions may have passed with them.  One possible outcome: If
; books/bdd/ tests fail, you might just modify translate-bdd-hint to cause a
; nice error if watefall parallelism is enabled, and also mention that (once
; again) in :doc unsupported-waterfall-parallelism-features.  Note that
; bdd-clause might be the function that actually performs the bdd hint, and
; that bdd-clause doesn't return state.  So, aside from the place in
; waterfall-step, bdd hints might be fine.

(defdoc unsupported-waterfall-parallelism-features

; For a discussion of the wormhole issue referenced in the :doc string below,
; see waterfall-print-clause-id@par.

; Parallelism no-fix: the problem below related to interrupts is potentially
; somewhat serious, but probably quite rare.  Moreover, it seems potentially
; quite difficult to fix, as it would likely involve multi-threaded Lisp issues
; as well as acl2-unwind-protect issues.

  ":Doc-Section ACL2::Parallel-proof

  proof features not supported with waterfall-parallelism enabled~/

  For a general introduction to ACL2(p), an experimental extension of ACL2 that
  supports parallel execution and proof, ~pl[parallelism].  Please note that
  although this extension is usable and, we hope, robust in its behavior, there
  are still known issues to address beyond those listed explicitly below.
  While we expect ACL2(p) to perform correctly, it may never have the same
  level of attention to correctness as is given to ACL2; ~pl[parallelism],
  specifically the ``IMPORTANT NOTE'' there.

  Below we list proof features of ACL2 that are not yet supported when parallel
  execution is enabled for the primary ACL2 proof process, generally known as
  ``the waterfall'', typically by calling ~ilc[set-waterfall-parallelism].

  Please note that this topic is limited to the case that such waterfall
  parallelism is enabled.  We believe that all ACL2 proof procedures are
  supported when waterfall parallelism is disabled, even in executables that
  support parallelism (~pl[compiling-acl2p]).

  Without a trust tag (~pl[defttag]): We support ~il[clause-processor]s,
  ~il[computed-hints], and ~il[custom-keyword-hints] that do not modify
  ~il[state], but we do not permit ~il[override-hints], regardless of whether
  they modify state.  With a trust tag, the user can use ~il[clause-processor]s
  that modify state and can also use ~il[override-hints]
  (~pl[set-waterfall-parallelism-hacks-enabled] for a convenient mechanism for
  adding a trust tag).  ~l[error-triples-and-parallelism] for a discussion of
  how to avoid modifying state in such situations.  Regardless of whether a
  trust tag is active: We do not support checkers of ~il[custom-keyword-hints]
  to be anything but the default checker.

  GNU Make versions 3.81 and 3.82 formerly caused a lot of problems (version
  3.80 somewhat less so), at least on Linux, when certifying books with ACL2
  built on a host Lisp of CCL using ~c[make] (~pl[book-makefiles]).  CCL was
  updated around March 23, 2011 to fix this problem, so if you get
  segfaults (for example) with CCL, try updating your CCL installation.

  The standard process for book certification will not use
  ~il[waterfall-parallelism], which is disabled by default (even when
  ~il[compiling-acl2p] by using the ~c[ACL2_PAR] flag).  ~l[book-makefiles],
  which explains that ~il[acl2-customization] files are ignored during that
  process unless specified explicitly on the command line or in the
  environment.

  Proof output can contain repeated printing of the same subgoal name.

  ~il[Gag-mode] isn't officially supported, although it has proved helpful to
  use ACL2(p) in conjunction with ~c[(set-gag-mode t)].  This being said,
  ACL2(p) also prints key checkpoints (for example
  ~pl[introduction-to-key-checkpoints]), but with a notion of ``key
  checkpoint'' that does not take into account whether the goal is later proved
  by induction.

  The ~c[:]~ilc[brr] utility is not supported.

  Time limits (~pl[with-prover-time-limit]) aren't supported.

  The timing information printed at the end of a proof attempt may be somewhat
  inaccurate.  Consider using ~ilc[time$] to obtain timing information.

  The use of ~ilc[wormhole]s is not recommended, as there may be race
  conditions.

  Output specific to ~c[:OR] ~il[hints] is disabled.

  Proof trees are likely not to work as originally designed.

  The use of ~ilc[set-inhibit-output-lst] may not fully inhibit proof output.

  Interrupting a proof attempt is not yet properly supported.  At a minimum,
  interrupts are trickier with waterfall parallelism enabled.  For one, the
  user typically needs to issue the interrupt twice before the proof attempt is
  actually interrupted.  Additionally, on rare occasions the theorem is
  registered as proved, even though the prover did not finish the proof.  If
  this occurs, issue a ~c[:u] (~pl[ubt]) and you will likely be at a stable
  state.

  Also with regards to interrupting a proof attempt, sometimes the user may
  need to issue a ~c[:q] and ~c[lp] to reset properly the parallelism
  implementation to a stable state.  The primary symptom that the user is
  experiencing this issue is that threads will continue to compute in the
  background, even though there should be no proof attempt in progress.  The
  user can observe this symptom by examining the CPU utilization of their ACL2
  process, for example on Linux/Unix with the shell process ~c[top].  Lisp
  usage greater than a few percent is indicative of this problem.

  Because of how ACL2 ~il[arrays] are designed, the user may find that, in
  practice, ACL2 arrays work (but perhaps with some ~il[slow-array-warning]
  messages).  However, we are aware of race conditions that can cause
  problems.

  Instead of dynamically monitoring rewrites, ~il[dmr] instead dynamically
  outputs information helpful for debugging the performance of proof
  parallelism.  The instructions concerning how to see this debugging
  information are the same as the instructions for enabling ~il[dmr]
  mode.

  If you are working with LispWorks 6.0 or 6.0.1, then you may see messages
  about misaligned conses.  The state of the system may be corrupted after such
  a message has been printed.  This LispWorks bug is fixed in LispWorks 6.1.

  The waterfall parallelism mode ~c[:resource-and-timing-based] is not fully
  supported when the host Lisp is other than CCL.  It may work, but we have not
  attempted to address a potential race condition.

  (Comment for ACL2(h) users; ~pl[hons-and-memoization].)  Memoization may not
  work as intended when executing in parallel (including the waterfall).  In an
  effort to be helpful to the user, the functions automatically memoized by
  ACL2(h) are unmemoized when setting waterfall parallelism to anything but
  ~c[nil].  Those exact functions are again memoized once waterfall parallelism
  is disabled.  Note that no functions other than these exact functions are
  treated in this way, so all user-defined memoizations must be handled by the
  user.~/~/")

(defdoc unsupported-parallelism-features

  ":Doc-Section ACL2::Parallelism

  ACL2 features not supported in ACL2(p)~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].  ~l[parallel] and
  ~pl[parallelism-tutorial] for an introduction to parallel execution in ACL2.

  For proof features of ACL2 that are not yet supported when parallel
  execution is enabled for the primary ACL2 proof process, generally known as
  ``the waterfall'', ~pl[unsupported-waterfall-parallelism-features].

  Please note that this topic discusses ACL2 features that are disabled when
  using ACL2(p) (~pl[compiling-acl2p]).  These features are disabled
  regardless of whether waterfall parallelism is enabled.

  Calls of ~ilc[observation-cw] simply convert to calls of ~ilc[cw], so
  suppressing ~ilc[observation]s (~pl[set-inhibit-output-lst]) will not
  suppress these messages.

  Memoization is not supported when executing in parallel.
  ~l[Unsupported-waterfall-parallelism-features] for memoization details
  related to waterfall parallelism.~/~/")

(defdoc waterfall-printing

  ":Doc-Section Parallel-proof

  for ACL2(p): configuring the printing within the parallelized waterfall~/

  ~l[set-waterfall-printing].~/~/")

(defdoc waterfall-parallelism

  ":Doc-Section Parallel-proof

  for ACL2(p): configuring the parallel execution of the waterfall~/

  ~l[set-waterfall-parallelism].~/~/")

(defun print-set-waterfall-parallelism-notice (val print-val state)

; Warning: This function should only be called inside the ACL2 loop, because of
; the calls of observation-cw.

  (declare (xargs :guard (and (member-eq val *waterfall-parallelism-values*)
                              (keywordp print-val))))
  (let ((str
         (case val
           ((nil)
            "Disabling parallel execution of the waterfall.")
           (:full
            "Parallelizing the proof of every subgoal.")
           (:top-level
            "Parallelizing the proof of top-level subgoals only.")
           (:pseudo-parallel
            "Running the version of the waterfall prepared for parallel ~
             execution (stateless).  However, we will execute this version of ~
             the waterfall serially.")
           (:resource-and-timing-based
            "Parallelizing the proof of every subgoal that was determined to ~
             take a non-trivial amount of time in a previous proof attempt.")
           (otherwise ; :resource-based
            "Parallelizing the proof of every subgoal, as long as CPU core ~
             resources are available."))))
    (observation nil
                 "~@0  Setting waterfall-parallelism to ~s1.  Setting ~
                  waterfall-printing to ~s2 (see :DOC set-waterfall-printing)."
                 str
                 (symbol-name val)
                 (symbol-name print-val))))

(defun check-for-no-override-hints (ctx state)

; Although this macro is intended for #+acl2-par, we need it unconditionally
; because it is called in set-waterfall-parallelism, which might be called
; outside ACL2(p); see the note about a call of observation in
; set-waterfall-parallelism-fn.

  (let ((wrld (w state)))
    (cond
     ((and (not (cdr (assoc-eq 'hacks-enabled
                               (table-alist 'waterfall-parallelism-table
                                            wrld))))
           (cdr (assoc-eq :override (table-alist 'default-hints-table
                                                 wrld))))
      (er soft ctx

; Override hints must be removed because set-waterfall-parallelism performs a
; defattach, which spawns some proof effort.  If there are override-hints
; available for use during this proof, apply-override-hints will see them and
; attempt to use them.  Since override-hints are not permitted without enabling
; waterfall-parallelism-hacks, in this case, we must cause an error.
            
          "Before changing the status of waterfall-parallelism, either (1) ~
           override hints must be removed from the default-hints-table or (2) ~
           waterfall-parallelism hacks must be enabled.  (1) can be achieved ~
           by calling ~x0.  (2) can be achived by calling ~x1."
          '(set-override-hints nil)
          '(set-waterfall-parallelism-hacks-enabled t)))
     (t (value nil)))))

(defun set-waterfall-parallelism-fn (val ctx state)
  (cond ((member-eq val *waterfall-parallelism-values*)
         #+acl2-par
         (cond 
          ((null (f-get-global 'parallel-execution-enabled state))
           (er soft ctx 
               "Parallel execution must be enabled before enabling waterfall ~
                parallelism.  See :DOC set-parallel-execution"))
          (t
           (pprogn #+(and hons (not acl2-loop-only))
                   (progn
                     (cond ((null val)
                            (observation 'set-waterfall-parallelism
                                         "Unmemoizing the functions that are ~
                                          memoized by default as part of ~
                                          ACL2(h) (see :DOC ~
                                          unsupported-waterfall-parallelism-features).")
                            (hons-init-hook-memoizations))
                           (t 
                            (observation 'set-waterfall-parallelism
                                         "Memoizing the functions that are ~
                                        memoized by default as part of ~
                                        ACL2(h) (see :DOC ~
                                        unsupported-waterfall-parallelism-features).")
                            (hons-init-hook-unmemoizations)))
                     state)
                   (f-put-global 'waterfall-parallelism val state)
                   (value val))))
         #-acl2-par

; Once upon a time we issued an error here instead of an observation.  In
; response to feedback from Dave Greve, we have changed it to an observation so
; that users can call set-waterfall-parallelism inside books (presumably via
; make-event) without causing their certification to stop when using #-acl2-par
; builds of ACL2.

         (pprogn
          (observation ctx
      
; We make this an observation instead of a warning, because it's probably
; pretty obvious to the user whether they're using an image that was built with
; the acl2-par feature.
                     
                       "Parallelism can only be enabled in CCL, threaded ~
                        SBCL, or Lispworks.  Additionally, the feature ~
                        :ACL2-PAR must be set when compiling ACL2 (for ~
                        example, by using `make' with argument `ACL2_PAR=t'). ~
                        ~ Either the current Lisp is neither CCL nor threaded ~
                        SBCL nor Lispworks, or this feature is missing.  ~
                        Consequently, this attempt to set ~
                        waterfall-parallelism to ~x0 will be ignored.~%~%"
                       val)
          (value :ignored)))
        (t (er soft ctx
               "Illegal value for set-waterfall-parallelism: ~x0.  The legal ~
                values are ~&1."
               val *waterfall-parallelism-values*))))

; Parallelism blemish: make a macro via deflast called
; with-waterfall-parallelism that enables waterfall parallelism for a given
; form, in particular an event form like calls of defun and defthm.  It's low
; priority, since it can easily be added as a book later -- though maybe it
; would be nice to have this as an event constructor, like with-output.  But
; while doing proofs with ACL2(hp), Rager would have found this convenient.

(defmacro set-waterfall-parallelism (val)

  ":Doc-Section switches-parameters-and-modes

  for ACL2(p): configuring the parallel execution of the waterfall~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  General Forms:
  (set-waterfall-parallelism nil)        ; never parallelize (serial execution)
  (set-waterfall-parallelism :full)      ; always parallelize
                                         ;   (recommended setting)
  (set-waterfall-parallelism :top-level) ; parallelize top-level subgoals
  (set-waterfall-parallelism             ; parallelize if sufficient resources
    :resource-based)
  (set-waterfall-parallelism             ; parallelize if sufficient resources
    :resource-and-timing-based           ;   and suggested by prior attempts
  (set-waterfall-parallelism             ; never parallelize but use parallel
    :pseudo-parallel)                    ;   code base (a debug mode)
  ~ev[]
  ~/

  ~c[Set-waterfall-parallelism] accepts an argument that specifies the enabling
  or disabling of the ~il[parallel] execution of ACL2's main proof process, the
  waterfall.

  It also sets state global ~c[waterfall-printing] to an appropriate value.
  ~l[set-waterfall-printing].

  Note that not all ACL2 features are supported when waterfall-parallelism is
  set to non-nil (~pl[unsupported-waterfall-parallelism-features]).

  ~c[:Full] waterfall parallelism typically achieves the best performance in
  ACL2(p), so ~c[:full] is the recommended setting.

  A value of ~c[nil] indicates that ACL2(p) should never prove subgoals in
  parallel.

  A value of ~c[:full] indicates that ACL2(p) should always prove independent
  subgoals in parallel.

  A value of ~c[:top-level] indicates that ACL2(p) should prove each of the
  top-level subgoals in parallel but otherwise prove subgoals in a serial
  manner.  This mode is useful when the user knows that there are enough
  top-level subgoals, many of which take a non-trivial amount of time to be
  proved, such that proving them in parallel will result in a useful reduction
  in overall proof time.

  A value of ~c[:resource-based] indicates that ACL2(p) should use its built-in
  heuristics to determine whether CPU core resources are available for parallel
  execution.  Note that ACL2(p) does not hook into the operating system to
  determine the workload on the machine.  ACL2(p) works off the assumption that
  it is the only process using significant CPU resources, and it optimizes the
  amount of parallelism based on the number of CPU cores in the system.  (Note
  that ACL2(p) knows how to obtain the number of CPU cores from the operating
  system in CCL, but that, in SBCL and in Lispworks, a constant is used
  instead).

  During the first proof attempt of a given conjecture, a value of
  ~c[:resource-and-timing-based] results in the same behavior as with
  ~c[:resource-based].  However, on subsequent proof attempts, the time it took
  to prove each subgoal will be considered when deciding whether to parallelize
  execution.  If a particular theorem's proof is already achieving satisfactory
  speedup via ~c[:resource-based] parallelism, there is no reason to try this
  setting.  However, if the user wishes to experiment, the
  ~c[:resource-and-timing-based] setting may improve performance.  Note that
  since the initial run does not have the subgoal proof times available, this
  mode will never be better than the ~c[:resource-based] setting for
  non-interactive theorem proving.

  A value of ~c[:pseudo-parallel] results in using the parallel waterfall code,
  but with serial execution.  This setting is useful for debugging the code
  base that supports parallel execution of the waterfall.  For example, you may
  wish to use this mode if you are an ``ACL2 Hacker'' who would like to see
  comprehensible output from tracing (~pl[trace$]) the ~c[@par] versions of the
  waterfall functions.

  Note that this form cannot be used at the top level of a book, or of a
  ~ilc[progn] or ~ilc[encapsulate] event.  Here is a workaround for use in such
  contexts; of course, you may replace ~c[:full] with any other legal argument
  for ~c[set-waterfall-parallelism].  Note that this form will not affect
  waterfall-parallelism when including a certified book that contains it.
  ~bv[]
  (make-event (er-progn (set-waterfall-parallelism :full)
                        (value '(value-triple nil))))
  ~ev[]
  (For more about event contexts and the use of ~c[make-event],
  ~pl[make-event], in particular the section ``Restriction to Event
  Contexts.'')

  The following form has the effect described above, except that it will affect
  waterfall-parallelism even when including a certified book that contains it.
  ~bv[]
  (make-event (er-progn (set-waterfall-parallelism :full)
                        (value '(value-triple nil)))
              :check-expansion t)
  ~ev[]
  ~/

  :cited-by parallel-proof"

  `(let* ((val ,val)
          (ctx 'set-waterfall-parallelism))
     (er-progn
      (check-for-no-override-hints ctx state)
      (er-let* ((val (set-waterfall-parallelism-fn val ctx state)))
               (cond ((eq val :ignored)
                      (value val))
                     (t (let ((print-val
                               (waterfall-printing-value-for-parallelism-value
                                val)))
                          (pprogn
                           (print-set-waterfall-parallelism-notice
                            val print-val state)
                           (er-progn
                            (set-waterfall-printing-fn print-val ctx state)
                            (value (list val print-val)))))))))))

(defun set-waterfall-printing-fn (val ctx state)
  (cond ((member-eq val *waterfall-printing-values*)
         #+acl2-par
         (pprogn (f-put-global 'waterfall-printing val state)
                 (value val))
         #-acl2-par

; See note about making this an observation instead of an error inside
; set-waterfall-parallelism.

         (pprogn (observation ctx
                              "Customizing waterfall printing only makes ~
                               sense in the #+acl2-par builds of ACL2.  ~
                               Consequently, this attempt to set ~
                               waterfall-printing to ~x0 will be ignored.~%~%"
                              val)
                 (value :invisible)))
        (t (er soft ctx
               "Illegal value for set-waterfall-printing: ~x0.  The legal ~
                values are ~&1."
               val *waterfall-printing-values*))))
               
(defmacro set-waterfall-printing (val)

  ":Doc-Section switches-parameters-and-modes

  for ACL2(p): configuring the printing that occurs within the parallelized waterfall~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  General Forms:
  (set-waterfall-printing :full)    ; print everything
  (set-waterfall-printing :limited) ; print a subset that's thought to be useful
  (set-waterfall-printing :very-limited) ; print an even smaller subset
  ~ev[]
  ~/

  ~c[Set-waterfall-printing] takes an argument that indicates how much
  printing should occur when executing ACL2 with the parallelized version of the
  waterfall.  It only affects the printing that occurs when parallelism mode is
  enabled for the waterfall (~pl[set-waterfall-parallelism]).

  A value of ~c[:full] is intended to print the same output as in serial mode.
  This output will be interleaved unless the waterfall-parallelism mode is one
  of ~c[nil] or ~c[:pseudo-parallel].

  A value of ~c[:limited] omits most of the output that occurs in the serial
  version of the waterfall.  Instead, the proof attempt prints proof
  checkpoints, similar to (but still distinct from) gag-mode
  (~pl[set-gag-mode]).  The value of ~c[:limited] also prints messages that
  indicate which subgoal is currently being proved, along with the wall-clock
  time elapsed since the theorem began its proof; and if state global
  ~c['waterfall-printing-when-finished] has a non-~c[nil] value, then such a
  message will also be printed at the completion of each subgoal.  The function
  ~c[print-clause-id-okp] may receive an attachment to limit such printing;
  ~pl[set-print-clause-ids].  Naturally, these subgoal numbers can appear out
  of order, because the subgoals can be proved in parallel.

  A value of ~c[:very-limited] is treated the same as ~c[:limited], except that
  instead of printing subgoal numbers, the proof attempt prints a
  period (`~c[.]') each time it starts a new subgoal.

  Note that this form cannot be used at the top level of a book, or of a
  ~ilc[progn] or ~ilc[encapsulate] event.  Here is a workaround for use in such
  contexts; of course, you may replace ~c[:very-limited] with any other legal
  argument for ~c[set-waterfall-printing].
  ~bv[]
  (make-event (er-progn (set-waterfall-printing :very-limited)
                        (value '(value-triple nil))))
  ~ev[]
  (For more about event contexts and the use of ~c[make-event],
  ~pl[make-event], in particular the section ``Restriction to Event
  Contexts.'')

  The following form has the effect described above, except that it will affect
  waterfall-printing even when including a certified book that contains it.
  ~bv[]
  (make-event (er-progn (set-waterfall-printing :very-limited)
                        (value '(value-triple nil)))
              :check-expansion t)
  ~ev[]

  Note that ~c[set-waterfall-printing] is automatically called by
  ~ilc[set-waterfall-parallelism].

  To enable the printing of information when a subgoal is finished, assign a
  non-~c[nil] value to global ~c[waterfall-printing-when-finished].  This can
  be accomplished by entering the following at the top level:
  ~bv[]
  (f-put-global 'waterfall-printing-when-finished t state)
  ~ev[]
  ~/

  :cited-by parallel-proof"

  `(set-waterfall-printing-fn ,val 'set-waterfall-printing state))

(defun set-waterfall-parallelism-hacks-enabled-guard (wrld)
  (or (ttag wrld)
      (er hard nil
          "Using waterfall parallelism hacks requires an active trust-tag. ~
           Consider using (set-waterfall-parallelism-hacks-enabled! t).  See ~
           :DOC set-waterfall-parallelism-hacks-enabled for~ more~ ~
           information.")))

(table waterfall-parallelism-table
       nil nil :guard (set-waterfall-parallelism-hacks-enabled-guard world))

(defmacro set-waterfall-parallelism-hacks-enabled (val)

; One might consider using a state global to implement
; set-waterfall-parallelism-hacks-enabled.  But as David Rager points out, this
; macro can change whether or not a proof completes.  So, we want this macro
; tied into the undoing mechanism; hence we use a table event.

  ":Doc-Section switches-parameters-and-modes

  enable waterfall-parallelism hacks~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  General Forms:
  (set-waterfall-parallelism-hacks-enabled t)
  (set-waterfall-parallelism-hacks-enabled nil)
  ~ev[]~/

  Some features (e.g., ~il[override-hints] and ~il[clause-processor]s) of
  serial ACL2 are by default not available in ACL2(p) with waterfall
  parallelism enabled, because they offer a mechanism to modify ~il[state] that
  is unsound.  To allow or (once again) disallow the use the these features in
  ACL2(p), call ~c[set-waterfall-parallelism-hacks-enabled] with argument ~c[t]
  or ~c[nil], respectively.

  ~c[Set-waterfall-parallelism-hacks-enabled] requires the use of a trust tag
  (~pl[defttag]).  One can call ~ilc[set-waterfall-parallelism-hacks-enabled!]
  instead, which will automatically install a trust tag named
  ~c[:waterfall-parallelism-hacks].

  ~l[error-triples-and-parallelism] for further related discussion.~/
  :cited-by parallel-proof"

  (declare (xargs :guard (or (equal val t) (null val))))
  `(table waterfall-parallelism-table 'hacks-enabled ,val))

(defmacro set-waterfall-parallelism-hacks-enabled! (val)

  ":Doc-Section switches-parameters-and-modes

  for ACL2(p): enabling waterfall parallelism hacks~/

  ~l[set-waterfall-parallelism-hacks-enabled].~/~/
  :cited-by parallel-proof"

  `(encapsulate
    ()

; Parallelism blemish: the following installation of ttag
; :waterfall-parallelism-hacks should probably be conditionalized upon val
; being equal to t.  Furthermore, perhaps the installation should also be
; conditionalized upon the non-existence of a prior ttag.

    (defttag :waterfall-parallelism-hacks)
    (set-waterfall-parallelism-hacks-enabled ,val)))

(defdoc parallelism-at-the-top-level

  ":Doc-Section Parallel-programming

  parallel execution in the ACL2 top-level loop~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  Calls of parallelism primitives made explicitly in the ACL2 top-level loop,
  as opposed to inside function bodies, will never cause parallel execution.
  Such calls will either execute with serial execution or will cause an error;
  ~pl[set-parallel-execution].  For a way around this restriction,
  ~pl[top-level].~/

  Consider for example the following call of ~ilc[pargs] in the ACL2
  top-level loop.  Instead of executing ~c[pargs], ACL2 macroexpands away this
  call, leaving us with serial execution of the arguments to the ~ilc[cons]
  call, or else causes an error (~pl[set-parallel-execution]).  If there is no
  error, then
  ~bv[]
  (pargs (cons (expensive-fn-1 4) (expensive-fn-2 5)))
  ~ev[]
  expands into:
  ~bv[]
  (cons (expensive-fn-1 4) (expensive-fn-2 5))
  ~ev[]

  One trivial way to enable parallel execution of a form is to surround it
  with a call to macro ~il[top-level].  Consider the following example.
  ~bv[]
  (top-level (pargs (cons (expensive-fn-1 4) (expensive-fn-2 5))))
  ~ev[]
  Then in an executable image that supports parallel execution ~-[]
  ~pl[compiling-acl2p] for instructions on how to build such an executable
  ~-[] ~c[(expensive-fn-1 4)] and ~c[(expensive-fn-2 5)] can evaluate in 
  parallel.

  A second way to enable parallel execution of a form is to place it 
  inside a function body.  For example, consider the following definition.
  ~bv[]
  (defun foo (x y)
    (pargs (cons (expensive-fn-1 x) (expensive-fn-2 y))))
  ~ev[]
  Then in an executable image that supports parallel execution, submission of
  the form ~c[(foo 4 5)] can cause parallel execution of 
  ~c[(expensive-fn-1 4)] and ~c[(expensive-fn-2 5)].

  Note that ~il[guard]s need not be verified in order to obtain ~il[parallel]
  execution.  The only restrictions on parallel execution are to use an
  executable supporting it, to avoid calling parallelism primitives directly in
  the top-level loop, to have sufficient resources (especially, threads)
  available, and to avoid explicitly disabling parallel execution
  (~pl[set-parallel-execution]).~/")

(defdoc parallelism-tutorial
  ":Doc-Section Parallel-programming

  a tutorial on how to use the parallelism library.~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  In this topic we introduce the ACL2 parallelism primitives using the example
  of a doubly-recursive Fibonacci function, whose basic definition is as
  follows.  ~l[parallelism] for a very high-level summary of the parallelism
  capability described here, and ~pl[compiling-acl2p] for how to build an
  executable image that supports parallel execution.  Here, we assume that
  such an executable is being used.~/

  ~b[Serial Fibonacci]

  ~bv[]
  (defun fib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (+ (fib (- x 1)) (fib (- x 2))))))
  ~ev[]

  ~b[Introducing] ~ilc[Pargs]

  A simple way to introduce parallelism into this function definition is to
  wrap the addition expression with a call of ~ilc[pargs], and the arguments to
  the addition will be computed in parallel whenever resources are available.
  As a result, we end up with a very similar and thus intuitive function
  definition.  Note that we replaced ~ilc[+] by ~ilc[binary-+], since
  ~ilc[pargs] expects a function call, not a macro call.
  ~bv[]
  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (pargs (binary-+ (pfib (- x 1))
                              (pfib (- x 2)))))))
  ~ev[]

  ~b[Introducing the Granularity Problem]

  After you submit the above two versions of the Fibonacci function, test them
  with the following forms.
  ~bv[]
  (time$ (fib 10))
  (time$ (pfib 10))
  ~ev[]
  Now increase the argument by increments of 5 to 10 until you find your
  curiosity satisfied or your patience wearing thin.  You can interrupt
  evaluation if necessary and return to the ACL2 loop.  You will immediately
  notice that you have not increased execution speed, at least not by much, by
  introducing parallelism.

  First, consider the computation of ~c[(pfib 4)].  Assuming resources are
  available, ~c[(pfib 4)] will create a thread for computing ~c[(pfib 3)] and
  another thread for ~c[(pfib 2)].  It is easy to imagine that setting up each
  thread takes much longer than the entire computation of ~c[(fib 4)].

  Second, we must realize that if we have two threads available for computing
  ~c[(fib 10)], then the evaluation of ~c[(fib 8)] will probably complete
  before the evaluation of ~c[(fib 9)].  Once ~c[(fib 8)] finishes, parallelism
  resources will become available for the next recursive call made on behalf of
  ~c[(fib 9)].  If for example that call is ~c[(fib 3)], we will waste a lot of
  cycles just handing work to the thread that does this relatively small
  computation.  We need a way to ensure that parallelism resources are only
  used on problems of a \"large\" size.  Ensuring that only \"large\" problems
  are spawned is called the ``granularity problem.''

  In summary: We want to tell ACL2 that it can evaluate the arguments of
  ~ilc[pargs] in parallel only when the parameter of ~c[pfib] is greater
  than some threshold.  Our tests using CCL have suggested that 27 is a
  reasonable threshold.

  ~b[Explicit Programming for the Granularity Problem]

  One way to avoid the granularity problem is to duplicate code as follows.
  ~bv[]
  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (if (> x 27) ; the granularity test
                 (pargs (binary-+ (pfib (- x 1))
                                  (pfib (- x 2))))
               (binary-+ (pfib (- x 1))
                         (pfib (- x 2)))))))
  ~ev[]
  Duplicating code is fundamentally a bad design principle, because it can
  double the work for future maintenance.  A ``granularity form'' is an
  expression
  ~bv[]
  (declare (granularity <form>))
  ~ev[]
  that can allow threads to be spawned (without duplicating code) whenever the
  evaluation of ~c[<form>] results in a non-~c[nil] value.  It may be placed
  inside any call of a parallelism primitive, in a position documentated
  separately for each primitive.  Here is a definition of ~c[pfib] using this
  feature for a call of the parallelism primitive ~ilc[pargs].
  ~bv[]
  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (pargs
              (declare (granularity (> x 27)))
              (binary-+ (pfib (- x 1))
                        (pfib (- x 2)))))))
  ~ev[]

  Test each version as follows (or substitute your own natural number for 33).
  ~bv[]
    (time$ (fib 33))
    (time$ (pfib 33))
  ~ev[]

  ~b[Another Granularity Issue Related to Thread Limitations]

  Our implementation of parallelism primitives has the property that once a
  thread is assigned a computation, that assignment stays in effect until the
  computation is complete.  In particular, if a thread encounters a parallelism
  primitive that spawns child threads, the parent thread stays assigned,
  waiting until the child computations complete before it can continue its own
  computation.  In the meantime, the parent thread reduces the number of
  additional threads that Lisp can provide by 1, rather than being reassigned
  to do other work.

  How can this lack of reassignment affect the user?  Consider, for example,
  the application of a recursive function to a long list.  Imagine that this
  function is written so that the body contains a recursive call, for example
  as ~c[(pargs (process (car x)) (recur (cdr x)))].  Each such ~ilc[pargs] call
  that spawns child work must wait for its children, one of which is the work
  of evaluating ~c[(recur (cdr x))], to complete.  There is an ACL2 limit on
  how much pending work can be in the system, limiting the number of
  ~ilc[pargs] calls that can result in parallel execution.  For example, if
  the ACL2 limit is k and each call of ~ilc[pargs] actually spawns threads for
  evaluating  its arguments, then
  after k ~c[cdr]s there will be no further parallel execution.

  Possible solutions may include reworking of algorithms (for example to be
  tree-based rather than list-based) or using appropriate granularity forms.
  We hope that future implementations will allow thread ``re-deployment'' in
  order to mitigate this problem.  This problem applies to ~ilc[plet],
  ~ilc[pargs], ~ilc[pand], ~ilc[por], and ~ilc[spec-mv-let].

  ~b[Introducing] ~ilc[Plet]

  We can use a ~ilc[let] binding to compute the recursive calls of ~c[fib] and
  then add the bound variables together, as follows.
  ~bv[]
  (defun fib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (let ((a (fib (- x 1)))
                   (b (fib (- x 2))))
               (+ a b)))))
  ~ev[]

  By using the parallelism primitive ~ilc[plet], we can introduce parallelism
  much as we did using ~ilc[pargs], with an optional granularity form, as
  follows.
  ~bv[]
  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (plet
              (declare (granularity (> x 27)))
              ((a (pfib (- x 1)))
               (b (pfib (- x 2))))
              (+ a b)))))
  ~ev[]
  Notice that this time, we were able to use ~c[+] rather than being forced to
  use ~c[binary-+].  Unlike ~ilc[pargs], which expects a function call (not a
  macro call), ~ilc[plet] allows macros at the top level of its body.

  ~b[Introducing] ~ilc[Pand] (By Way of a Tree Validation Example)

  Consider ``genetic trees'' that contains leaves of DNA elements, in the sense
  that each tip is one of the symbols ~c[A], ~c[G], ~c[C], or ~c[T].  First we
  define the function ~c[valid-tip] which recognizes whether a tip contains one
  of these symbols.
  ~bv[]
  (defun valid-tip (tip)
    (declare (xargs :guard t))
    (or (eq tip 'A)
        (eq tip 'G)
        (eq tip 'C)
        (eq tip 'T)))
  ~ev[]

  Now we define a function that traverses the tree, checking that every tip is
  valid.
  ~bv[]
  (defun valid-tree-serial (tree)
    (declare (xargs :guard t))
    (if (atom tree)
        (valid-tip tree)
      (and (valid-tree-serial (car tree))
           (valid-tree-serial (cdr tree)))))
  ~ev[]

  We also define a parallel version.
  ~bv[]
  (defun valid-tree-parallel (tree)
    (declare (xargs :guard t))
    (if (atom tree)
        (valid-tip tree)
      (pand (valid-tree-parallel (car tree))
            (valid-tree-parallel (cdr tree)))))
  ~ev[]

  Before we can time the functions, we need to create test trees.  We have
  found that test trees need to be approximately 1 gigabyte before we clearly
  see speedup, and we make them asymmetric to demonstrate the ability of our
  implementation to adapt to asymmetric data.  We can create the trees with the
  execution of the following forms.
  ~bv[]
  (defun make-valid-binary-tree (x)
    (declare (xargs :mode :program))
    (if (< x 0)
        (cons (cons 'C 'G) (cons 'A 'T))
      (cons (make-valid-binary-tree (- x 2)) ; 2 to make asymmetric
            (make-valid-binary-tree (- x 1)))))

  (defconst *valid-tree* (make-valid-binary-tree 30)) ; takes awhile
  (defconst *invalid-tree* (cons *valid-tree* nil)) ; nil is invalid tip
  ~ev[]

  We can time our functions with the forms:
  ~bv[]
  (time$ (valid-tree-serial *valid-tree*))
  (time$ (valid-tree-parallel *valid-tree*))
  ~ev[]
  Unfortunately, the serial version runs faster than the parallelism version;
  however, there is more to this story.

  ~b[Demonstrating Early Termination with an Invalid Tree]

  Now observe this magic:
  ~bv[]
  (time$ (valid-tree-serial   *invalid-tree*))
  (time$ (valid-tree-parallel *invalid-tree*))
  ~ev[]
  The serial version took awhile, while the parallel version finished almost
  immediately.  The test for validation was split into testing the ~ilc[car]
  and the ~ilc[cdr] of the ~c[*invalid-tree*] root, and since the ~c[cdr] was
  equal to ~c[nil], its test returned immediately.  This immediate return
  quickly interrupted the computation associated with the ~c[car], and returned
  the result.

  ~b[Granularity with] ~ilc[Pand]

  We can also define a parallel version with a granularity form:
  ~bv[]
  (defun valid-tree-parallel (tree depth)
    (declare (xargs :guard (natp depth)))
    (if (atom tree)
        (valid-tip tree)
      (pand
       (declare (granularity (< depth 5)))
       (valid-tree-parallel (car tree) (1+ depth))
       (valid-tree-parallel (cdr tree) (1+ depth)))))
  ~ev[]

  We can test this form by executing our previous forms.  You will probably
  find some speedup on a machine with several cores available, but more speedup
  can likely be obtained with an expensive test on the leaves in place of
  ~c[valid-tip].
  ~bv[]
  (time$ (valid-tree-serial   *valid-tree*))
  (time$ (valid-tree-parallel *valid-tree* 0))
  ~ev[]

  ~b[Introducing] ~ilc[Por]

  ~ilc[Por] can be used in the same way as ~ilc[pand], but with early
  termination occurring when an argument evaluates to a non-~c[nil] value, in
  which case the value returned is ~c[t].  Finally, ~ilc[por] also supports the
  use of a ~il[granularity] form.~/")

(defdoc granularity
  ":Doc-Section Parallel-programming
  limit the amount of parallelism~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  Some function calls are on arguments whose evaluation time is long enough to
  warrant parallel execution, while others are not.  A granularity form can be
  used to make appropriate restrictions on the use of parallelism.~/

  For example, consider the Fibonacci function.  Experiments have suggested
  that execution time can be reduced if whenever the argument is less than 27,
  a serial version of the Fibonacci function is called.  One way to utilize
  this information is to write two definitions of the Fibonacci function, one
  serial and one parallel.
  ~bv[]
  (defun fib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (binary-+ (fib (- x 1))
                       (fib (- x 2))))))

  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          ((< x 27) (binary-+ (fib (- x 1))
                              (fib (- x 2))))
          (t (pargs (binary-+ (pfib (- x 1))
                              (pfib (- x 2)))))))
  ~ev[]
  We realize quickly that writing both of these function definitions is
  cumbersome and redundant.  This problem can be avoided by using a
  ~c[granularity] declaration with a parallelism primitive.  This form ensures
  that a call is parallelized only if resources are available and the
  granularity form evaluates to a non-~c[nil] value at the time of the call.
  Below is a definition of the Fibonacci function using a granularity form.
  ~bv[]
  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((or (zp x) (<= x 0)) 0)
          ((= x 1) 1)
          (t (pargs (declare (granularity (>= x 27)))
                    (binary-+ (pfib (- x 1))
                              (pfib (- x 2)))))))
  ~ev[]

  A granularity form can reference an extra formal parameter that describes the
  call depth of the function the user is parallelizing.  Consider for example
  the following parallel ~c[mergesort] function, based on Davis's Ordered Sets
  library.  It splits the data into symmetric chunks for computation, so we
  increment the ~c[depth] argument during the recursive call on both the
  ~c[car] and ~c[cdr].
  ~bv[]
  (include-book \"finite-set-theory/osets/sets\" :dir :system)
  (defun sets::pmergesort-exec (x depth)
    (declare (xargs :mode :program))
    (cond ((endp x) nil)
          ((endp (cdr x)) (sets::insert (car x) nil))
          (t (mv-let (part1 part2)
                     (sets::split-list x nil nil)
                     (pargs
                      (declare (granularity (< depth 2)))
                      (sets::union (sets::pmergesort-exec part1
                                                          (1+ depth))
                                   (sets::pmergesort-exec part2
                                                          (1+ depth))))))))
  ~ev[]

  A less intrusive method (i.e., not requiring an extra formal parameter like
  the ~c[depth] argument just above), which however can be less efficient,
  involves analyzing the data itself for structural properties.  For example:
  ~bv[]
  (defun some-depth-exceeds (x n)
    (declare (xargs :guard (natp n)))
    (if (atom x)
        nil
      (if (zp n)
          t
        (or (some-depth-exceeds (car x) (1- n))
            (some-depth-exceeds (cdr x) (1- n))))))

  (defun valid-tip (x)
    (declare (xargs :guard t))
    (or (eq x 'A)
        (eq x 'T)
        (eq x 'C)
        (eq x 'G)))

  (defun pvalid-tree (x)
    (declare (xargs :guard t))
    (if (atom x)
        (valid-tip x)
      (pand (declare (granularity (some-depth-exceeds x 3)))
            (pvalid-tree (car x))
            (pvalid-tree (cdr x)))))
  ~ev[]
  If you experiment with calls of ~c[pvalid-tree], you are likely to find that
  the ``speedup'' it provides over a corresponding serial version is, in fact,
  a slowdown!  The problem is likely that ~c[some-depth-exceeds] is an
  expensive function to run repeatedly.  Instead of the approach above, it is
  often handy to add an extra formal parameter in order to allow for more
  efficient granularity forms, as we have done above in the definition of
  ~c[SETS::pmergesort-exec].
  ~/")

(defdoc parallelism-performance
  ":Doc-Section Parallel-programming
  performance issues for parallel execution~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~l[granularity] for an important construct that limits the spawning of
  parallel computations, which can be important when a computation is too
  short-lived to warrant a separate thread.

  There are times in which parallelism provides no speedup because of garbage
  collection in the underlying Lisp implementation.  The following example
  illustrates this phenomenon.  If you change the ~ilc[granularity] declaration
  so that the depth bound is 3, 4, or larger instead of 2, you may still find
  no speedup.  In all cases you may find that parallelism results in a
  significantly greater time spent in garbage collection.
  ~bv[]
  (include-book \"finite-set-theory/osets/sets\" :dir :system)
  (defun sets::pmergesort-exec (x depth)
      (declare (xargs :mode :program))
      (cond ((endp x) nil)
            ((endp (cdr x)) (sets::insert (car x) nil))
            (t (mv-let (part1 part2)
                       (sets::split-list x nil nil)
                       (pargs
                        (declare (granularity (< depth 2)))
                        (sets::union (sets::pmergesort-exec part1
                                                            (1+ depth))
                                     (sets::pmergesort-exec part2
                                                            (1+ depth))))))))
  (defconst *x* (reverse (fromto 1 400000)))
  (time$ (length (sets::pmergesort-exec *x* 0)))
  (set-parallel-execution nil)
  (time$ (length (sets::pmergesort-exec *x* 0)))
  ~ev[]~/~/")

(defdoc early-termination
  ":Doc-Section Parallel-programming
  early termination for ~ilc[pand] and ~ilc[por].~/~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  The evaluation of ~c[(and expr1 expr2)] returns ~c[nil] if ~c[expr1]
  evaluates to ~c[nil], avoiding the evaluation of ~c[expr2].  More generally,
  the evaluation of ~c[(and expr1 expr2 ... exprk)] terminates with a return
  value of ~c[nil] as soon as any ~c[expri] evaluates to ~c[nil] ~-[] no
  ~c[exprj] is evaluated in this case for ~c[j > i].  This so-called ``lazy
  evaluation'' of ~ilc[and] terms can thus save some computation; roughly
  speaking, the smaller the ~c[i], the more computation is saved.

  If the above call of ~ilc[and] is replaced by its parallel version,
  ~ilc[pand], then there can be even more opportunity for skipping work.  The
  arguments to ~ilc[pand] can be evaluated in parallel, in which case the first
  such evaluation that returns with a value of ~c[nil], if any, causes the
  remaining such evaluations to abort.

  Consider the following functions that compute whether a tree is valid
  (~pl[granularity] for a discussion of the granularity form).
  ~bv[]
  (defun valid-tip (x)
    (declare (xargs :guard t))
    (or (eq x 'A)
        (eq x 'T)
        (eq x 'C)
        (eq x 'G)))

  (defun pvalid-tree (x depth)
    (declare (xargs :guard (natp depth)))
    (if (atom x)
        (valid-tip x)
      (pand (declare (granularity (< depth 10)))
            (pvalid-tree (car x) (1+ depth))
            (pvalid-tree (cdr x) (1+ depth)))))
  ~ev[]

  We would like to stop execution as soon as any tip is found to be invalid.
  So, when computing the conjunction of terms by using ~ilc[pand], once one of
  those terms evaluates to ~c[nil], the computations for the other terms are
  aborted and the ~ilc[pand] call returns ~c[nil].  By using ~ilc[pand], we can
  in principle attain a speedup factor greater than the number of available
  cores.

  The concept of early termination also applies to ~ilc[por], except that early
  termination occurs when an argument evaluates to non-~c[nil].~/")

(defdoc parallel-pushing-of-subgoals-for-induction

  ":Doc-Section Parallel-proof
  consequences of how parallelized proofs of subgoals are pushed for induction~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  The following discussion, concerning the naming of subgoals pushed for proof
  by induction and the timeliness of aborting when two or more goals are pushed
  for proof by induction, only applies when waterfall parallelism is enabled
  (~pl[set-waterfall-parallelism]).~/

  When two sibling subgoals (e.g. 4.5 and 4.6) both push goals to be proved by
  induction (e.g., 4.6 pushes *1 and 4.5 pushes *2), a name is assigned to the
  second pushed subgoal (e.g., *2) as if the first push hasn't happened (e.g.,
  *2 is mistakenly called *1).  In such a case, we say what the name _could_
  be.  The following non-theorem illustrates how this works.
  ~bv[]
  (set-waterfall-parallelism :full)
  (thm (equal (append (car (cons x x)) y z) (append x x y)))
  ~ev[]

  There is another consequence of the way the parallelized waterfall pushes
  subgoals for proof by induction.  Without waterfall parallelism enabled, ACL2
  sometimes decides to abort instead of pushing a goal for later proof by
  induction, preferring instead to induct on the original conjecture.  But with
  waterfall parallelism enabled, the prover no longer necessarily immediately
  aborts to prove the original conjecture.  Suppose for example that sibling
  subgoals, Subgoal 4.6 and Subgoal 4.5, each push a subgoal for induction.  If
  the waterfall is performing the proof of each of these subgoals in parallel,
  the proof will no longer abort immediately after the second push occurs, that
  is at Subgoal 4.5.  As a result, the prover will continue through Subgoal
  4.4, Subgoal 4.3, and beyond.  It is not until the results of combining the
  proof results of Subgoal 4.6 with the results from the remaining sibling
  subgoals (4.5, 4.4, and so on), that the proof attempt will abort and revert
  to prove the original conjecture by induction.  This example illustrates
  behavior that is rather like the case that ~c[:]~ilc[otf-flg] is ~c[t], in
  the sense that the abort does not happen immediately, but also rather like
  the case that ~c[:]~ilc[otf-flg] is ~c[nil], in the sense that the abort does
  occur before getting to Subgoal 3.~/")

(defun caar-is-declarep (x)

; Recognizer for expressions x for which (car x) is of the form (declare ...).

  (declare (xargs :guard t))
  (and (consp x)
       (consp (car x))
       (eq (caar x) 'declare)))

(defun declare-granularity-p (x)

; We return true when x is of the form (declare (granularity <expr>)).

  (declare (xargs :guard t))
  (and (true-listp x)
       (eql (length x) 2)
       (eq (car x) 'declare)
       (let ((gran-form (cadr x)))
         (and (true-listp gran-form)
              (eql (length gran-form) 2)
              (eq (car gran-form) 'granularity)))))

(defun check-and-parse-for-granularity-form (x)

; X is a list of forms that may begin with a granularity declaration such as
; (declare (granularity (< depth 5))).  The return signature is (erp msg
; granularity-form-exists granularity-form remainder-forms).  If there is no
; declaration then we return (mv nil nil nil nil x).  If there is error then we
; return (mv t an-error-message nil nil x).  Otherwise we return (mv nil nil t
; granularity-form (cdr x)).

; It is necessary to return whether the granularity form exists.  If we did not
; do so, there would be no mechanism for distinguishing between a non-existent
; granularity form and one that was nil.

; A granularity form declaration is the only acceptable form of declaration.
; Some examples of unaccepted declarations are type and ignore declarations.

; We use this function in both the raw and acl2-loop definitions of plet to
; macroexpand away our granularity form, as part of our effort to ensure that
; pargs is logically the identity function.

  (cond ((not (caar-is-declarep x))
         (mv nil nil nil nil x))
        ((declare-granularity-p (car x))
         (let* ((granularity-declaration (cadar x))
                (granularity-form (cadr granularity-declaration)))
           (mv nil nil t granularity-form (cdr x))))
        (t
         (mv t
             "Within a parallelism primitive, a granularity form declaration ~
              is the only acceptable form of declaration.  Some examples of ~
              unaccepted declarations are type and ignore declarations.  See ~
              :DOC granularity."
             nil
             nil
             x))))

#+(or acl2-loop-only (not acl2-par))
(defmacro pargs (&rest forms)
  ":Doc-Section Parallel-programming

  parallel evaluation of arguments in a function call~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  Example Forms:
  (pargs (binary-+ (fibonacci (- x 1)) (fibonacci (- x 2))))

  (pargs (declare (granularity (> x 35)))
         (binary-+ (fibonacci (- x 1)) (fibonacci (- x 2))))~/

  General Form:
  (pargs (declare (granularity expr)) ; optional granularity declaration
         (f arg1 ... argN))
  ~ev[]
  where ~c[N >= 0] and each ~c[argi] and ~c[expr] are arbitrary terms.
  Logically, ~c[pargs] is just the identity macro, in the sense that the above
  forms can logically be replaced by ~c[(f arg1 ... argN)].  However, this
  ~c[pargs] form may parallelize the evaluation of arguments ~c[arg1] through
  ~c[argN] before applying function ~c[f] to those results.  If the above
  ~ilc[granularity] declaration is present, then its expression (~c[expr]
  above) is first evaluated, and if the result is ~c[nil], then such
  parallelism is avoided.  Even if parallelism is not thus avoided, parallelism
  may be limited by available resources.

  Since macros can change expressions in unexpected ways, it is illegal to call
  ~c[pargs] on a form that is a macro call.  To parallelize computation of
  arguments to a macro, ~pl[plet].

  ~l[parallelism-at-the-top-level] for restrictions on evaluating parallelism
  primitives from within the ACL2 top-level loop.~/"

  (mv-let
   (erp msg gran-form-exists gran-form remainder-forms)
   (check-and-parse-for-granularity-form forms)
   (cond (erp (er hard 'pargs msg))
         ((or (and (equal (length forms) 1) (not gran-form-exists))
              (and (equal (length forms) 2) gran-form-exists))
          (let ((function-call (car remainder-forms)))
            (if gran-form-exists
                `(prog2$ ,gran-form ,function-call)
              function-call)))
         (t
          (er hard 'pargs
              "Pargs was passed the wrong number of arguments.  Without a ~
               granularity declaration, pargs takes one argument.  With a ~
               granularity declaration, pargs requires two arguments, the ~
               first of which must be of the form ~x0.  See :DOC pargs."
              '(declare (granularity expr)))))))

#+(or acl2-loop-only (not acl2-par))
(defmacro plet (&rest forms)
  ":Doc-Section Parallel-programming

  parallel version of ~ilc[let]~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  Example Forms:
  (plet ((a (fibonacci (- x 1)))
         (b (fibonacci (- x 2))))
        (+ a b))

  (plet (declare (granularity (> x 35)))
        ((a (fibonacci (- x 1)))
         (b (fibonacci (- x 2))))
        (+ a b))~/

  General Form:
  (plet (declare (granularity expr)) ; optional granularity declaration
        ((var1 val1)
         ...
         (varN valN))
        (declare ...) ... (declare ...) ; optional declarations
        body)
  ~ev[]
  The syntax of ~c[plet] is identical to the syntax of ~ilc[let], except that
  ~c[plet] permits an optional granularity declaration in the first argument
  position; ~pl[granularity].  In the logic a call of ~c[plet] macroexpands to
  the corresponding call of ~ilc[let], where the granularity declaration (if
  any) is dropped.

  ~c[Plet] cause the evaluation of each ~c[vali] above to be done in parallel
  before processing the body.  If the above ~ilc[granularity] declaration is
  present, then its expression (~c[expr] above) is first evaluated, and if the
  result is ~c[nil], then such parallelism is avoided.  Even if parallelism is
  not thus avoided, parallelism may be limited by available resources.

  ~l[parallelism-at-the-top-level] for restrictions on evaluating parallelism
  primitives from within the ACL2 top-level loop.~/"

  (mv-let (erp msg gran-form-exists gran-form remainder-forms)
          (check-and-parse-for-granularity-form forms)
          (cond (erp (er hard 'plet msg))
                (gran-form-exists
                 `(prog2$ ,gran-form
                          (let ,@remainder-forms)))
                (t `(let ,@remainder-forms)))))

(defun binary-pand (x y)

; Booleanized binary and.

  (declare (xargs :guard t :mode :logic))
  (and x y t))

#+(or acl2-loop-only (not acl2-par))
(defmacro pand (&rest forms)

; We Booleanize pand so that it is consistent with por, which must be
; Booleanized (see :DOC por).  Another nice thing about this Booleanization is
; that it emphasizes that PAND differs from AND logically, which can raise
; awareness of a guard-related difference based on the impact of lazy
; evaluation.

  ":Doc-Section Parallel-programming

  parallel, Boolean version of ~ilc[and]~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  Example Forms:
  (pand (subsetp-equal x y)
        (subsetp-equal y x))

  (pand (declare
         (granularity
          (and (> (length x) 500)
               (> (length y) 500))))
         (subsetp-equal x y)
         (subsetp-equal y x))
  ~ev[]~/

  ~bv[]
  General Form:
  (pand (declare (granularity expr)) ; optional granularity declaration
        arg1 ... argN)
  ~ev[]
  where ~c[N >= 0] and each ~c[argi] and ~c[expr] are arbitrary terms.

  ~c[Pand] evaluates its arguments in parallel.  It returns a Boolean result:
  ~c[nil] if any argument evaluates to ~c[nil], else ~c[t].  Note that
  ~c[pand] always returns a Boolean result, even though ~c[and] can return a
  non-~c[nil] value other than ~c[t], namely the value of its last argument.
  (A moment's reflection will make it clear that in order for ~ilc[por] to
  parallelize efficiently, it needs to return a Boolean value; so ~c[pand]
  returns a Boolean value for consistency with ~ilc[por].)

  Another difference between ~c[pand] and ~ilc[and] is that for a call of
  ~c[pand], even if an argument evaluates to ~c[nil], a subsequent argument
  may be evaluated.  Consider the following example (where ~c[cw] prints a
  string; ~pl[cw]).
  ~bv[]
  (defun bar ()
    (pand (equal (make-list 100000) nil) ; evaluates to nil
          (cw \"hello world~~%\")))
  ~ev[]
  When ~c[(bar)] is evaluated, the above arguments of ~c[pand] can execute in
  parallel, causing ``~c[hello world]'' to be printed to the terminal.  If we
  had used ~c[and] rather than ~c[pand], then since
  ~c[(equal (make-list 100000) nil)] evaluates to ~c[nil], the above call of
  ~ilc[cw] would be avoided and no such printing would take place.  Even with
  ~c[pand], such printing ~em[might] not take place, depending on resources,
  timing of thread creation, and whether or not parallel execution is enabled
  (~pl[set-parallel-execution]).

  Note that unlike the case for ~ilc[and], the definition of ~c[pand] does not
  provide ~c[(consp x)] as a ~il[guard] to ~c[(car x)] in the call of ~c[pand]
  below:
  ~bv[]
  (defun h (x)
    (declare (xargs :guard t))
    (pand (consp x) (equal (car x) 'foo)))
  ~ev[]
  As a result, ~il[guard] verification will fail for the above definition.  If
  ~c[pand] were replaced by ~c[and], then ~il[guard] verification would
  succeed.

  ~l[parallelism-tutorial] for another example.  Also
  ~pl[parallelism-at-the-top-level] for restrictions on evaluating parallelism
  primitives from within the ACL2 top-level loop.  Finally
  ~pl[early-termination] to read how ~c[pand] can offer more efficiency than
  ~ilc[and] by avoiding evaluation of some of its arguments.~/"

; Since we use &rest, we know forms is a true-list.

  (mv-let
   (erp msg gran-form-exists gran-form remainder-forms)
   (check-and-parse-for-granularity-form forms)
   (cond (erp (er hard 'pand msg))
         ((atom remainder-forms) t) ; (pand) == t
         ((null (cdr remainder-forms)) ; same as length == 1
          (list 'if (car remainder-forms) t nil)) ; booleanize
         (gran-form-exists
          (list 'prog2$
                gran-form
                (xxxjoin 'binary-pand remainder-forms)))
         (t (xxxjoin 'binary-pand remainder-forms)))))

(defun binary-por (x y)

; Booleanized binary or.

  (declare (xargs :guard t :mode :logic))
  (if x t (if y t nil)))

#+(or acl2-loop-only (not acl2-par))
(defmacro por (&rest forms)

; Note that por must be Booleanized if we are to support early termination,
; i.e., so that any non-nil value can cause por to return.

  ":Doc-Section Parallel-programming

  parallel, Boolean version of ~ilc[or]~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  Example Forms:
  (por (subsetp-equal x y)
       (subsetp-equal y x))

  (por (declare
        (granularity
         (and (> (length x) 500)
              (> (length y) 500))))
        (subsetp-equal x y)
        (subsetp-equal y x))
  ~ev[]~/

  ~bv[]
  General Form:
  (por (declare (granularity expr)) ; optional granularity declaration
       arg1 ... argN)
  ~ev[]
  where ~c[N >= 0] and each ~c[argi] and ~c[expr] are arbitrary terms.

  ~c[Por] evaluates its arguments in parallel.  It returns a Boolean result:
  ~c[t] if any argument evaluates to non-~c[nil], else ~c[nil].  Note that
  while ~ilc[or] returns the first non-~c[nil] value from evaluating its
  arguments left-to-right (if any such value is not ~c[nil]) ~ilc[por] always
  returns a Boolean result, in support of efficiency (~pl[early-termination])
  in light of the nondeterministic order in which argument values are returned.

  Another difference between ~c[por] and ~ilc[or] is that for a call of
  ~c[por], even if the an argument's value is not ~c[nil], a subsequent
  argument may be evaluated.  ~l[pand] for a discussion of the analogous
  property of ~c[pand].  In particular, ~il[guard]s generated from calls of
  ~c[por] may not assume for an argument that the preceding arguments evaluated
  to ~c[nil].

  ~l[parallelism-tutorial] for another example.  Also
  ~pl[parallelism-at-the-top-level] for restrictions on evaluating parallelism
  primitives from within the ACL2 top-level loop.  Finally
  ~pl[early-termination] to read how ~c[por] can offer more efficiency than
  ~ilc[or] by avoiding evaluation of some of its arguments.~/"

  (mv-let
   (erp msg gran-form-exists gran-form remainder-forms)
   (check-and-parse-for-granularity-form forms)
   (cond (erp (er hard 'por msg))
         ((atom remainder-forms) nil) ; (por) == nil
         ((null (cdr remainder-forms)) ; same as length == 1
          (list 'if (car remainder-forms) t nil))
         (gran-form-exists
          (list 'prog2$
                gran-form
                (xxxjoin 'binary-por remainder-forms)))
         (t (xxxjoin 'binary-por remainder-forms)))))

(defun or-list (x)
  (declare (xargs :guard (true-listp x) :mode :logic))
  (if (endp x)
      nil
    (if (car x)
        t
        (or-list (cdr x)))))

(defun and-list (x)
  (declare (xargs :guard (true-listp x) :mode :logic))
  (if (endp x)
      t
    (and (car x)
         (and-list (cdr x)))))

(defun cpu-core-count (state)

  ":Doc-Section ACL2::ACL2-built-ins

  the number of cpu cores~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  Unless the ACL2 executable supports parallel execution (~pl[parallelism]),
  this function returns ~c[(mv 1 state)].  Otherwise:

  ~c[(Cpu-core-count state)] returns ~c[(mv core-count state)], where
  ~c[core-count] is the number of cpu cores if ACL2 can get that information
  from the underlying Common Lisp implementation.  Otherwise an error occurs,
  unless global ~c['cpu-core-count] is assigned to a positive integer value
  (~pl[assign]), in which case that value is returned as the ~c[core-count].
  ~bv[]
  Example:
  (cpu-core-count state) ==> (mv 4 state)
  ~ev[].~/~/"

  (declare (xargs :stobjs state :guard t))
  #+(and (not acl2-loop-only) (not acl2-par))
  (when (live-state-p state)
    (return-from cpu-core-count
                 (mv 1 state)))
  #+(and (not acl2-loop-only) acl2-par)
  (when (live-state-p state)
    (return-from cpu-core-count
                 (mv (if (and (f-boundp-global 'cpu-core-count state)
                              (posp (f-get-global 'cpu-core-count state)))
                         (core-count-raw nil (f-get-global 'cpu-core-count
                                                           state)) 
                       (core-count-raw 'core-count))
                     state)))
  (mv-let (nullp val state)
          (read-acl2-oracle state)
          (declare (ignore nullp))
          (mv val state)))

; Preliminary code for parallelizing the rewriter

; ; We now develop code for parallelizing calls to the arguments of a call of
; ; rewrite.
; 
; ; WARNING!  We believe that this approach has the following bug.  If
; ; with-prover-time-limit is used, then the main thread (which is the one
; ; calling waterfall-step) has a catch (implemented by the call there of
; ; catch-time-limit5) that will only catch throws to that tag from the SAME
; ; thread.  We will get in trouble if a spawned thread's call of rewrite does
; ; such a throw.
; 
; ; Warning: Moreover, if we use this code, consider modifying the
; ; rewrite-constant to store the value of :limit in
; ; rewrite-args-granularity-table.  Otherwise, we have to go to the world with a
; ; potentially slow getprop every time we call rewrite-args-par-big-enough.
; ; Maybe that's just noise, but maybe it's expensive.
; 
; ; We initially set the value of (the unique key) :limit to nil in
; ; rewrite-args-granularity-table, so that in fact we do not do such
; ; parallelization.  But we leave this infrastructure in place (see comment "or
; ; try :limit" below) in case we want to experiment with such parallelization in
; ; the future.
; 
; #+acl2-par
; (table rewrite-args-granularity-table nil nil
;        :guard (and (eq key :limit)
;                    (or (null val) (natp val))))
; 
; #+acl2-par
; (table rewrite-args-granularity-table :limit nil) ; or try :limit = 10
; 
; #+acl2-par
; (defun rewrite-args-par-big-enough-rec (flg x bound acc)
; 
; ; Flg is true when x is a list of terms; else x is a term.  Returns a number by
; ; accumulating into acc, or t if that number would exceed bound.  We assume
; ; that acc is <= bound.
; 
;   (cond (flg ; x is a list
;          (cond ((null x)
;                 acc)
;                (t
;                 (let ((new-acc (rewrite-args-par-big-enough-rec
;                                 nil (car x) bound acc)))
;                   (if (eq new-acc t)
;                       t
;                     (rewrite-args-par-big-enough-rec
;                      flg (cdr x) bound new-acc))))))
;         ((variablep x)
;          acc)
;         ((fquotep x)
;          acc)
;         ((eql bound acc)
;          t)
;         ((flambdap (ffn-symb x))
;          (let ((new-acc (rewrite-args-par-big-enough-rec
;                          nil (lambda-body (ffn-symb x)) bound (1+ acc))))
;            (if (eq new-acc t)
;                t
;              (rewrite-args-par-big-enough-rec t (fargs x) bound new-acc))))
;         (t (rewrite-args-par-big-enough-rec t (fargs x) bound (1+ acc)))))
; 
; #+acl2-par
; (defun rewrite-args-par-big-enough (x wrld)
; 
; ; If the limit is set to nil, the function returns nil.  This allows the
; ; enabling and disabling of rewriting args in parallel.
; 
;   (let ((limit (cdr (assoc-eq :limit
;                               (table-alist
;                                'rewrite-args-granularity-table
;                                wrld)))))
;     (and limit (equal t (rewrite-args-par-big-enough-rec nil x limit 0)))))
; 
; ; With the additions above, we can contemplate adding something like the
; ; following to the rewrite nest below.  If we do that, then replace the call of
; ; rewrite-args in rewrite by the following:
; 
; ;                    #-acl2-par
; ;                    rewrite-args
; ;                    #+acl2-par
; ;                    rewrite-args-par
; 
; #+acl2-par
; (defun rewrite-args-par (args alist bkptr ; &extra formals
;                               rdepth
;                               type-alist obj geneqv wrld state fnstack
;                               ancestors backchain-limit
;                               simplify-clause-pot-lst rcnst gstack ttree)
;   (let ((pair (rewrite-entry (rewrite-args-par-rec args alist bkptr))))
;     (mv (car pair) (cdr pair))))
; 
; #+acl2-par
; (defun rewrite-args-par-rec (args alist bkptr ; &extra formals
;                                   rdepth
;                                   type-alist obj geneqv wrld state fnstack
;                                   ancestors backchain-limit
;                                   simplify-clause-pot-lst rcnst gstack ttree)
; 
; ; Note: In this function, the extra formal geneqv is actually a list of geneqvs
; ; or nil denoting a list of nil geneqvs.
; 
; ; Unlike rewrite-args, we return (cons rewritten-args ttree) instead of
; ; (mv rewritten-args ttree).
; 
;   (declare (type (unsigned-byte 29) rdepth))
;   (cond ((f-big-clock-negative-p state)
;          (cons (sublis-var-lst alist args)
;                ttree))
;         ((null args)
;          (cons nil ttree))
;         (t (plet
;             (declare (granularity t)) ; should call rewrite-args-par-big-enough
;             ((pair1
;               (mv-let (term ttree1)
;                       (rewrite-entry (rewrite (car args) alist bkptr)
;                                      :geneqv (car geneqv)
;                                      :ttree nil)
;                       (cons term ttree1)))
;              (pair2 (rewrite-entry
;                      (rewrite-args-par-rec (cdr args) alist (1+ bkptr))
;                      :geneqv (cdr geneqv))))
;             (let* ((term (car pair1))
;                    (ttree1 (cdr pair1))
;                    (rewritten-args (car pair2))
;                    (ttree2 (cdr pair2)))
;               (cons (cons term rewritten-args)
;                     (cons-tag-trees ttree1 ttree2)))))))

#+(or acl2-loop-only (not acl2-par))
(defmacro spec-mv-let (bindings computation body)

  ":Doc-Section Parallel-programming

  modification of ~ilc[mv-let] supporting speculative and parallel execution~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  Example Form:
  (defun pfib-with-step-count (x)
    (declare (xargs :mode :program))
    (if (or (zp x) (< x 33))
        (fib-with-step-count x)
      (spec-mv-let 
       (a cnt1)
       (pfib-with-step-count (- x 1))
       (mv-let (b cnt2)
               (pfib-with-step-count (- x 2))
               (if t
                   (mv (+ a b)
                       (+ 1 cnt1 cnt2))
                 (mv \"speculative result is always needed\"
                     -1))))))~/
  
  General Form:
  (spec-mv-let
   (v1 ... vn)  ; bind distinct variables
   <spec>       ; evaluate speculatively; return n values
   (mv-let
    (w1 ... wk) ; bind distinct variables
    <eager>     ; evaluate eagerly
    (if <test>  ; use results from <spec> if true
        <typical-case> ; may mention v1 ... vn
      <abort-case>)))  ; does not mention v1 ... vn
  ~ev[]

  Our design of ~c[spec-mv-let] is guided by its use in ACL2 source code to
  parallelize part of ACL2's proof process, in the experimental parallel
  extension of ACL2.  The user can think of ~c[spec-mv-let] as a speculative
  version of ~ilc[mv-let].  (In ordinary ACL2, the semantics agree with this
  description but without speculative or parallel execution.)

  Evaluation of the above general form proceeds as suggested by the comments.
  First, ~c[<spec>] is executed speculatively.  Control then passes immediately
  to the ~ilc[mv-let] call, without waiting for the result of evaluating
  ~c[<spec>].  The variables ~c[(w1 ... wk)] are bound to the result of
  evaluating ~c[<eager>], and then ~c[<test>] is evaluated.  If the value of
  ~c[<test>] is true, then the values of ~c[(v1 ... vn)] are needed, and
  ~c[<typical-case>] blocks until they are available.  If the value of
  ~c[<test>] is false, then the values of ~c[(v1 ... vn)] are not needed, and
  the evaluation of ~c[<spec>] may be aborted.

  The calls to ~c[mv-let] and to ~c[if] displayed above in the General Form are
  an essential part of the design of ~c[spec-mv-let], and are thus required.

  The following definition of ~c[fib-with-step-count] completes the example
  above:

  ~bv[]
  (defun fib-with-step-count (x)
  (declare (xargs :mode :program))
  (cond ((<= x 0)
         (mv 0 1))
        ((= x 1) (mv 1 1))
        (t (mv-let (a cnt1)
                   (fib-with-step-count (- x 1))
                   (mv-let (b cnt2) 
                           (fib-with-step-count (- x 2))
                           (mv (+ a b)
                               (+ 1 cnt1 cnt2)))))))
  ~ev[]~/"

  (assert$ 
   (and (true-listp body) 
        (equal (length body) 4) 
        (or (equal (car body) 'mv-let@par)
            (equal (car body) 'mv-let)
            (equal (car body) 'mv?-let)))
   (let* ((inner-let (car body))
          (inner-bindings (cadr body))
          (inner-body (caddr body))
          (ite (cadddr body)))
     (assert$ (and (true-listp ite) 
                   (equal (length ite) 4) 
                   (equal (car ite) 'if))
              (let* ((test (cadr ite))
                     (true-branch (caddr ite))
                     (false-branch (cadddr ite)))
                `(check-vars-not-free

; Keep the check for variable name "the-very-obscure-feature" in sync with the
; variable name in the raw Lisp version.

                  (the-very-obscure-future)
                  (,inner-let
                   ,inner-bindings
                   ,inner-body
                   (if (check-vars-not-free ,bindings ,test)
                       (mv?-let ,bindings
                                ,computation
                                ,true-branch)                     
                     (check-vars-not-free ,bindings ,false-branch)))))))))

; Parallelism wart: when set-verify-guards-eagerness is 0, and there is a guard
; violation in subfunctions that are evaluating in the non-main-thread, we get
; errors that aren't user friendly (the errors occur in the non-main-threads).
; I think that the solution to this problem might necessitate catching the
; errors and re-causing them.  Hitting ctrl+c causes the main thread to abort
; waiting on the result from those threads, and allows the interactive session
; to resume.  David says that he may have already fixed this for spec-mv-let,
; and for the other parallelism primitives, the solution may be for the closure
; to bind *ld-level* to the value inherited from each thread's parent.  As of
; this writing (1/13/2012), we can see the unfortunate need for control-c in
; the following example:
; (defun f (x) (declare (xargs :guard (integerp x))) (+ x x))
; (defun g ()
;   (declare (xargs :guard t :verify-guards nil))
;   (plet ((a (f (car (make-list 1000000))))
;          (b (f (car (make-list 1000000)))))
;         (+ a b)))
; (g)

(defdoc error-triples-and-parallelism
  ":Doc-Section Parallel-programming
  how to avoid error triples in ACL2(p)~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ACL2 supports the use of error triples in many features; e.g.,
  ~ilc[computed-hints].  (For background on error triples,
  ~pl[programming-with-state].)  However, ACL2(p) does not support the use of
  error triples in some of these features (e.g., ~ilc[computed-hints]) while
  ~il[waterfall-parallelism] is enabled.~/
  
  You may see an error message like the following when running ACL2(p) with
  ~il[waterfall-parallelism] enabled:

  ~bv[]
  ACL2 Error in ( THM ...):  Since we are translating a form in ACL2(p)
  intended to be executed with waterfall parallelism enabled, the form
  (MY-STATE-MODIFYING-COMPUTED-HINT ID STATE) was expected to represent
  an ordinary value, not an error triple (mv erp val state), as would
  be acceptable in a serial execution of ACL2.  Therefore, the form returning
  a tuple of the form (* * STATE) is an error.  See :DOC unsupported-
  waterfall-parallelism-features and :DOC error-triples-and-parallelism
  for further explanation.
  ~ev[]

  In this particular example, the cause of the error was trying to use a
  computed hint that returned state, which is not allowed when executing the
  waterfall in parallel (~pl[unsupported-waterfall-parallelism-features] for
  other related information).

  Often, the only reason users need to return state is so they can perform
  some output during the proof process.  In this case, we suggest using one of
  the state-free output functions, like ~ilc[cw] or ~ilc[observation-cw].  If
  the user is concerned about the interleaving of their output with other
  output, these calls can be surrounded with the macro ~ilc[with-output-lock].

  Another frequent reason users return state is so they can cause a ~c[soft]
  error and halt the proof process.  In this case, we suggest instead calling
  ~ilc[er] with the ~c[hard] or ~c[hard?] severity.  By using these mechanisms,
  the user avoids modifying ~ilc[state], a requirement for much of the code
  written in ACL2(p).

  You may encounter other similar error messages when using
  ~il[computed-hints], ~il[custom-keyword-hints], or ~il[override-hints].
  Chances are that you are somehow returning an error triple when an ordinary
  value is needed.  If this turns out not to be the case, please let the ACL2
  implementors know.~/")

(defdoc with-output-lock

; Note: If you're looking for the definition of with-output-lock, you can find
; it as (deflock <comments> *output-lock*) in axioms.lisp.

  ":Doc-Section Parallel-programming

  provides a mutual-exclusion mechanism for performing output in parallel~/

  This documentation topic relates to an experimental extension of ACL2,
  ACL2(p), created initially by David L. Rager.  ~l[compiling-acl2p] for how to
  build an executable image that supports parallel execution.  Also see
  distributed directory ~c[books/parallel/] for examples.~/

  One may wish to perform output while executing code in parallel.  If 
  threads are allowed to print concurrently, the output will be interleaved and
  often unreadable.  To avoid this, the user can surround forms that perform
  output with the ~c[with-output-lock] macro.

  Take the following definition of ~c[pfib] as an example.

  ~bv[]
  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((mbe :logic (or (zp x) (<= x 0))
                :exec (<= x 0))
           0)
          ((= x 1) 1)
          (t (plet (declare (granularity t))
                   ((a (prog2$ (cw \"Computing pfib ~~x0~~%\" (- x 1))
                               (pfib (- x 1))))
                    (b (prog2$ (cw \"Computing pfib ~~x0~~%\" (- x 2))
                               (pfib (- x 2)))))
                   (+ a b)))))
  ~ev[]

  With ~il[parallel-execution] enabled, a call of ~c[(pfib 5)]results in
  non-deterministically interleaved output, for example as follows.

  ~bv[]
  ACL2 !>(pfib 5)
  CComputing pfib 4
  omputing pfib 3
  ComCpuotmipnugt ipnfgi bp fib3
  2
  Computing pCfiobm put2i
  ng pfib 1
  Computing pfib Co1mp
  uting pfib 0
  CCoommppuuttiinngg  ppffiibb  12

  ComCpuotmipnugt ipnfgi bp fib1 
  0
  CoCmopmuptuitnign gp fpifbi b 1
  0
  5
  ACL2 !>
  ~ev[]

  If the user instead surrounds the calls to ~ilc[cw] with the macro
  ~c[with-output-lock], as in the following session, the output will no longer
  be interleaved.

  ~bv[]
  ACL2 !>
  (defun pfib (x)
    (declare (xargs :guard (natp x)))
    (cond ((mbe :logic (or (zp x) (<= x 0))
                :exec (<= x 0))
           0)
          ((= x 1) 1)
          (t (plet (declare (granularity t))
                   ((a (prog2$ (with-output-lock
                                (cw \"Computing pfib ~~x0~~%\" (- x 1)))
                               (pfib (- x 1))))
                    (b (prog2$ (with-output-lock
                                (cw \"Computing pfib ~~x0~~%\" (- x 2)))
                               (pfib (- x 2)))))
                   (+ a b)))))

  <snip>

  ACL2 !>(pfib 5)
  Computing pfib 4
  Computing pfib 3
  Computing pfib 3
  Computing pfib 2
  Computing pfib 2
  Computing pfib 1
  Computing pfib 2
  Computing pfib 1
  Computing pfib 1
  Computing pfib 0
  Computing pfib 1
  Computing pfib 0
  Computing pfib 1
  Computing pfib 0
  5
  ACL2 !>
  ~ev[]
  ~/")

; Parallelism wart: it is still possible in ACL2(p) to receive an error at the
; Lisp-level when CCL cannot "create thread".  An example of a user (Kaufmann)
; encountering this error is shown below, with book
; concurrent-programs/bakery/stutter2.  In March 2012, Kaufmann's laptop could
; sometimes exhibit this problem (a 2-core machine with 4 hardware threads).
; There are two possible ways to fix this problem.  The first is to set the
; default-total-parallelism-work-limit to a lower number so that it never
; occurs (but this costs performance).  Kaufmann suggests that we should also
; catch this particular Lisp error and instead cause an ACL2 error, similar to
; the error in function not-too-many-futures-already-in-existence.  This may be
; harder than one might intially think, because our current mechanism for
; catching errors in child threads involves catching thrown tags and then
; rethrowing them in the thread who is that child's parent.

; The error looks like the following:

;; <snip>
;; 
;;.............................................................
;; ***********************************************
;; ************ ABORTING from raw Lisp ***********
;; Error:  .Can't create thread
;; ***********************************************

;; The message above might explain the error.  If not, and
;; if you didn't cause an explicit interrupt (Control-C),
;; then the root cause may be call of a :program mode
;; function that has the wrong guard specified, or even no
;; guard specified (i.e., an implicit guard of t).
;; See :DOC guards.

;; To enable breaks into the debugger (also see :DOC acl2-customization):
;; (SET-DEBUGGER-ENABLE T)
;; .
;; ***********************************************
;; ************ ABORTING from raw Lisp ***********
;; Error:  Can't create thread
;; ***********************************************

;; The message above might explain the error.  If not, and
;; if you didn't cause an explicit interrupt (Control-C),
;; then the root cause may be call of a :program mode
;; function that has the wrong guard specified, or even no
;; guard specified (i.e., an implicit guard of t).
;; See :DOC guards.

;; To enable breaks into the debugger (also see :DOC acl2-customization):
;; (SET-DEBUGGER-ENABLE T)
;; ...........................................................
;; ..................Here is the current pstack [see :DOC pstack]:
;; (CLAUSIFY REWRITE-ATM
;;          SIMPLIFY-CLAUSE SIMPLIFY-CLAUSE
;;          REWRITE-ATM SIMPLIFY-CLAUSE REWRITE-ATM
;;          PREPROCESS-CLAUSE PREPROCESS-CLAUSE
;;          SETUP-SIMPLIFY-CLAUSE-POT-LST
;;          SIMPLIFY-CLAUSE
;;          EV-FNCALL-META REWRITE-ATM
;;          EV-FNCALL-META EV-FNCALL-META
;;          EV-FNCALL-META REWRITE-ATM
;;          EV-FNCALL EV-FNCALL EV-FNCALL-META
;;          REWRITE-ATM REWRITE-ATM SIMPLIFY-CLAUSE
;;          FORWARD-CHAIN1 SIMPLIFY-CLAUSE
;;          PREPROCESS-CLAUSE EV-FNCALL-META
;;          REWRITE-ATM REWRITE-ATM REWRITE-ATM
;;          FORWARD-CHAIN1 FORWARD-CHAIN1
;;          SIMPLIFY-CLAUSE SIMPLIFY-CLAUSE
;;          SIMPLIFY-CLAUSE PREPROCESS-CLAUSE
;;          SIMPLIFY-CLAUSE SIMPLIFY-CLAUSE
;;          SIMPLIFY-CLAUSE SIMPLIFY-CLAUSE
;;          REWRITE-ATM PREPROCESS-CLAUSE
;;          SIMPLIFY-CLAUSE PREPROCESS-CLAUSE
;;          SIMPLIFY-CLAUSE PREPROCESS-CLAUSE
;;
;; <snip>

(defun set-total-parallelism-work-limit-fn (val state)
  (declare (xargs :guard (or (equal val :none)
                             (integerp val))))
  (f-put-global 'total-parallelism-work-limit val state))

(defmacro set-total-parallelism-work-limit (val)

  ":Doc-Section switches-parameters-and-modes

  set thread limit beyond which parallelism primitives execute serially~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].  While the most
  common use of the limit described below is in parallel proof
  (~pl[parallel-proof]), it also applies to all parallelism primitives
  (~pl[parallel-programming]) except ~ilc[spec-mv-let] ~-[] though we expect
  that rather few programming applications will encouter this limit.

  ~bv[]
  General Forms:
  (set-total-parallelism-work-limit :none)     ; disable the limit
  (set-total-parallelism-work-limit <integer>) ; set limit to <integer>
  ~ev[]

  ~l[parallelism-tutorial], Section ``Another Granularity Issue Related to
  Thread Limitations'', for an explanation of how the host Lisp can run out of
  threads.  Also ~pl[set-total-parallelism-work-limit-error].~/

  If the underlying runtime system (the Operating System, the host Lisp, etc.)
  is unable to provide enough threads to finish executing the parallelism work
  given to it, the runtime system can crash in a very unpleasant
  manner (ranging from a Lisp error to completely freezing the machine).  To
  avoid this unpleasantness, ACL2(p) will attempt to avoid creating so much
  parallelism that the runtime system crashes.

  ACL2 initially uses a conservative estimate to limit the number of threads.
  To tell ACL2(p) to use a different limit, call
  ~c[set-total-parallelism-work-limit] with the new limit.  For example, if the
  current default limit is 10,000, then to allow 13,000 threads to exist, issue
  the following form at the top level.
  ~bv[]
  (set-total-parallelism-work-limit 13000)
  ~ev[]

  To disable this limit altogether, evaluate the following form:
  ~bv[]
  (set-total-parallelism-work-limit :none)
  ~ev[]

  The default value of total-parallelism-work-limit can be found by calling
  function ~c[default-total-parallelism-work-limit].  If the default value is
  too high for your system please notify the ACL2 maintainers with a limit that
  does work for your system, as they might then lower the default limit.~/

  :cited-by parallel-proof
  :cited-by parallel-programming"

  (declare (xargs :guard (or (equal val :none)
                             (integerp val))))
  `(set-total-parallelism-work-limit-fn ,val state))

(defun set-total-parallelism-work-limit-error-fn (val state)
  (declare (xargs :guard (or (equal val t)
                             (null val))))
  (f-put-global 'total-parallelism-work-limit-error val state))

(defmacro set-total-parallelism-work-limit-error (val)

; Parallelism blemish: explain something about how, unlike
; set-total-parallelism-work-limit, this one only applies to proof (not
; programming).

  ":Doc-Section switches-parameters-and-modes

  control the action taken when the thread limit is exceeded~/

  This ~il[documentation] topic relates to the experimental extension of ACL2
  supporting parallel execution and proof; ~pl[parallelism].

  ~bv[]
  General Forms:
  (set-total-parallelism-work-limit-error t)   ; cause error (default)
  (set-total-parallelism-work-limit-error nil) ; disable error and
                                               ; continue serially
  ~ev[]

  ~l[parallelism-tutorial], Section ``Another Granularity Issue Related to
  Thread Limitations'', for an explanation of how the host Lisp can run out of
  threads.  ~l[set-total-parallelism-work-limit] for further details, including
  an explanation of how to manage the limit that triggers this error.~/

  The value of state global ~c[total-parallelism-work-limit-error] dictates
  what occurs when the underlying runtime system runs reaches a limit on the
  number of threads for parallel computation.  By default, when this limit is
  reached, the ACL2(p) user will receive an error and computation will halt.
  At this point, the ACL2(p) user has the following options.

  (1) Remove the limit by evaluating the following form.
  ~bv[]
  (set-total-parallelism-work-limit :none)
  ~ev[]

  (2) Disable the error so that execution continues serially once the available
  thread resources have been exhausted.
  ~bv[]
  (set-total-parallelism-work-limit-error nil)
  ~ev[]

  (3) Increase the limit on number of threads that ACL2(p) is willing to
  create, in spite of potential risk (~pl[set-total-parallelism-work-limit]).
  In this case, the following query returns the current limit.
  ~bv[]
  (f-get-global 'total-parallelism-work-limit)
  ~ev[]
  Then to increase that limit, evaluate the following form:
  ~bv[]
  (set-total-parallelism-work-limit <new-integer-value>)
  ~ev[]

  For example, suppose that the value of ~c[total-parallelism-work-limit] was
  originally 10,000.  Then evaluation of the following form increases that
  limit to 13,000.
  ~bv[]
  (set-total-parallelism-work-limit 13000)
  ~ev[]
  ~/
  :cited-by parallel-proof"

  (declare (xargs :guard (or (equal val t)
                             (null val))))
  `(set-total-parallelism-work-limit-error-fn ,val state))
