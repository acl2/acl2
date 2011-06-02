; ACL2 Version 4.2 -- A Computational Logic for Applicative Common Lisp
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

(defdoc parallelism
  ":Doc-Section Parallelism

  experimental extension for evaluating forms in parallel~/

  This documentation topic relates to an experimental extension of ACL2,
  created initially by David L. Rager.  ~l[parallelism-build] for how to build
  an executable image that supports parallel evaluation.  Also see
  ~c[books/parallel] for examples.

  One of ACL2's strengths lies in its ability to execute industrial models
  efficiently.  The ACL2 source code provides an experimental parallel
  evaluation capability that can increase the speed of explicit evaluation,
  including simulator runs using such models, and it can also decrease the time
  required for proofs that make heavy use of the evaluation of ground terms.

  The parallelism primitives are ~ilc[plet], ~ilc[pargs], ~ilc[pand], and
  ~ilc[por].  ~ilc[Pand] and ~ilc[por] terminate early when an argument is
  found to evaluate to ~c[nil] or non-~c[nil], respectively, thus potentially
  improving on the efficiency of lazy evaluation.~/

  The above four parallelism primitives allow for limiting parallel evaluation
  (spawning of so-called ``threads'') depending on resource availability.
  Specifically, the primitives allow specification of a size condition to
  control the granularity under which threads are allowed to spawn.  You can
  use such granularity declarations in recursively-defined functions to
  implement data-dependent parallelism in their execution.

  We recommend that in order to learn to use the parallelism primitives, you
  begin by reading examples: ~pl[parallelism-tutorial].  That section will
  direct you to further documentation topics.

  While we aim to support Clozure Common Lisp (CCL), Steel Bank Common
  Lisp (SBCL), and Lispworks, SBCL and Lispworks both currently sometimes
  experience problems when evaluating the ACL2 proof process (the
  ``waterfall'') in parallel.  Therefore, CCL is the recommend Lisp for anyone
  that wants to use parallelism and isn't working on fixing those problems.")

; Parallelism wart: complete the following documentation topic for compiling
; with #+acl2-par.  Link to it from :doc parallelism (and maybe elsewhere).

(defdoc compiling-acl2p

  ":Doc-Section ACL2::Parallelism

  compiling ACL2(p)~/

  The command below will compile ACL2 to support parallel execution, including
  parallel execution during proofs.  Any non-empty string may be used in place
  of ~c[t], and the value of ~c[LISP] (shown here as ~c[ccl]) is any Lisp
  executable on which one can build ACL2(p) (~pl[parallelism]).
  ~bv[]
  make ACL2_PAR=t LISP=ccl
  ~ev[]~/~/")

; Parallelism wart: need to add a doc topic on what's not currently supported
; inside the parallelized waterfall.

(defdoc parallel

; Just in case someone types :doc parallel!

  ":Doc-Section Parallelism

  evaluating forms in parallel~/

  ~l[parallelism].~/~/")

(defdoc parallelism-build

; Keep this documentation in sync with the acl2-par error in acl2-init.lisp.

  ":Doc-Section Parallelism

  building an ACL2 executable with parallel evaluation enabled~/

  ~l[parallel] and ~pl[parallelism-tutorial] for an introduction to parallel
  evaluation in ACL2 using parallelism primitives ~ilc[pand], ~ilc[por],
  ~ilc[plet], and ~ilc[pargs].

  You can build an experimental version of ACL2 that supports parallel
  evaluation in the following host Common Lisp implementations:
  ~bq[]
  * CCL (OpenMCL)

  * SBCL with threads (feature ~c[:sb-thread])~eq[]

  An easy way is to build an executable supporting parallel evaluation is to
  include the following with a ~c[make] command:
  ~bv[]
  ACL2_PAR=p
  ~ev[]
  So for example, to make an executable image and also documentation (which
  will appear in subdirectories ~c[doc/EMACS] and ~c[doc/HTML]):
  ~bv[]
  make large DOC ACL2_PAR=p
  ~ev[]~/~/")

(defun set-parallel-evaluation-fn (val ctx state)
  (declare (xargs :guard (member-eq val '(t nil :bogus-parallelism-ok))))
  (cond
   ((eq (f-get-global 'parallel-evaluation-enabled state)
        val)
    (pprogn (observation ctx
                         "No change in enabling of parallel evaluation.")
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
         primitives at the top level when parallel evaluation is disabled, ~
         although they will not result in any parallel evaluation.~%")
    #+acl2-par
    (let ((observation-string
           (case val
             ((nil)
              "Disabling parallel evaluation.  Parallelism primitives may ~
               still be used, but during evaluation they will degrade to ~
               their serial equivalents.")
             ((t)
              "Parallel evaluation is enabled, but parallelism primitives may ~
               only be called within function definitions or macro top-level, ~
               not at the top level of the ACL2 read-eval-print loop.  See ~
               :DOC parallelism-at-the-top-level.")
             (otherwise ; :bogus-parallelism-ok
              "Parallel evaluation is enabled.  Parallelism primitives may be ~
               called directly in the top-level loop, but without use of the ~
               macro top-level, they will execute serially.  See :DOC ~
               parallelism-at-the-top-level."))))
      (pprogn
       (f-put-global 'parallel-evaluation-enabled val state)
       (observation ctx observation-string)
       (value val))))))

(defmacro set-parallel-evaluation (value)

; Parallelism wart: Should we add spec-mv-let to this doc topic?

  ":Doc-Section Parallelism

  enabling or disabling parallel evaluation for parallelism primitives~/

  ~l[parallel] and ~pl[parallelism-tutorial] for an introduction to parallel
  evaluation in ACL2 using parallelism primitives ~ilc[pand], ~ilc[por],
  ~ilc[plet], and ~ilc[pargs].

  ~bv[]
  General Forms:
  (set-parallel-evaluation nil) ; default for images not built for parallelism
  (set-parallel-evaluation t)   ; default for images built for parallelism
  (set-parallel-evaluation :bogus-parallelism-ok)
  ~ev[]
  ~/

  ~c[Set-parallel-evaluation] takes an argument that specifies the enabling or
  disabling of ~il[parallel] evaluation.  However, calls of parallelism
  primitives made explicitly in the ACL2 top-level loop, as opposed to inside
  function bodies, will never cause parallel evaluation;
  ~pl[parallelism-at-the-top-level].  Parallel evaluation is determined by the
  value of the argument to ~c[set-parallel-evaluation], as follows.

  Value ~c[t]:~nl[]
  All parallelism primitives used in bodies of function definitions are given
  the opportunity to execute in parallel.  However, the use of parallelism
  primitives directly in the ACL2 top-level loop causes an error.

  Value ~c[:bogus-parallelism-ok]:~nl[]
  Parallel evaluation is enabled, as for value ~c[t].  However, the use of
  parallelism primitives directly in the ACL2 top-level loop does not cause an
  error, but rather, simply results in serial evaluation for these primitives.

  Value ~c[nil]:~nl[]
  All parallelism primitives will degrade to their serial equivalents, include
  their calls made directly in the ACL2 top-level loop, which does not cause an
  error.~/"

  (declare (xargs :guard (member-equal value
                                       '(t 't nil 'nil
                                           :bogus-parallelism-ok
                                           ':bogus-parallelism-ok))))
  `(let ((val ,value)
         (ctx 'set-parallel-evaluation))
     (set-parallel-evaluation-fn
      (cond ((consp val) (cadr val))
            (t val))
      ctx
      state)))

(defconst *waterfall-parallelism-values*
  '(nil :full :top-level :resource-based :pseudo-serial))

(defun waterfall-printing-value-for-parallelism-value (value)

; Warning: Keep guard in sync with guard of set-waterfall-parallelism-fn.

  (declare (xargs :guard (member-eq value *waterfall-parallelism-values*)))
  (cond ((eq value nil)
         :full)
        ((eq value :full)
         :limited)
        ((eq value :top-level)
         :limited)
        ((eq value :resource-based)
         :limited)
        (t 
         (assert$ (eq value :pseudo-serial)
                  :limited))))

; Parallelism wart: either support the reading of state by computed hints, or
; explicitly disallow it with a user-friendly error message; modify :doc
; unsupported-waterfall-parallelism-features accordingly.

; Parallelism wart: figure out if :bdd hints are supported.  Given the call of
; error-in-parallelism-mode@par in waterfall-step, it seems that they might not
; be; yet, regressions may have passed with them.  One possible outcome: If
; books/bdd/ tests fail, you might just modify translate-bdd-hint to cause a
; nice error if watefall parallelism is enabled, and also mention that (once
; again) in :doc unsupported-waterfall-parallelism-features.

(defdoc unsupported-waterfall-parallelism-features

; For a discussion of the wormhole issue referenced in the :doc string below,
; see waterfall-print-clause-id@par.

  ":Doc-Section ACL2::Parallelism

  proof features not supported with waterfall-parallelism enabled~/

  For a general introduction to ACL2(p), an experimental extension of ACL2 that
  supports parallel execution and proof, ~pl[parallelism].  Please note that
  although this extension is usable and, we hope, robust in its behavior, there
  are still known issues to address beyond those listed explicitly below.  For
  example, esoteric ``invalid speculation'' messages may appear.

  Below we list proof features of ACL2 that are not yet supported when parallel
  execution is enabled for the primary ACL2 proof process, generally known as
  ``the Waterfall'', typically by calling ~ilc[set-waterfall-parallelism].

  Please note that this topic is limited to the case that such waterfall
  parallelism is enabled.  We believe that all ACL2 proof procedures are
  supported when waterfall parallelism is disabled, even in executables that
  support parallelism (~pl[compiling-acl2p]).

  While we support ~il[clause-processor]s, we do not support those that modify
  ~il[state].  At this time, such an attempt to modify ~il[state] may result in
  a sub-optimal error message.

  Computed hints are supported, as long as they don't modify ~il[state].
  Computed hints may in principle read ~il[state], but support for such hints
  may be incomplete.

  ~il[Custom-keyword-hints] are unsupported, though they may work on occasion.

  GNU Make versions 3.81 and 3.82 used to cause a lot of problems (version 3.80
  somewhat less so), at least on Linux, when certifying books with CCL using
  ~c[make] (~pl[book-makefiles].  CCL was updated around March 23, 2011 to fix
  this problem, so if you get segfaults (for example), try updating your CCL.

  The standard process for book certification will not use
  waterfall-parallelism (~pl[set-waterfall-parallelism]), which is disabled by
  default.  ~l[book-makefiles], which explains that ~il[acl2-customization]
  files are ignored during that process unless specified explicitly on the
  command line or in the environment.

  Proof output can contain repeated printing of the same subgoal name.

  ~il[Gag-mode] isn't supported.  However, ACL2(p) also prints key checkpoints
  (for example ~pl[introduction-to-key-checkpoints]), but with a notion of
  ``key checkpoint'' that does not take into account whether the goal is later
  proved by induction.

  The ~c[:]~ilc[brr] utility is not supported.

  Time limits (~pl[with-prover-time-limit]) aren't supported.

  The use of ~ilc[wormhole]s is not recommended, as there may be race
  conditions.

  If the host Lisp is Lispworks, you may see messages about misaligned conses.
  The state of the system may be corrupted after such a message has been
  printed.~/~/")

(defun set-waterfall-parallelism-fn (val state)

; Warning: Keep guard in sync with guard of
; waterfall-printing-value-for-parallelism-value.

; Parallelism wart: perhaps change the wording to make it more obvious that
; there are two settings involved here, waterfall-parallelism and
; waterfall-printing.

  (declare (xargs :guard (member-eq val *waterfall-parallelism-values*)))
  (let ((printing-value
         (waterfall-printing-value-for-parallelism-value val)))
    (cond
     ((and (eq (f-get-global 'waterfall-parallelism state)
               val)
           (eq (f-get-global 'waterfall-printing state)
               printing-value))
      (pprogn (observation nil "No change in waterfall parallelism or ~
                                waterfall printing.")
              (value val)))
     #-acl2-par
     (val
      (er soft 'set-waterfall-parallelism-fn
          "Parallelism can only be enabled in CCL, threaded SBCL, or ~
           Lispworks.  Additionally, the feature :ACL2-PAR must be set when ~
           compiling ACL2 (for example, by using `make' with argument ~
           `ACL2_PAR=t').  Either the current Lisp is neither CCL nor ~
           threaded SBCL nor Lispworks, or this feature is missing.  ~
           Consequently, parallel evaluation of the waterfall will remain ~
           disabled."))
     (t
      (let ((observation-string
             (case val
               ((nil)
                "Disabling parallel evaluation of the waterfall.  Setting ~
                 waterfall-printing to ~x0 (see :DOC set-waterfall-printing).")
               (:full
                "Parallelizing the proof of every subgoal.  Setting ~
                 waterfall-printing to ~x0 (see :DOC set-waterfall-printing).")
               (:top-level
                "Parallelizing the proof of top-level subgoals only.  Setting ~
                 waterfall-printing to ~x0 (see :DOC set-waterfall-printing).")
               (:pseudo-serial
                "Running the version of the waterfall prepared for parallel ~
                 execution (stateless). However, we will evaluate this ~
                 version of the waterfall serially.  Setting ~
                 waterfall-printing to ~x0 (see :DOC set-waterfall-printing).")
               (otherwise ; :resource-based
                "Parallelizing the proof of every subgoal, as long as CPU ~
                 core resources are available.  Setting waterfall-printing to ~
                 ~x0 (see :DOC set-waterfall-printing)."))))
        (pprogn
         (f-put-global 'waterfall-parallelism val state)
         (f-put-global 'waterfall-printing printing-value state)
         (observation nil observation-string printing-value)
         (value val)))))))

; Parallelism wart: consider adding a :doc topic for waterfall-printing and
; waterfall-parallelism that just point to set-waterfall-printing and
; set-waterfall-parallelism, respectively.

(defmacro set-waterfall-parallelism (value)

  ":Doc-Section Parallelism

  configuring the parallel evaluation of the waterfall~/

  ~bv[]
  General Forms:
  (set-waterfall-parallelism nil) ; serial evaluation
  (set-waterfall-parallelism :full)   ; always parallelize
  (set-waterfall-parallelism :top-level) ; parallelize top-level subgoals
  (set-waterfall-parallelism :resource-based) ; parallelize all subgoals, but
                                              ; only when resources are 
                                              ; available
  (set-waterfall-parallelism :pseudo-serial)  ; serial evaluation of the
                                              ; version of the waterfall made
                                              ; for parallel execution
                                              ; useful for debugging
  ~ev[]
  ~/

  ~c[Set-waterfall-parallelism] takes an argument that specifies the enabling or
  disabling of ~il[parallel] evaluation of ACL2's main proof process, the
  waterfall.

  It also sets state global ~c[waterfall-printing] to an appropriate value.
  ~l[set-waterfall-printing].

  Note that not all ACL2 features are supported when waterfall-parallelism is
  set to non-nil.~/"

; Parallelism wart: add a reference to
; unsupported-waterfall-parallelism-features, above.

; Parallelism wart: rename :psuedo-serial to :pseudo-parallel.

  (declare (xargs :guard
                  (or (member-eq value *waterfall-parallelism-values*)
                      (and (consp value)
                           (eq (car value) 'quote)
                           (consp (cdr value))
                           (null (cddr value))
                           (member-eq (cadr value)
                                      *waterfall-parallelism-values*)))))
  `(let ((val ,value))
     (set-waterfall-parallelism-fn
      (cond ((consp val) (cadr val))
            (t val))
      state)))

(defun set-waterfall-printing-fn (val state)
  (declare (xargs :guard (member-eq val '(:full :limited))))
  (cond
   ((eq (f-get-global 'waterfall-printing state)
        val)
    (pprogn (observation nil "No change in waterfall printing.")
            (value nil)))
   (val
    (er soft 'set-waterfall-printing-fn
        "Customizing waterfall printing only makes sense in the #+ac2l-par ~
         builds of ACL2.  Consequently, the waterfall-printing option will ~
         remain unchanged."))
   (t
    (pprogn
     (f-put-global 'waterfall-printing val state)
     (observation nil "Setting waterfall-printing to ~x0." val)
     (value val)))))

(defmacro set-waterfall-printing (value)

  ":Doc-Section Parallelism

  configuring the printing that occurs within the parallelized waterfall~/

  ~bv[]
  General Forms:
  (set-waterfall-printing :full)    ; print everything
  (set-waterfall-printing :limited) ; print a subset that's thought to be useful
  ~ev[]
  ~/

  ~c[Set-waterfall-printing] takes an argument that indicates how much
  printing should occur when executing ACL2 with the parallelized version of the
  waterfall.  It only affects the printing that occurs when parallelism mode is
  enabled for the waterfall (~pl[set-waterfall-parallelism]).
  ~/"

  (declare (xargs :guard (member-equal value
                                       '(:full ':full
                                               :limited ':limited))))
  `(let ((val ,value))
     (set-waterfall-printing-fn
      (cond ((consp val) (cadr val))
            (t val))
      state)))

(defdoc parallelism-at-the-top-level
  ":Doc-Section Parallelism

  parallel evaluation in the ACL2 top-level loop~/

  Calls of parallelism primitives made explicitly in the ACL2 top-level loop,
  as opposed to inside function bodies, will never cause parallel evaluation.
  Such calls will either execute with serial evaluation or will cause an error;
  ~pl[set-parallel-evaluation].~/

  Consider for example the following call of ~ilc[pargs] in the ACL2
  top-level loop.  Instead of executing ~c[pargs], ACL2 macroexpands away this
  call, leaving us with serial evaluation of the arguments to the ~ilc[cons]
  call, or else causes an error (~pl[set-parallel-evaluation]).  If there is no
  error, then
  ~bv[]
  (pargs (cons (expensive-fn-1 4) (expensive-fn-2 5)))
  ~ev[]
  expands into:
  ~bv[]
  (cons (expensive-fn-1 4) (expensive-fn-2 5))
  ~ev[]

  One trivial way to enable parallel evaluation of a form is to surround it
  with a call to macro ~il[top-level].  Consider the following example.
  ~bv[]
  (top-level (pargs (cons (expensive-fn-1 4) (expensive-fn-2 5))))
  ~ev[]
  Then in an executable image that supports parallel evaluation ~-[]
  ~pl[parallelism-build] for instructions on how to build such an executable
  ~-[] ~c[(expensive-fn-1 4)] and ~c[(expensive-fn-2 5)] can evaluate in 
  parallel.

  A second way to enable parallel evaluation of a form is to place it 
  inside a function body.  For example, consider the following definition.
  ~bv[]
  (defun foo (x y)
    (pargs (cons (expensive-fn-1 x) (expensive-fn-2 y))))
  ~ev[]
  Then in an executable image that supports parallel evaluation, submission of
  the form ~c[(foo 4 5)] can cause parallel evaluation of 
  ~c[(expensive-fn-1 4)] and ~c[(expensive-fn-2 5)].

  Note that ~il[guard]s need not be verified in order to obtain ~il[parallel]
  evaluation.  The only restrictions on parallel evaluation are to use an
  executable supporting it, to avoid calling parallelism primitives directly in
  the top-level loop, to have sufficient resources (especially, threads)
  available, and to avoid explicitly disabling parallel evaluation
  ~pl[set-parallel-evaluation]).~/")

(defdoc parallelism-tutorial
  ":Doc-Section Parallelism

  a tutorial on how to use the parallelism library.~/

  In this topic we introduce the ACL2 parallelism primitives using the example
  of a doubly-recursive Fibonacci function, whose basic definition is as
  follows.  ~l[parallelism ] for a very high-level summary of the parallelism
  capability described here, and ~pl[parallelism-build] for how to build an
  executable image that supports parallel evaluation.  Here, we assume that
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
  ~ilc[pargs] calls that can result in parallel evaluation.  For example, if
  the ACL2 limit is k and each call of ~ilc[pargs] actually spawns threads for
  evaluating  its arguments, then
  after k ~c[cdr]s there will be no further parallel evaluation.

  Possible solutions may include reworking of algorithms (for example to be
  tree-based rather than list-based) or using appropriate granularity forms.
  We hope that future implementations will allow thread ``re-deployment'' in
  order to mitigate this problem.

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
  ":Doc-Section Parallelism
  limit the amount of parallelism~/

  Some function calls are on arguments whose evaluation time is long enough to
  warrant parallel evaluation, while others are not.  A granularity form can be
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
  ":Doc-Section Parallelism
  performance issues for parallel evaluation~/

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
  (set-parallel-evaluation nil)
  (time$ (length (sets::pmergesort-exec *x* 0)))
  ~ev[]~/~/")

; Parallelism wart: Add a section on waterfall-parallelism-performance.  It
; should be a discussion of the advantages of each argument to
; set-waterfall-parallelism.

(defdoc early-termination
  ":Doc-Section Parallelism
  early termination for ~ilc[pand] and ~ilc[por].~/~/

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
  ":Doc-Section Parallelism

  parallel evaluation of arguments in a function call~/

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
  ":Doc-Section Parallelism

  parallel version of ~ilc[let]~/

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

  ":Doc-Section Parallelism

  parallel, Boolean version of ~ilc[and]~/

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
  timing of thread creation, and whether or not parallel evaluation is enabled
  (~pl[set-parallel-evaluation]).

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

  ":Doc-Section Parallelism

  parallel, Boolean version of ~ilc[or]~/

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

; We conclude with two functions defined also in parallel-raw.lisp; but see
; comments below before deleting these!

#+(or acl2-loop-only (not acl2-par))
(defun or-list (x)

; Warning: This function is needed in books/clause-processors/equality.lisp,
; which however cannot define it redundantly because it is in
; *primitive-logic-fns-with-raw-code*.  So do not delete this definition even
; though it is in parallel-raw.lisp!

  (declare (xargs :guard (true-listp x) :mode :logic))
  (if (endp x)
      nil
    (if (car x)
        t
        (or-list (cdr x)))))

#+(or acl2-loop-only (not acl2-par))
(defun and-list (x)

; Warning: This function is needed in books/clause-processors/equality.lisp,
; which however cannot define it redundantly because it is in
; *primitive-logic-fns-with-raw-code*.  So do not delete this definition even
; though it is in parallel-raw.lisp!

  (declare (xargs :guard (true-listp x) :mode :logic))
  (if (endp x)
      t
    (and (car x)
         (and-list (cdr x)))))

(defun cpu-core-count (state)

  ":Doc-Section ACL2::Programming

  the number of cpu cores~/

  Unless the ACL2 executable supports parallel evaluation (~pl[parallelism]),
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
  #+acl2-loop-only
  (mv-let (nullp val state)
          (read-acl2-oracle state)
          (declare (ignore nullp))
          (mv val state))
  #+(and (not acl2-loop-only) (not acl2-par))
  (mv 1 state)
  #+(and (not acl2-loop-only) acl2-par)
  (mv (if (and (f-boundp-global 'cpu-core-count state)
               (posp (f-get-global 'cpu-core-count state)))
          (core-count-raw nil (f-get-global 'cpu-core-count state))
        (core-count-raw 'core-count))
      state))

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

; Parallelism wart: Document spec-mv-let.  One can use plet/pargs/pand/por as
; starting points for the format.

; Parallelism wart: I want to switch the true and false branches.

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
                       (check-vars-not-free ,bindings ,true-branch)
                     (mv?-let ,bindings
                              ,computation
                              ,false-branch)))))))))
