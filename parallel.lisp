; ACL2 Version 8.4 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

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
;   zero-ary functions).  If you consider making such a change, then think
;   about how functions cpu-core-count and cpu-core-count-raw might be
;   relevant.

;   Modify the coefficient (currently 2) in the definition of
;   *unassigned-and-active-work-count-limit*.  Evaluate such modifications with
;   testing, of course.

; End of Section "To Consider".

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

(defun waterfall-printing-value-for-parallelism-value (value)
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
; tests fail for contributed book directory books/bdd/, you might just modify
; translate-bdd-hint to cause a nice error if waterfall parallelism is enabled,
; and also mention that (once again) in :doc
; unsupported-waterfall-parallelism-features.  Note that bdd-clause might be
; the function that actually performs the bdd hint, and that bdd-clause doesn't
; return state.  So, aside from the place in waterfall-step, bdd hints might be
; fine.

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

; Keep the following ending "~%" in sync with set-waterfall-parallelism.

    (observation nil
                 "~@0  Setting waterfall-parallelism to ~s1.  Setting ~
                  waterfall-printing to ~s2 (see :DOC ~
                  set-waterfall-printing).~%"
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
           by calling ~x0.  (2) can be achieved by calling ~x1."
          '(set-override-hints nil)
          '(set-waterfall-parallelism-hacks-enabled t)))
     (t (value nil)))))

(defun set-waterfall-parallelism-fn (val ctx state)
  (cond
   ((eq val (f-get-global 'waterfall-parallelism state))
    (pprogn (observation ctx
                         "Ignoring call to set-waterfall-parallelism since ~
                          the new value is the same as the current value.~%~%")
            (value :ignored)))
   (t
    (let ((val (if (eq val t) ; t is a alias for :resource-based
                   :resource-based
                 val)))
      (er-progn

; We check for override hints even when #-acl2-par, to avoid being surprised by
; an error when the same proof development is encountered with #+acl2-par.  But
; we skip the check if there is no change (see GitHub Issue #1171) or we are
; turning off waterfall-parallelism.

       (cond ((or (null val)
                  (equal val (f-get-global 'waterfall-parallelism state)))
              (value nil))
             (t (check-for-no-override-hints ctx state)))
       (cond
        ((member-eq val *waterfall-parallelism-values*)
         #+acl2-par
         (cond
          ((null (f-get-global 'parallel-execution-enabled state))
           (er soft ctx
               "Parallel execution must be enabled before enabling ~
                  waterfall parallelism.  See :DOC set-parallel-execution"))
          ((and val (f-get-global 'gstackp state))
           (er soft ctx
               "You must disable brr (e.g., with :BRR NIL) before turning ~
                  on waterfall-parallelism.  See :DOC ~
                  unsupported-waterfall-parallelism-features."))
          (t

; One might be tempted to insert (mf-multiprocessing val) here.  However, in
; ACL2(hp) -- which is where this code is run -- we really want to keep
; multiprocessing on, since one can do multithreaded computations (e.g., with
; pand) even with waterfall-parallelism disabled.

           (progn$
            (and val

; We avoid a possible hard error, e.g. from (mini-proveall), when parallelism
; and accumulated-persistence are both turned on.  A corresponding bit of code
; is in accumulated-persistence.  We do similarly, just to be safe, for
; forward-chaining-reports; see also set-fc-criteria-fn.

; Warning: Keep the following two wormhole-eval calls in sync with the
; definitions of accumulated-persistence and set-fc-criteria-fn.

                 (prog2$ (wormhole-eval
                          'accumulated-persistence
                          '(lambda (whs) (set-wormhole-data whs nil))
                          nil)
                         (wormhole-eval
                          'fc-wormhole
                          '(lambda (whs)
                             (set-wormhole-data
                              whs
                              (put-assoc-eq :CRITERIA nil
                                            (wormhole-data whs))))
                          nil)))
            #-acl2-loop-only
            (funcall ; avoid undefined function warning
             'initialize-dmr-interval-used)
            (pprogn
             (f-put-global 'waterfall-parallelism val state)
             (value val)))))
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
                          example, by using `make' with argument ~
                          `ACL2_PAR=t'). ~ Either the current Lisp is neither ~
                          CCL nor threaded SBCL nor Lispworks, or this ~
                          feature is missing.  Consequently, this attempt to ~
                          set waterfall-parallelism to ~x0 will be ~
                          ignored.~%~%"
                       val)
          (value :ignored)))
        (t (er soft ctx
               "Illegal value for set-waterfall-parallelism: ~x0.  The legal ~
                values are ~&1."
               val *waterfall-parallelism-values*))))))))

; Parallelism blemish: make a macro via deflast called
; with-waterfall-parallelism that enables waterfall parallelism for a given
; form, in particular an event form like calls of defun and defthm.  It's low
; priority, since it can easily be added as a book later -- though maybe it
; would be nice to have this as an event constructor, like with-output.  But
; while doing proofs with ACL2(hp), Rager would have found this convenient.

(defmacro set-waterfall-parallelism1 (val)
  `(let* ((val ,val)
          (ctx 'set-waterfall-parallelism))
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
                    (value (list val print-val))))))))))

(table saved-memoize-table nil nil
       :guard

; It is tempting to install a table guard of (memoize-table-chk key val world).
; However, that won't work, for example because it will prohibit adding an
; entry to this table for a function that is currently memoized -- an act that
; is the point of this table!  So instead we rely solely on the checks done
; when putting entries in memoize-table.

       t)

(defmacro save-memo-table ()
  '(with-output
    :off (summary event)
    (table saved-memoize-table
           nil
           (table-alist 'memoize-table world)
           :clear)))

(defun clear-memo-table-events (alist acc)
  (declare (xargs :guard (true-list-listp alist)))
  (cond ((endp alist) acc)
        (t (clear-memo-table-events
            (cdr alist)
            (cons `(table memoize-table ',(caar alist) nil)
                  acc)))))

(defmacro clear-memo-table ()
  `(with-output
    :off (summary event)
    (make-event
     (let ((alist (table-alist 'memoize-table (w state))))
       (cons 'progn
             (clear-memo-table-events alist nil))))))

(defmacro save-and-clear-memoization-settings ()
  '(with-output
    :off (summary event)
    (progn (save-memo-table)
           (clear-memo-table))))

(defun set-memo-table-events (alist acc)
  (declare (xargs :guard (true-list-listp alist)))
  (cond ((endp alist) acc)
        (t (set-memo-table-events
            (cdr alist)
            (cons `(table memoize-table ',(caar alist) ',(cdar alist))
                  acc)))))

(defmacro restore-memoization-settings ()
  `(with-output
    :off (summary event)
    (make-event
     (let ((alist (table-alist 'saved-memoize-table (w state))))
       (cons 'progn
             (set-memo-table-events alist nil))))))

(defmacro set-waterfall-parallelism (val)
  `(with-output
    :off (summary event)
    (make-event
     (er-let*
         ((new-val (set-waterfall-parallelism1 ,val)))
       (value (list 'value-triple (list 'quote new-val)))))))

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

  (declare (xargs :guard (or (equal val t) (null val))))
  `(table waterfall-parallelism-table 'hacks-enabled ,val))

(defmacro set-waterfall-parallelism-hacks-enabled! (val)
  `(encapsulate
    ()

; Parallelism blemish: the following installation of ttag
; :waterfall-parallelism-hacks should probably be conditionalized upon val
; being equal to t.  Furthermore, perhaps the installation should also be
; conditionalized upon the non-existence of a prior ttag.

    (defttag :waterfall-parallelism-hacks)
    (set-waterfall-parallelism-hacks-enabled ,val)))

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

; Preliminary code for parallelizing the rewriter.

; Note that the following code treats step-limits a little differently from how
; they are treated in the sequential version.  If we keep this treatment, we
; should add a comment here and in decrement-step-limit suggesting that if we
; change either, then we should consider changing the other.  Also note the
; commented out declare forms, which would be good to include (especially
; important for GCL) once spec-mv-let accepts them.  And finally, note that as
; of v6-2, it is necessary to unmemoize the rewriter functions when running the
; rewriter in parallel in ACL2(hp) because memoization is not thread-safe.
; This unmemoization can perhaps be done by issuing a call of (unmemoize-all)
; in raw Lisp).

; (defun rewrite-args (args alist bkptr; &extra formals
;                           rdepth step-limit
;                           type-alist obj geneqv wrld state fnstack ancestors
;                           backchain-limit
;                           simplify-clause-pot-lst rcnst gstack ttree)
;
; ; Note: In this function, the extra formal geneqv is actually a list of geneqvs
; ; or nil denoting a list of nil geneqvs.
;
;   (declare (type (unsigned-byte 29) rdepth)
;            (type (signed-byte 30) step-limit))
;   (the-mv
;    3
;    (signed-byte 30)
;    (cond ((null args)
;           (mv step-limit nil ttree))
;          (t (spec-mv-let
;              (step-limit1 rewritten-arg ttree1)
; ;            (declare (type (signed-byte 30) step-limit1))
;              (rewrite-entry (rewrite (car args) alist bkptr)
;                             :geneqv (car geneqv))
;              (mv-let
;                (step-limit2 rewritten-args ttree2)
;                (rewrite-entry (rewrite-args (cdr args) alist (1+ bkptr))
;                               :geneqv (cdr geneqv))
; ;              (declare (type (signed-byte 30) step-limit2))
;                (if t
;                    (mv (let* ((steps1 (- step-limit step-limit1))
;                               (step-limit (- step-limit2 steps1)))
;                          (declare (type (signed-byte 30) steps1 step-limit))
;                          (cond ((>= step-limit 0)
;                                 step-limit)
;                                ((step-limit-strictp state)
;                                 (step-limit-error nil))
;                                (t -1)))
;                        (cons rewritten-arg rewritten-args)
;                        (cons-tag-trees ttree1 ttree2))
;                  (mv 0
;                      nil
;                      nil))))))))

#+(or acl2-loop-only (not acl2-par))
(defmacro spec-mv-let (&whole spec-mv-let-form outer-vars computation body)

; Warning: Keep this in sync with the raw Lisp #+acl2-par definition of
; spec-mv-let.

; From the documentation, with annotations in brackets [..] showing names used
; in the code below:

;   (spec-mv-let
;    (v1 ... vn)  ; bind distinct variables
;    <spec>       ; evaluate speculatively; return n values
;    (mv-let      ; [inner-let] or, use mv?-let if k=1 below
;     (w1 ... wk) ; [inner-vars] bind distinct variables
;     <eager>     ; [evaluate eagerly
;     (if <test>  ; [test] use results from <spec> if true
;         <typical-case> ; [true-branch] may mention v1 ... vn
;       <abort-case>)))  ; [false-branch] does not mention v1 ... vn

; In the logic, spec-mv-let is just mv?-let where the inner binding is also to
; be done with mv-let, but capture needs to be avoided in the following sense:
; no vi may occur in <test> or <abort-case>, because in the raw Lisp version,
; those values may not be available for those forms.

  (case-match body
    ((inner-let inner-vars inner-body
                ('if test true-branch false-branch))
     (cond
      ((not (member inner-let '(mv-let mv?-let mv-let@par)
                    :test 'eq))
       (er hard! 'spec-mv-let
           "Illegal form (expected inner let to bind with one of ~v0): ~x1. ~ ~
            See :doc spec-mv-let."
           '(mv-let mv?-let mv-let@par)
           spec-mv-let-form))
      ((or (not (symbol-listp outer-vars))
           (not (symbol-listp inner-vars))
           (intersectp inner-vars outer-vars
                       :test 'eq))
       (er hard! 'spec-mv-let
           "Illegal spec-mv-let form: ~x0.  The two bound variable lists ~
            must be disjoint true lists of variables, unlike ~x1 and ~x2.  ~
            See :doc spec-mv-let."
           spec-mv-let-form
           inner-vars
           outer-vars))
      (t
       `(check-vars-not-free

; Warning: Keep the check for variable name "the-very-obscure-feature" in sync
; with the variable name in the raw Lisp version.

         (the-very-obscure-future)

; We lay down code that treats spec-mv-let as mv?-let, augmented by some
; necessary checks.  The raw Lisp code has a different shape in order to
; support speculative execution, and possible aborting, of the (speculative)
; computation.

         (mv?-let
          ,outer-vars
          ,computation
          (,inner-let
           ,inner-vars
           ,inner-body
           (cond ((check-vars-not-free ,outer-vars ,test)
                  ,true-branch)
                 (t
                  (check-vars-not-free ,outer-vars ,false-branch)))))))))
    (& (er hard! 'spec-mv-let
           "Illegal form, ~x0.  See :doc spec-mv-let."
           spec-mv-let-form))))

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

; The definition of with-output-lock can be found as (deflock <comments>
; *output-lock*) in ACL2 source file axioms.lisp.

; Parallelism wart: it is still possible in ACL2(p) to receive an error at the
; Lisp-level when CCL cannot "create thread".  An example of a user (Kaufmann)
; encountering this error is shown below, with community book
; concurrent-programs/bakery/stutter2.  In March 2012, Kaufmann's laptop could
; sometimes exhibit this problem (a 2-core machine with 4 hardware threads).
; There are two possible ways to fix this problem.  The first is to set the
; default-total-parallelism-work-limit to a lower number so that it never
; occurs (but this costs performance).  Kaufmann suggests that we should also
; catch this particular Lisp error and instead cause an ACL2 error, similar to
; the error in function not-too-many-futures-already-in-existence.  This may be
; harder than one might initially think, because our current mechanism for
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

  (declare (xargs :guard (or (equal val t)
                             (null val))))
  `(set-total-parallelism-work-limit-error-fn ,val state))
