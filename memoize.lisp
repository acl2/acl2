; ACL2 Version 6.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2013, Regents of the University of Texas

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

; memoize.lisp -- Logical definitions for memoization functions, only
; to be included in the experimental HONS version of ACL2.

; The original version of this file was contributed by Bob Boyer and
; Warren A. Hunt, Jr.  The design of this system of Hash CONS,
; function memoization, and fast association lists (applicative hash
; tables) was initially implemented by Boyer and Hunt.

(in-package "ACL2")

(defmacro defn (f a &rest r)
  `(defun ,f ,a (declare (xargs :guard t)) ,@r))

(defmacro defnd (f a &rest r)
  `(defund ,f ,a (declare (xargs :guard t)) ,@r))

#+(or acl2-loop-only (not hons))
(defn clear-memoize-table (fn)
  fn)

#+(or acl2-loop-only (not hons))
(defn clear-memoize-tables ()
  nil)

#+(or acl2-loop-only (not hons))
(defn memoize-summary ()
  nil)

#+(or acl2-loop-only (not hons))
(defn clear-memoize-statistics ()
  nil)

(defmacro memsum ()
  '(memoize-summary))

; The macros MEMOIZE-ON and MEMOIZE-OFF typically cause "under the hood"
; effects that, though not changing the semantics of what ACL2 returns, may
; affect the speed and/or space utilization of the computation.

; The functions memoize and unmemoize have rather innocent looking
; semantics.  But under the hood, they enable and disable memoization.
; The function memoize might cause errors due to compilation problems.

(defconst *hons-primitive-fns*
  ;; This affects acl2-exports, maybe other stuff
  '(hons-copy
    hons
    hons-equal
    hons-equal-lite
    hons-clear
    hons-wash
    hons-summary
    hons-resize-fn
    get-slow-alist-action
    hons-get
    hons-acons
    hons-acons!
    hons-shrink-alist
    hons-shrink-alist!
    fast-alist-len
    fast-alist-free
    fast-alist-summary
    cons-subtrees
    number-subtrees
    clear-hash-tables
    flush-hons-get-hash-table-link
    ;; from memoize.lisp
    clear-memoize-table
    clear-memoize-tables
    memoize-summary
    clear-memoize-statistics))

(defconst *hons-primitives*
  ;; hons-related macros and primitive fns
  (append '(hons-resize
            set-slow-alist-action
            memoize
            unmemoize
            memoize-on
            memoize-off
            memsum)
          *hons-primitive-fns*))

(defconst *mht-default-size* 60)

(defun memoize-form (fn
                     condition
                     condition-p
                     condition-fn
                     hints
                     otf-flg
                     inline
                     trace
                     commutative
                     forget
                     memo-table-init-size
                     aokp
                     ideal-okp)

; Jared Davis suggests that we consider bundling up these 13 parameters, for
; example into an alist.  He says: "Various subsets of these arguments occur in
; spaghetti fashion throughout the code for memoize, add-trip, the
; memoize-table stuff, etc."

  (declare (xargs :guard t))
  (let ((condition (cond ((equal condition ''t) t)
                         ((equal condition ''nil) nil)
                         (t condition))))
    (cond
     ((and condition-fn (null condition-p))
      `(progn (table memoize-table
                     (deref-macro-name ,fn (macro-aliases world))
                     (list* (cons :condition-fn ,condition-fn)
                            (cons :inline ,inline)
                            (cons :trace ,trace)
                            (cons :commutative ,commutative)
                            (cons :forget ,forget)
                            (cons :memo-table-init-size
                                  ,(or memo-table-init-size
                                       *mht-default-size*))
                            (cons :aokp ,aokp)
                            (and (not (eq ,ideal-okp :default))
                                 (list (cons :ideal-okp ,ideal-okp)))))
              (value-triple (deref-macro-name
                             ,fn
                             (macro-aliases (w state))))))
     ((and condition-p
           (not (eq condition t))
           (not (eq condition nil)))
      `(make-event
        (let* ((wrld (w state))
               (fn (deref-macro-name ,fn (macro-aliases wrld)))
               (condition ,condition)
               (formals
                (and (symbolp fn) ; guard for getprop
                     (getprop fn 'formals t
                              'current-acl2-world wrld)))
               (stobjs-in (getprop fn 'stobjs-in t
                                   'current-acl2-world wrld))
               (condition-fn (or ,condition-fn
                                 (intern-in-package-of-symbol
                                  (concatenate
                                   'string
                                   (symbol-name fn)
                                   "-MEMOIZE-CONDITION")
                                  fn)))
               (hints ,hints)
               (otf-flg ,otf-flg)
               (inline ,inline)
               (trace ,trace)
               (commutative ,commutative)
               (forget ,forget)
               (memo-table-init-size ,memo-table-init-size)
               (aokp ,aokp)
               (ideal-okp ,ideal-okp))
          (cond ((not (and
                       (symbolp fn)
                       (not (eq t formals))
                       (not (eq t stobjs-in))
                       (not (eq t (getprop fn 'stobjs-out t

; Normally we would avoid getting the stobjs-out of return-last.  But
; return-last will eventually be rejected for mamoization anyhow (by
; memoize-table-chk).

                                           'current-acl2-world wrld)))
                       (cltl-def-from-name fn wrld)))
                 (er hard 'memoize
                     "The symbol ~x0 is not a known function symbol, and thus ~
                      it cannot be memoized."
                     fn))

; Certify-book seems to do things twice, so the following is commented out.

;             ((cdr (assoc-eq fn (table-alist 'memoize-table wrld)))
;              (er hard 'memoize "~x0 is already memoized." fn))

                ((not (member-eq inline '(t nil)))
                 (er hard 'memoize
                     "The value ~x0 for inline is illegal (must be ~x1 or ~x2)."
                     inline t nil))
                ((not (member-eq trace '(t nil)))
                 (er hard 'memoize
                     "The value ~x0 for trace is illegal (must be ~x1 or ~x2)."
                     trace t nil))
                (t
                 `(progn
                    (defun ,condition-fn ,formals
                      (declare
                       (ignorable ,@formals)
                       (xargs :guard
                              ,(getprop fn 'guard *t*
                                        'current-acl2-world wrld)
                              :verify-guards nil
                              ,@(let ((stobjs (remove nil stobjs-in)))
                                  (and stobjs
                                       `(:stobjs ,stobjs)))))
                      ,condition)
                    (verify-guards ,condition-fn
                                   ,@(and hints `(:hints ,hints))
                                   ,@(and otf-flg
                                          `(:otf-flg ,otf-flg)))
                    (table memoize-table
                           ',fn
                           (list* (cons :condition-fn ',condition-fn)
                                  (cons :inline ',inline)
                                  (cons :trace ',trace)
                                  (cons :commutative ',commutative)
                                  (cons :forget ',forget)
                                  (cons :memo-table-init-size
                                        (or ,memo-table-init-size
                                            *mht-default-size*))
                                  (cons :aokp ',aokp)
                                  (and (not (eq ',ideal-okp :default))
                                       (list (cons :ideal-okp ',ideal-okp)))))
                    (value-triple ',fn)))))))
     (t `(progn (table memoize-table
                       (deref-macro-name ,fn (macro-aliases world))
                       (list* (cons :condition-fn ,condition) ; t or nil
                              (cons :inline ,inline)
                              (cons :trace ,trace)
                              (cons :commutative ,commutative)
                              (cons :forget ,forget)
                              (cons :memo-table-init-size
                                    (or ,memo-table-init-size
                                        *mht-default-size*))
                              (cons :aokp ',aokp)
                              (and (not (eq ',ideal-okp :default))
                                   (list (cons :ideal-okp ',ideal-okp)))))
                (value-triple (deref-macro-name
                               ,fn
                               (macro-aliases (w state)))))))))

(defmacro memoize (fn &key
                      (condition 't condition-p)
                      condition-fn hints otf-flg
                      (recursive 't)
                      trace
                      commutative
                      forget
                      memo-table-init-size
                      aokp
                      (ideal-okp ':default)
                      (verbose 't))

; WARNING: If you add a new argument here, consider making corresponding
; modifications to memoize-form, table-cltl-cmd, maybe-push-undo-stack, and
; add-trip.  (These were the functions modified when adding the FORGET
; argument; the process was to see how the COMMUTATIVE argument was handled.)

; If condition and condition-fn are both non-nil, then the intent is
; that we do exactly what we would normally do for condition except
; that we use the name condition-fn.

; Parallelism blemish: when waterfall parallelism is enabled (detected by
; seeing whether ACL2 global 'waterfall-parallelism is non-nil), memoize and
; unmemoize should be changed to modify the 'saved-memoize-table instead of
; 'memoize-table.

  (declare (xargs :guard (booleanp recursive))
           (ignorable condition-p condition condition-fn hints otf-flg
                      recursive trace commutative forget memo-table-init-size
                      aokp ideal-okp verbose))

  #-acl2-loop-only
  `(progn (when (eql *ld-level* 0)

; We are not inside the ACL2 loop (hence not in certify-book, for
; example).

            (let ((state *the-live-state*))
              (warning$ 'memoize nil
                        "No change for function ~x0: Memoization ~
                         requests are ignored in raw Lisp.  In raw ~
                         Lisp, use memoize-fn."
                        ',fn)))
          (value-triple nil))

  #+acl2-loop-only
  (let* ((inline recursive)
         (form
          (cond
           ((eq commutative t)
            `(make-event
              (let* ((fn ,fn)
                     (commutative
                      (intern-in-package-of-symbol
                       (concatenate 'string (symbol-name fn) "-COMMUTATIVE")
                       fn)))
                (list ; use encapsulate so that each form is printed first
                 'encapsulate
                 ()
                 (list 'defthm commutative
                       (list 'equal
                             (list fn 'x 'y)
                             (list fn 'y 'x))
                       :rule-classes nil)
                 (memoize-form (kwote fn) ',condition ',condition-p
                               ',condition-fn ',hints ',otf-flg ',inline
                               ',trace
                               (kwote commutative)
                               ',forget
                               ',memo-table-init-size
                               ',aokp
                               ',ideal-okp)))))
           (t (memoize-form fn condition condition-p condition-fn
                            hints otf-flg inline trace commutative forget
                            memo-table-init-size aokp ideal-okp)))))
    (cond (verbose form)
          (t `(with-output
               :off (summary prove event)
               :gag-mode nil
               ,form)))))

(defmacro unmemoize (fn)
  (declare (xargs :guard t))
  #-acl2-loop-only
  `(progn (when (eql *ld-level* 0)

; We are not inside the ACL2 loop (hence not in certify-book, for
; example).

            (warning$ 'unmemoize nil
                      "No change for function ~x0: Unmemoization requests are ~
                       ignored in raw Lisp.  In raw Lisp, use unmemoize-fn."
                      ',fn))
          (value-triple nil))
  #+acl2-loop-only
  `(with-output
    :off summary
    (progn (table memoize-table
                  (deref-macro-name ,fn (macro-aliases world))
                  nil)
           (value-triple
            (deref-macro-name ,fn (macro-aliases (w state)))))))

(defmacro profile (fn &rest r)
  (declare (xargs :guard (and (keyword-value-listp r)
                              (not (assoc-keyword :condition r))
                              (not (assoc-keyword :condition-fn r))
                              (not (assoc-keyword :recursive r)))))
  `(memoize ,fn :condition nil :recursive nil ,@r))

#-hons
(defmacro memoize-on-raw (fn form)
  (declare (ignore fn))
  form)

(defmacro memoize-on (fn form)

; MEMOIZE-ON evaluates form.  During the evaluation the symbol fn has as
; its symbol-function what it had immediately AFTER the memoization of
; fn.  Hence, the values of calls of fn may be remembered during the
; evaluation and later.  Warning: to use MEMOIZE-ON, fn must already
; be memoized.

  `(return-last 'memoize-on-raw ,fn ,form))

#-hons
(defmacro memoize-off-raw (fn form)
  (declare (ignore fn))
  form)

(defmacro memoize-off (fn form)

; MEMOIZE-OFF evaluates form.  During the evaluation the symbol fn has as
; its symbol-function what it had immediately BEFORE the memoization
; of fn.  Hence the values of calls of fn may not be remembered during
; the evaluation.  Warning: to use MEMOIZE-OFF, fn must already be
; memoized."

  `(return-last 'memoize-off-raw ,fn ,form))

(defmacro memoizedp-world (fn wrld)
  `(let ((fn ,fn)
         (wrld ,wrld))
     (cond
      ((not (global-val 'hons-enabled wrld))
       (er hard 'memoizedp
           "Memoizedp cannot be called in this ACL2 image, as it requires a ~
            hons-aware ACL2.  See :DOC hons-and-memoization."))
      (t
       (cdr (assoc-eq fn (table-alist 'memoize-table wrld)))))))

(defmacro memoizedp (fn)
  (declare (xargs :guard t))
  `(memoizedp-world ,fn (w state)))

;;; hons-shrink-alist

; HONS-SHRINK-ALIST, when called with an atomic second
; argument, produces an alist that is alist-equivalent
; to the first argument, but with all irrelevant entries in
; the first argument deleted.  Informal remark: the alist
; returned is a hons when the initial ANS is not an atom.

; Comment about the last clause above.  Or really?
; Counterexamples?
;
; mbu> stp
; ? (honsp (hons-shrink-alist '((a . b) (a . b2)) (hons-acons 1 2 3)))
; NIL
;
; mbu> stp
; ? (honsp (hons-shrink-alist '((a . b) (a . b2)) nil))
; NIL
; ?

; Some centaur/ books put entries in *never-profile-ht*.  In order to allow
; those books to certify in vanilla ACL2, we define a default value for that
; variable here.

#+(and (not hons) (not acl2-loop-only))
(defparameter *never-profile-ht*
  (make-hash-table :test 'eq))

#+(or acl2-loop-only (not hons))
(defun never-memoize-fn (fn)
   (declare (xargs :guard (symbolp fn))
            (ignore fn))
   nil)

(defmacro never-memoize (fn)
  (declare (xargs :guard (symbolp fn)))
  `(make-event
    (prog2$ (never-memoize-fn ',fn)
            '(value-triple :invisible))
    :check-expansion t))
