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

; memoize.lisp -- Logical definitions for memoization functions.

; The original version of this file was contributed by Bob Boyer and
; Warren A. Hunt, Jr.  The design of this system of Hash CONS,
; function memoization, and fast association lists (applicative hash
; tables) was initially implemented by Boyer and Hunt.

(in-package "ACL2")

#+(or acl2-loop-only (not hons))
(defn clear-memoize-table (fn)

; Warning: Keep the return values in sync for the logic and raw Lisp.

  fn)

#+(or acl2-loop-only (not hons))
(defn clear-memoize-tables ()

; Warning: Keep the return values in sync for the logic and raw Lisp.

  nil)

#+(or acl2-loop-only (not hons))
(defn memoize-summary ()

; Warning: Keep the return values in sync for the logic and raw Lisp.

  nil)

#+(or acl2-loop-only (not hons))
(defn clear-memoize-statistics ()

; Warning: Keep the return values in sync for the logic and raw Lisp.

  nil)

(defmacro memsum ()
  '(memoize-summary))

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
    hons-clear!
    hons-wash
    hons-wash!
    hons-summary
    hons-resize-fn
    get-slow-alist-action
    hons-get
    hons-acons
    hons-acons!
    fast-alist-fork
    fast-alist-fork!
    fast-alist-clean
    fast-alist-clean!
    fast-alist-len
    fast-alist-free
    fast-alist-summary
    cons-subtrees
    number-subtrees
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
            memsum)
          *hons-primitive-fns*))

(defconst *mht-default-size* 60)

(defun memoize-form (fn
                     condition
                     condition-p
                     condition-fn
                     hints
                     otf-flg
                     inline ; from :recursive argument
                     commutative
                     forget
                     memo-table-init-size
                     aokp
                     stats
                     total
                     invoke
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
                            (cons :commutative ,commutative)
                            (cons :forget ,forget)
                            (cons :memo-table-init-size
                                  ,(or memo-table-init-size
                                       *mht-default-size*))
                            (cons :aokp ,aokp)
                            (cons :stats ,stats)
                            (cons :total ,total)
                            (cons :invoke ,invoke)
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
                     (getpropc fn 'formals t wrld)))
               (stobjs-in (getpropc fn 'stobjs-in t wrld))
               (condition-fn (or ,condition-fn
                                 (add-suffix fn "-MEMOIZE-CONDITION")))
               (hints ,hints)
               (otf-flg ,otf-flg)
               (inline ,inline)
               (commutative ,commutative)
               (forget ,forget)
               (memo-table-init-size ,memo-table-init-size)
               (aokp ,aokp)
               (stats ,stats)
               (total ,total)
               (invoke ,invoke)
               (ideal-okp ,ideal-okp))
          (cond ((not (and
                       (symbolp fn)
                       (not (eq t formals))
                       (not (eq t stobjs-in))
                       (not (eq t (getpropc fn 'stobjs-out t

; Normally we would avoid getting the stobjs-out of return-last.  But
; return-last will eventually be rejected for mamoization anyhow (by
; memoize-table-chk).

                                            wrld)))
                       (cltl-def-from-name fn wrld)))
                 (er hard 'memoize
                     "The symbol ~x0 is not a known function symbol, and thus ~
                      it cannot be memoized."
                     fn))

; There seems to have been a time when the following had caused an error
; because of double evaluation of memoize forms by certify-book (not sure).  So
; the following is commented out.  That doesn't seem to cause a problem;
; redundancy of memoize forms seems to be handled well.

;               ((cdr (assoc-eq fn (table-alist 'memoize-table wrld)))
;                (er hard 'memoize "~x0 is already memoized." fn))

                ((not (member-eq inline '(t nil)))
                 (er hard 'memoize
                     "The value ~x0 for inline is illegal (must be ~x1 or ~
                      ~x2)."
                     inline t nil))
                (t
                 `(progn
                    (defun ,condition-fn ,formals
                      (declare
                       (ignorable ,@formals)
                       (xargs :guard
                              ,(getpropc fn 'guard *t* wrld)
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
                                  (cons :commutative ',commutative)
                                  (cons :forget ',forget)
                                  (cons :memo-table-init-size
                                        (or ,memo-table-init-size
                                            *mht-default-size*))
                                  (cons :aokp ',aokp)
                                  (cons :stats ,stats)
                                  (cons :total ',total)
                                  (cons :invoke ',invoke)
                                  (and (not (eq ',ideal-okp :default))
                                       (list (cons :ideal-okp ',ideal-okp)))))
                    (value-triple ',fn)))))))
     (t `(progn (table memoize-table
                       (deref-macro-name ,fn (macro-aliases world))
                       (list* (cons :condition-fn ,condition) ; t or nil
                              (cons :inline ,inline)
                              (cons :commutative ,commutative)
                              (cons :forget ,forget)
                              (cons :memo-table-init-size
                                    (or ,memo-table-init-size
                                        *mht-default-size*))
                              (cons :aokp ',aokp)
                              (cons :stats ,stats)
                              (cons :total ,total)
                              (cons :invoke ,invoke)
                              (and (not (eq ',ideal-okp :default))
                                   (list (cons :ideal-okp ',ideal-okp)))))
                (value-triple (deref-macro-name
                               ,fn
                               (macro-aliases (w state)))))))))

(defmacro memoize (fn &key
                      (condition 't condition-p)
                      condition-fn hints otf-flg
                      (recursive ':default)
                      commutative
                      forget
                      memo-table-init-size
                      aokp
                      (stats ':default)
                      total
                      invoke
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

  (declare (xargs :guard (member-eq recursive '(t nil :default)))
           (ignorable condition-p condition condition-fn hints otf-flg
                      recursive commutative forget memo-table-init-size
                      aokp stats total invoke ideal-okp verbose))

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
  (cond
   ((symbolp fn)
    (er hard 'memoize
        "It is illegal for the first argument of MEMOIZE to be a symbol.  ~
         Note that the arguments to MEMOIZE are evaluated; so perhaps you ~
         intended the first argument to be (QUOTE ~x0) or, equivalently, '~x0."
        fn))
   ((and invoke (symbolp invoke))
    (er hard 'memoize
        "It is illegal for the :INVOKE argument of MEMOIZE to be a symbol.  ~
         Note that the arguments to MEMOIZE are evaluated; so perhaps you ~
         intended that argument to be (QUOTE ~x0) or, equivalently, '~x0."
        invoke))
   (t
    (let* ((inline (if (eq recursive :default)
                       (if invoke nil t)
                     recursive))
           (condition (cond ((and invoke
                                  (not condition-p)
                                  (not condition-fn))
                             nil)
                            (t condition)))
           (stats (if (and invoke (eq stats :default))
                      nil
                    stats))
           (form
            (cond
             ((eq commutative t)
              `(make-event
                (let* ((fn ,fn)
                       (commutative (add-suffix fn "-COMMUTATIVE")))
                  (list ; use encapsulate so that each form is printed first
                   'encapsulate
                   ()
                   (list 'value-triple ; avoid redundancy for the encapsulate
                         (kwote (cons (max-absolute-event-number (w state))
                                      (car (global-val 'include-book-path
                                                       (w state))))))
                   (list 'defthm commutative
                         (list 'equal
                               (list fn 'x 'y)
                               (list fn 'y 'x))
                         :rule-classes nil)
                   (memoize-form (kwote fn) ',condition ',condition-p
                                 ',condition-fn ',hints ',otf-flg ',inline
                                 (kwote commutative)
                                 ',forget
                                 ',memo-table-init-size
                                 ',aokp
                                 ',stats
                                 ',total
                                 ',invoke
                                 ',ideal-okp)))))
             (t (memoize-form fn condition condition-p condition-fn
                              hints otf-flg inline commutative forget
                              memo-table-init-size aokp stats total invoke
                              ideal-okp)))))
      (cond (verbose form)
            (t `(with-output
                 :off (summary prove event)
                 :gag-mode nil
                 ,form)))))))

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

; Warning: See the comment in profiled-functions before eliminating :recursive
; nil, which corresponds to :inline nil in profile-fn.

  `(memoize ,fn :condition nil :recursive nil ,@r))

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

; Some centaur/ books put entries in *never-profile-ht*.  In order to allow
; those books to certify in vanilla ACL2, we define a default value for that
; variable here.

#+(and (not hons) (not acl2-loop-only))
(defparameter *never-profile-ht*
  (make-hash-table :test 'eq))

#+(or acl2-loop-only (not hons))
(defun never-memoize-fn (fn)

; Warning: Keep the return values in sync for the logic and raw Lisp.

  (declare (xargs :guard (symbolp fn))
           (ignore fn))
  nil)

(defmacro never-memoize (fn)
  (declare (xargs :guard (symbolp fn)))
  `(make-event
    (prog2$ (never-memoize-fn ',fn)
            '(value-triple :invisible))
    :check-expansion t))

(defconst *bad-lisp-consp-memoization*
  '(bad-lisp-consp :forget t))

(defconst *thread-unsafe-builtin-memoizations*

; This alist associates built-in raw Lisp functions with corresponding
; keyword arguments for memoize-fn.  These functions may be unsafe to memoize
; when using ACL2(hp).

  (list *bad-lisp-consp-memoization*))

#+acl2-loop-only
(defun set-bad-lisp-consp-memoize (arg)

; Warning: Keep the return values in sync for the logic and raw Lisp.

  (declare (xargs :guard t)
           (ignore arg))
  nil)

(defconst *special-cltl-cmd-attachment-mark-name*
; This is used in memoize-raw.lisp, so we define it here.
  ':apply$-userfn/badge-userfn)

(defconst *special-cltl-cmd-attachment-mark*
  `(attachment ,*special-cltl-cmd-attachment-mark-name*))
