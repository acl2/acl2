; watch-raw.lsp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; This file was originally part of the HONS version of ACL2.  The original
; version of ACL2(h) was contributed by Bob Boyer and Warren A. Hunt, Jr.  The
; design of this system of Hash CONS, function memoization, and fast
; association lists (applicative hash tables) was initially implemented by
; Boyer and Hunt.

(in-package "ACL2")

(defmacro defn1 (f a &rest r)
  (when (intersection a lambda-list-keywords)
    (error "DEFN1: ** In the defintion of ~s, the argument list ~s ~
            contains a member of lambda-list-keywords so do not ~
            use defn1."
           f a))
  `(progn
     (setf (gethash ',f *number-of-arguments-and-values-ht*)
           (cons ,(length a) 1))
     (declaim (ftype (function ,(make-list (len a) :initial-element t)
                               (values t))
                     ,f))
     (defun ,f ,a (declare (xargs :guard t)) ,@r)))


(defg *watch-file* nil
  "If *WATCH-FILE* is not NIL, it is a string that names the 'watch
  file', to which (WATCH-DUMP) prints.")

(defg *watch-string*
  (let ((ws (make-array 0 :element-type 'character
                        :adjustable t :fill-pointer t)))
    (setf (fill-pointer ws) 0)
    ws)
  "WATCH-DUMP first writes to the adjustable string *WATCH-STRING*
  and then prints to the *WATCH-FILE*.")

(declaim (type (array character (*)) *watch-string*))

(defg *watch-forms*
  '("\"A string or a quoted form in *WATCH-FORMS* is ignored.\""
    (print-call-stack)
    #+Clozure '(bytes-used)
    (memoize-summary)
    (time-since-watch-start)
    (time-of-last-watch-update)
    ;; '(mapc 'print-some-documentation *watch-items*)
    ;; [Jared] removing these, they haven't worked since hl-hons
    ;; '(hons-calls/sec-run-time)
    ;; '(hons-hits/calls)
    '(hons-acons-summary)
    '(pons-calls/sec-run-time)
    '(pons-hits/calls)
    '(pons-summary)
    '(hons-summary)
    ;; [Jared]; removing this because it seems very architecture specific, etc.
    ;; If we really want this, we can add it back with some kind of ttag book.
    ;; '(print-fds)
    ;; [Jared]: removed this because it lets me get rid of a lot of
    ;; code.  If we really want this, we can add it back with some kind
    ;; of ttag book.
    ;; '(print-ancestry)
    ;; [Jared]: removing this 
    ;; #+Clozure '(watch-shell-command "pwd")
    '(functions-that-may-be-too-fast-to-sensibly-profile)
    '(physical-memory-on-this-machine)
    #+Clozure '(number-of-cpus-on-this-machine)
    #+Clozure (gc-count)
    )

  "The forms in *WATCH-FORMS* are evaluated periodically and the
  output is written to *WATCH-FILE*.  Change *WATCH-FORMS*
  to produce whatever watch output you want.")

(defg *watch-items*
  '((length-memoized-functions)
    *memoize-summary-limit*
    *memoize-summary-order-list*
    *memoize-summary-order-reversed*
    *max-mem-usage*

    *watch-forms*
    *watch-file*
    *watch-items*

    *count-pons-calls*

    *memoize-summary-order-list*
    *memoize-summary-order-reversed*
    *memoize-summary-limit*

    *record-bytes*
    *record-calls*
    *record-hits*
    *record-hons-calls*
    *record-mht-calls*
    *record-pons-calls*
    *record-time*

    *report-bytes*
    *report-calls*
    *report-calls-from*
    *report-calls-to*
    *report-hits*
    *report-hons-calls*
    *report-mht-calls*
    *report-pons-calls*
    *report-time*
    *report-on-memo-tables*
    *report-on-pons-tables*

    #+Clozure (ccl::lisp-heap-gc-threshold)
    #+Clozure (ccl::%freebytes)

    )
  "*WATCH-ITEMS* is a list of forms that are printed with their values
  and documentation if (MAPC 'PRINT-SOME-DOCUMENTATION *WATCH-ITEMS*)
  is a member of *WATCH-FORMS* and (WATCH-DO) is invoked.")

(defg *watch-last-real-time* 0)
(defg *watch-last-run-time* 0)
(defg *watch-start-real-time* 0)
(defg *watch-start-run-time* 0)
(defg *watch-start-gc-count*  0)
(defg *watch-start-gc-time* 0)
(defg *watch-start-heap-bytes-allocated* 0)

(declaim (mfixnum *watch-last-real-time* *watch-last-run-time*
                  *watch-start-real-time* *watch-start-run-time* *watch-start-gc-count*
                  *watch-start-gc-time*))

(defg *watch-file-form*

  '(format nil "watch-output-temp-~D.lsp" (getpid$))

  "The value of *WATCH-FILE-FORM* should be a form that is to
  be evaluated whenever (WATCH) is invoked in order to get
  the string that is to name *WATCH-FILE*.")



#+Clozure
(defv *watch-dog-process* nil

  "*WATCH-DOG-PROCESS*, when non-NIL is a CCL process that
  periodically asks the main CCL thread/process,
  *WATCH-STARTUP-PROCESS*, to invoke MAYBE-WATCH-DUMP.

  It is always ok to kill the *WATCH-DOG-PROCESS*.  (WATCH-KILL) does
  that.")

#+Clozure
(defv *watch-startup-process* nil

  "*WATCH-STARTUP-PROCESS*, when non-NIL is the CCL process that
  created the *WATCH-DOG-PROCESS*, and the only process that should
  ever run MAYBE-WATCH-DUMP.")

#+Clozure
(defparameter *with-space-timer-raw-limit* nil)

#+Clozure
(defparameter *with-run-timer-raw-limit* nil

  "*WITH-RUN-TIMER-RAW-LIMIT* is bound only by WITH-RUN-TIMER-RAW, and
  is bound to a nonnegative integer representing the value of
  (INTERNAL-RUN-TIME) after which, if the watch process interrupts the
  main Lisp process to run MAYBE-WATCH-DUMP, the execution of
  MAYBE-WATCH-DUMP will raise an error with a condition of type
  WITH-TIMER-RAW-CONDITION-TYPE.")

#+Clozure
(defparameter *with-real-timer-raw-limit* nil

  "*WITH-REAL-TIMER-RAW-LIMIT* is bound only by WITH-REAL-TIMER-RAW,
  and is bound to a nonnegative integer representing the value of
  (INTERNAL-REAL-TIME) after which, if the watch process interrupts
  the main Lisp process to run MAYBE-WATCH-DUMP, the execution of
  MAYBE-WATCH-DUMP will raise an error with a condition of type
  WITH-TIMER-RAW-CONDITION-TYPE.")

#+Clozure
(defg *watch-lock-ht* (make-hash-table)
  "*WATCH-LOCK-HT* is used to provide a locking mechanism to
  prevent watch-dump from being run twice at the same time.")

#+Clozure
(declaim (hash-table *watch-lock-ht*))

#+Clozure
(defg *watch-real-seconds-between-dumps* 5

  "WATCH-DUMP will not run more than once every
  *WATCH-REAL-SECONDS-BETWEEN-DUMPS* seconds.")

#+Clozure
(declaim (fixnum *watch-real-seconds-between-dumps*))

#+Clozure
(defn watch-condition ()
  (unless (eq *watch-dog-process* ccl::*current-process*)
    (ofto "~%WATCH-CONDITION should only be called by ~
          *watch-dog-process*:~%~a~%never by~%~a."
          *watch-dog-process*
          ccl::*current-process*))
  (and *watch-file*
       (eql 0 ccl::*break-level*)
       (let ((run nil) (real nil))
         (or (and *with-space-timer-raw-limit*
                  (> (ccl::%usedbytes) *with-space-timer-raw-limit*))
             (and *with-real-timer-raw-limit*
                  (> (setq real (get-internal-real-time))
                     *with-real-timer-raw-limit*))
             (and *with-run-timer-raw-limit*
                  (> (setq run (get-internal-run-time))
                     *with-run-timer-raw-limit*))
             (and (> (or run (get-internal-run-time))
                     *watch-last-run-time*)
                  (> (or real (get-internal-real-time))
                     (+ *watch-last-real-time*
                        (* *watch-real-seconds-between-dumps*
                           internal-time-units-per-second))))))
       (eql 0 (hash-table-count *watch-lock-ht*))))

#+Clozure
(defmacro with-watch-lock (&rest r)

; WITH-WATCH-LOCK may well do nothing, knowing that a later call of
; MAYBE-WATCH-DUMP will probably evenutally be made by the
; WATCH-DOG-PROCESS, and that will be good enough.  WITH-WATCH-LOCK
; does not support a queue of pending requests for the lock.

  `(progn
     (cond ((not (eq *watch-startup-process* ccl::*current-process*))
            (ofd "~%; WITH-WATCH-LOCK: ** Only the ~
                   *WATCH-STARTUP-PROCESS* may obtain the watch ~
                   lock."))
           ((not (eql 0 ccl::*break-level*))
            (ofd "~%; WITH-WATCH-LOCK: ** (eql 0 ~
                  ccl::*break-level*)."))
           ((not *watch-file*)
            (ofd "~%; *WATCH-FILE* is NIL.  Invoke (watch)."))
           ((eql 0 (hash-table-count *watch-lock-ht*))

; At this point, nothing has the watch lock.  We race for the watch
; lock but unknown others may also get into the race, this very
; process executing this very code.

            (let ((id (cons nil nil)))  ; a unique object
              (unwind-protect
                  (progn
                    (setf (gethash id *watch-lock-ht*) t)
                    (cond ((eql (hash-table-count *watch-lock-ht*) 1)

; The watch lock has been obtained by only one of 'us', and any
; competitors will do nothing.

                           ,@r)
                          (t (ofd "~%; WITH-WATCH-LOCK: ** the watch ~
                                   lock is currently taken."))))
                (remhash id *watch-lock-ht*))

; The watch lock is released as of now, if it was obtained.

              ))
           (t (ofd "~%; WITH-WATCH-LOCK: ** the watch lock is ~
                    currently taken.")))
     *watch-file*))



#+Clozure
(define-condition with-timer-raw-condition-type (error) ())

; The following 'condition' type and one 'instance' thereof are
; created to support one use in the HANDLER-CASE form in
; WITH-RUN-TIMER-RAW or WITH-RUN-TIMER-RAW, permitting time out errors
; to be distinguished from all other sorts of errors.

#+Clozure
(defg *with-space-timer-raw-condition-instance*
  (make-condition 'with-timer-raw-condition-type))

#+Clozure
(defg *with-real-timer-raw-condition-instance*
  (make-condition 'with-timer-raw-condition-type))

#+Clozure
(defg *with-run-timer-raw-condition-instance*
  (make-condition 'with-timer-raw-condition-type))

#+Clozure
(defv *space-timer-raw-bytes* 1)

#+Clozure
(defv *space-timer-raw-value* '("space out"))

#+Clozure
(defv *real-timer-raw-seconds* 1)

#+Clozure
(defv *real-timer-raw-value* '("time out"))

#+Clozure
(defv *run-timer-raw-seconds* 1)

#+Clozure
(defv *run-timer-raw-value* '("time out"))

#+Clozure
(defmacro with-space-timer-raw (form
                                &key
                          (bytes *space-timer-raw-bytes*)
                          (space-out-value *space-timer-raw-value*))
  `(let* ((old *with-space-timer-raw-limit*)
          (new (+ (ccl::%usedbytes) ,bytes))
          (new2 (if *with-space-timer-raw-limit*
                    (min *with-space-timer-raw-limit* new)
                  new)))
     (handler-case
      (progn (setq *with-space-timer-raw-limit* new2)
             (unwind-protect ,form
               (setq *with-space-timer-raw-limit* old)))
      (with-timer-raw-condition-type
       (c)
       (cond ((eq c *with-space-timer-raw-condition-instance*)
              ; (ofd "~&; space-out when evaluating:~%~s." ',form)
              (setq *with-space-timer-raw-limit* old)
              ',space-out-value)
             (t (error c)))))))



#+Clozure
(defmacro with-real-timer-raw (form
                          &key
                          (seconds *real-timer-raw-seconds*)
                          (time-out-value *real-timer-raw-value*))

  "(WITH-REAL-TIMER-RAW form &key seconds time-out-value) begins an
  evaluation of FORM, but the evaluation may and should be aborted
  when more than SECONDS seconds of real-time (wall time) elapses.
  Whether an abort actually occurs depends upon the vagaries of time,
  including whether the watch-dog-process, if there is one, is
  successful in interrupting the main Lisp process.  If and when the
  evaluation of FORM completes, WITH-REAL-TIMER-RAW returns the
  value(s) of that evaluation.  But otherwise, TIME-OUT-VALUE is
  returned.  SECONDS defaults to the value of
  *REAL-TIMER-RAW-SECONDS*.  TIME-OUT-VALUE defaults to a list of
  length one whose only member is a string; such an object satisfies
  TO-IF-ERROR-P.

  If WITH-REAL-TIMER-RAW is called while WITH-REAL-TIMER-RAW is
  running, the new time limit is bounded by any and all real-timer
  limits already in place."

 `(let* ((old *with-real-timer-raw-limit*)
         (new (floor
               (+ (get-internal-real-time)
                  (* ,seconds internal-time-units-per-second))))
         (new2 (if *with-real-timer-raw-limit*
                   (min *with-real-timer-raw-limit* new)
                 new)))
    (handler-case
     (progn (setq *with-real-timer-raw-limit* new2)
            (unwind-protect ,form
              (setq *with-real-timer-raw-limit* old)))
     (with-timer-raw-condition-type
      (c)
      (cond ((eq c *with-real-timer-raw-condition-instance*)
             (ofd "~&; real-time-out when evaluating:~%~s." ',form)
             (setq *with-real-timer-raw-limit* old)
             ',time-out-value)
            (t (error c)))))))

#+Clozure
(defmacro with-run-timer-raw (form
                          &key
                          (seconds *run-timer-raw-seconds*)
                          (time-out-value *run-timer-raw-value*))

  "(WITH-RUN-TIMER-RAW form &key seconds time-out-value) begins an
  evaluation of FORM, but the evaluation may and should be aborted
  when more than SECONDS seconds of run-time (not wall time) elapses.
  Whether an abort actually occurs depends upon the vagaries of time,
  including whether the watch-dog-process, if there is one, is
  successful in interrupting the main Lisp process.  If and when the
  evaluation of FORM completes, WITH-RUN-TIMER-RAW returns the
  value(s) of that evaluation.  But otherwise, TIME-OUT-VALUE is
  returned.  SECONDS defaults to the value of *RUN-TIMER-RAW-SECONDS*,
  which is initially 5.  TIME-OUT-VALUE defaults to a list of length
  one whose only member is a string; such an object satisfies
  TO-IF-ERROR-P.

  If WITH-RUN-TIMER-RAW is called while WITH-RUN-TIMER-RAW is running,
  the new time limit is bounded by any and all run-time limits already
  in place."

 `(let* ((old *with-run-timer-raw-limit*)
         (new (floor
               (+ (get-internal-run-time)
                  (* ,seconds internal-time-units-per-second))))
         (new2 (if *with-run-timer-raw-limit*
                   (min *with-run-timer-raw-limit* new)
                 new)))
    (handler-case
     (progn (setq *with-run-timer-raw-limit* new2)
            (unwind-protect ,form
              (setq *with-run-timer-raw-limit* old)))
     (with-timer-raw-condition-type
      (c)
      (cond ((eq c *with-run-timer-raw-condition-instance*)
             (ofd "~&; run-time-out when evaluating:~%~s." ',form)
             (setq *with-run-timer-raw-limit* old)
             ',time-out-value)
            (t (error c)))))))


(defg *watch-count-ht* (make-hash-table))

(defn1 watch-count ()
  (values (gethash 'count *watch-count-ht*)))

(defn1 incf-watch-count ()
  (incf (gethash 'count *watch-count-ht*)))

(defn1 set-watch-count (x)
  (setf (gethash 'count *watch-count-ht*) x))

(defv *watch-sleep-seconds* 1

  "The watch dog process sleeps at least *WATCH-SLEEP-SECONDS*
  before interrupting the main process.")


(defparameter *faking-batch-flag*
  ;; See live-terminal-p
  nil)

(defun live-terminal-p ()
  ;; Part of WATCH

  "(LIVE-TERMINAL-P) attempts to determine whether there
  is an active user terminal for this Lisp."

  #+Clozure
  (and (null (or *faking-batch-flag* ccl::*batch-flag*))
       (not (search "FILE"
                    (with-standard-io-syntax
                     (write-to-string *terminal-io*
                                      :escape nil
                                      :readably nil)))))
    #-Clozure t)


#+Clozure
(defn1 maybe-watch-dump ()

  "The function MAYBE-WATCH-DUMP is only executed as an interruption
  request to the main Lisp thread from the watch dog process.  To
  repeat, MAYBE-WATCH-DUMP is executed only by the main Lisp thread.
  There is no overwhelming reason why this should be so, but the issue
  of 'shared' hash tables, 'static' variables, ERROR handling, and
  DEFPARAMETER bindings should be carefully considered if this design
  choice is reconsidered.

  (MAYBE-WATCH-DUMP) performs three unrelated tasks.

  1.  If *WITH-RUN-TIMER-RAW-LIMIT* is a nonnegative integer that is
  less than (GET-INTERNAL-RUN-TIME), then an error of type
  TIMER-RAW-CONDITION is raised, which normally will be caught by the
  error handler established by a pending call of WITH-RUN-TIMER-RAW.

  2.  If *WITH-REAL-TIMER-RAW-LIMIT* is a nonnegative integer that is
  less than (GET-INTERNAL-REAL-TIME), then an error of type
  TIMER-RAW-CONDITION is raised, which normally will be caught by
  the error handler established by a pending call of
  WITH-REAL-TIMER-RAW.

  3.  If the watch lock can be obtained, (WATCH-DUMP) is run."

  (cond ((not (eql 0 ccl::*break-level*))
         (incf-watch-count))
        ((and *watch-file*
              (eq *watch-startup-process* ccl::*current-process*))
         (when (and *with-space-timer-raw-limit*
                    (> (ccl::%usedbytes)
                       *with-space-timer-raw-limit*))
           (setq *with-space-timer-raw-limit* nil)
           (incf-watch-count)
           (error *with-space-timer-raw-condition-instance*))
         (when (and *with-run-timer-raw-limit*
                    (> (get-internal-run-time)
                       *with-run-timer-raw-limit*))
           (setq *with-run-timer-raw-limit* nil)
           (incf-watch-count)
           (error *with-run-timer-raw-condition-instance*))
         (when (and *with-real-timer-raw-limit*
                    (> (get-internal-real-time)
                       *with-real-timer-raw-limit*))
           (setq *with-real-timer-raw-limit* nil)
           (incf-watch-count)
           (error *with-real-timer-raw-condition-instance*))
         (handler-case

; No thread or stack frame can be expected to handle an error under
; MAYBE-WATCH-DUMP in WATCH-DUMP, because MAYBE-WATCH-DUMP is run as
; the result of an interrupt from the watch dog process.  In this
; unexpected case, we ignore the error, after printing a note to
; *DEBUG-IO*.

; MAYBE-WATCH-DUMP calls (INCF-WATCH-COUNT), even if MAYBE-WATCH-DUMP
; exits via ERROR or exits after catching and ignoring an error.
; Otherwise, the interrupting watch dog process might wait a very long
; time before resuming normal operation."

          (with-watch-lock (watch-dump))
          (with-timer-raw-condition-type
           (c) ; pass it on up
           (incf-watch-count)
           (error c))
          (error
           (x)
           (ofd "~%; MAYBE-WATCH-DUMP: An error is being ignored:~% ~
                 ~a." x)
           (incf-watch-count)))
         (incf-watch-count)
         *watch-file*)
        (t (incf-watch-count)
           (ofd "~%; MAYBE-WATCH-DUMP may only be called by the ~
                 *WATCH-STARTUP-PROCESS*"))))

(defn1 watch-kill ()

  "(WATCH-KILL) kills the CCL *WATCH-DOG-PROCESS*, if any, and sets
  the *WATCH-FILE* to NIL.  It is alway OK to invoke (WATCH-KILL)."

  (setq *watch-file* nil)
  #+Clozure
  (when *watch-dog-process*
    (ignore-errors (ccl::process-kill *watch-dog-process*))
    (setq *watch-dog-process* nil))
  #+Clozure
  (setq
    *watch-dog-process*            nil
    *with-real-timer-raw-limit*    nil
    *with-space-timer-raw-limit*   nil
    *with-run-timer-raw-limit*     nil
    *watch-startup-process*        nil))


#+Clozure
(defn1 watch-dump ()

  "(WATCH-DUMP) writes to the watch file the characters sent to
  *STANDARD-OUTPUT* by the evaluation of the members of *WATCH-FORMS*.

  The value of *WATCH-FILE* is returned by WATCH-DUMP.

  If *WATCH-FILE* is NIL, (WATCH) is invoked."

  (unless *watch-file* (watch))
  (setf (fill-pointer *watch-string*) 0)
  (our-syntax-nice
   (with-output-to-string
     (*standard-output* *watch-string*)
     (setq *print-miser-width* 100)
     (loop for form in *watch-forms* do
           (handler-case
            (eval form)
            (with-timer-raw-condition-type
             (c) ; pass it on up
             (incf-watch-count)
             (error c))
            (error ()
                   (oft "~&~s~50t? error in eval ?~%"
                        form)))
           (fresh-line)))
   (with-open-file (stream *watch-file* :direction :output
                           :if-exists :supersede)
     (write-string *watch-string* stream))
   (setq *watch-last-real-time* (get-internal-real-time))
   (setq *watch-last-run-time* (get-internal-run-time)))
  *watch-file*)


(defun watch (&optional force-dog)

  "WATCH is a raw Lisp function that initiates the printing of
  profiling information.  (WATCH) sets *WATCH-FILE* to the string that
  results from the evaluation of *WATCH-FILE-FORM*, a string that is
  to be the name of a file we call the 'watch file'.

  In Clozure Common Lisp, (WATCH) also initiates the periodic
  evaluation of (WATCH-DUMP), which evaluates the members of the list
  *WATCH-FORMS*, but diverts characters for *STANDARD-OUTPUT* to the
  watch file.  The value of *WATCH-FILE* is returned by both (WATCH)
  and (WATCH-DUMP).  (WATCH-KILL) ends the periodic printing to the
  watch file.

  You are most welcome to, even encouraged to, change the members of
  *WATCH-FORMS* to have your desired output written to the watch file.

  Often (MEMOIZE-SUMMARY) is a member of *WATCH-FORMS*.  It prints
  information about calls of memoized and/or profiled functions.

  Often (PRINT-CALL-STACK) is a member of *WATCH-FORMS*.  It shows the
  names of memoized and/or profiled functions that are currently in
  execution and how long they have been executing.

  Other favorite members of *WATCH-FORMS* include (PRINT-FDS),
  (BYTES-USED), and (GC-COUNT).

  We suggest the following approach for getting profiling information
  about calls to Common Lisp functions:

    0. Invoke (WATCH).

    1. Profile some functions that have been defined.

       For example, call (PROFILE-FN 'foo1), ...

       Or, for example, call PROFILE-FILE on the name of a file that
       contains the definitions of some functions that have been
       defined.

       Or, as a perhaps extreme example, invoke
       (PROFILE-ACL2), which will profile many of the functions that
       have been introduced to ACL2, but may take a minute or two.

       Or, as a very extreme example, invoke
       (PROFILE-ALL), which will profile many functions, but may take
       a minute or two.

    2. Run a Lisp computation of interest to you that causes some of
       the functions you have profiled to be executed.

    3. Invoke (WATCH-DUMP).

    4. Examine, perhaps in Emacs, the watch file, whose name was
       returned by (WATCH-DUMP).  The watch file contains information
       about the behavior of the functions you had profiled or
       memoized during the computation of interest.

  From within ACL2, you may MEMOIZE any of your ACL2 Common Lisp
  compliant ACL2 functions.  One might MEMOIZE a function that is
  called repeatedly on the exact same arguments.  Deciding which
  functions to memoize is tricky.  The information from (WATCH-DUMP)
  helps.  Sometimes, we are even led to radically recode some of our
  functions so that they will behave better when memoized.

  In Emacs, the command 'M-X AUTO-REVERT-MODE' toggles auto-revert
  mode, i.e., causes a buffer to exit auto-revert mode if it is in
  auto-revert mode, or to enter auto-revert mode if it is not.  In
  other words, to stop a buffer from being auto-reverted, simply
  toggle auto-revert mode; toggle it again later if you want more
  updating.  'M-X AUTO-REVERT-MODE' may be thought of as a way of
  telling Emacs, 'keep the watch buffer still'.

  In Clozure Common Lisp, if the FORCE-DOG argument to WATCH (default
  NIL) is non-NIL or if (LIVE-TERMINAL-P) is non-NIL a 'watch dog'
  thread is created to periodically call (WATCH-DUMP).  The thread is
  the value of *WATCH-DOG-PROCESS*.

  Invoke (WATCH-HELP) outside of ACL2 for further details."

  #-Clozure
  (declare (ignore force-dog))

  #+Clozure
  (ccl::cpu-count)
  (watch-kill)
  #+Clozure
  (pushnew 'watch-kill ccl::*save-exit-functions*)
  #+Clozure
  (setq *watch-lock-ht* (make-hash-table))
  (setq *watch-file* nil)
  (setq *watch-start-real-time* (get-internal-real-time))
  (setq *watch-start-run-time* (get-internal-run-time))
  (setq *watch-last-real-time* 0)
  (setq *watch-last-run-time* 0)
  (set-watch-count 0)
  (clear-memoize-call-array)
  (unless (and (ignore-errors
                 (setq *watch-file* (eval *watch-file-form*)))
               (stringp *watch-file*))
    (ofe "; WATCH: evaluation of *WATCH-FILE-FORM* failed to ~
          produce a string."))
  #+Clozure
  (progn
    (setq *watch-start-gc-count* (ccl::full-gccount))
    (setq *watch-start-gc-time* (ccl::gctime))
    (setq *watch-start-heap-bytes-allocated* (heap-bytes-allocated))
    (setq *watch-startup-process* ccl::*current-process*)
    (when (or force-dog (live-terminal-p))
      (setq *watch-dog-process*
        (ccl::process-run-function "watch-dog-process"
         (lambda ()
           (let (x)
             (loop (sleep *watch-sleep-seconds*)
                   (setq x (watch-count))
                   (when (watch-condition)
                     (ccl:process-interrupt *watch-startup-process*
                                            #'maybe-watch-dump)
                     (loop for i from 1 while (>= x (watch-count))
                           do (sleep *watch-sleep-seconds*))))))))
      (ofv "An invocation of (WATCH) has now started a new ~%; ~
            Aside:  Clozure Common Lisp thread, the ~
            *WATCH-DOG-PROCESS*, which~%; Aside:  calls ~
            (MAYBE-WATCH-DUMP) periodically, which writes to the ~
            file ~%; Aside:  whose name is the value of ~
            *WATCH-FILE*, viz.,~%; Aside:  ~a.~%(WATCH-KILL) kills ~
            the thread.~%"
         *watch-file*)))
  #+Clozure
  (watch-dump))


(defmacro defw (fn &rest r)
  `(defn ,fn ()
     (let ((fn (string-capitalize (symbol-name ',fn))))
       ,@r)))



(defmacro oft-wrm (str &rest r)
  `(oft ,str (or *print-right-margin* 70) ,@r))


(defn1 date-string ()
  (multiple-value-bind (sec mi h d mo y)
      (decode-universal-time (get-universal-time))
    (let (m)
      (cond ((> h 12)
             (setq m " p.m.")
             (setq h (- h 12)))
            (t (setq m " a.m.")))
      (ofn "~2,d:~2,'0d:~2,'0d~a ~4d/~d/~d"
           h mi sec m y mo d))))

(defw time-of-last-watch-update
  (oft-wrm "~v<~a~;~a~>" fn (date-string)))

(defun watch-real-time ()
  (/ (- (get-internal-real-time) *watch-start-real-time*)
     *float-internal-time-units-per-second*))

(defun watch-run-time ()
  (/ (- (get-internal-run-time) *watch-start-run-time*)
     *float-internal-time-units-per-second*))

(defw pons-calls/sec-run-time
  (let* ((c *pons-call-counter*)
         (ans
          (cond ((eql c 0) "No pons calls yet.")
                (t (ofn "~,1e" (round (/ c (+ .000001
                                              (watch-run-time)))))))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))

(defw pons-hits/calls
  (let* ((c *pons-call-counter*)
         (h (- c *pons-misses-counter*))
         (ans
          (cond ((eql c 0) "No pons calls yet.")
                (t (ofn "~,1e / ~,1e = ~,2f" h c (/ h c))))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))



#+Clozure
(defw gc-count ()
  (if *watch-file*
      (let ((h 0)
            (mi 0)
            (sec (floor (- (ccl::gctime) *watch-start-gc-time*)
                        internal-time-units-per-second)))
        (multiple-value-setq (mi sec) (floor sec 60))
        (multiple-value-setq (h mi) (floor mi 60))
        (oft-wrm "~v,20<~a~;~a.~;~a~;~2d:~2,'0d:~2,'0d.~>"
             fn
             (- (ccl::full-gccount) *watch-start-gc-count*)
             "Time in gc since watch start"
             h mi sec))))


(defw time-since-watch-start ()
  (if *watch-file*
      (multiple-value-bind (mi1 sec1)
          (floor (round (watch-real-time)) 60)
        (multiple-value-bind (h1 mi1) (floor mi1 60)
          (multiple-value-bind (mi2 sec2)
              (floor (round (watch-run-time)) 60)
            (multiple-value-bind (h2 mi2) (floor mi2 60)
              (oft-wrm "~v<Watch update ~a. ~
                ~;~a~;~2d:~2,'0d:~2,'0d.~;~a~;~2d:~2,'0d:~2,'0d.~>"
                       (watch-count) fn h1 mi1 sec1 "Run-time"
                   h2 mi2 sec2)))))))


#+Clozure
(defun make-watchdog (duration)

;   Thanks to Gary Byers for this!

   (let* ((done (ccl:make-semaphore))
          (current ccl:*current-process*))
      (ccl::process-run-function "watchdog"
        (lambda ()
          (or (ccl:timed-wait-on-semaphore done duration)
              (ccl:process-interrupt
               current #'error "Time exceeded"))))
      done))

#+Clozure
(defw number-of-cpus-on-this-machine
  (let* ((ans (ofn "~:d" (ccl::cpu-count))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))


(defw physical-memory-on-this-machine
  (let* ((ans (ofn "~:d" (physical-memory))))
    (oft-wrm "~v<~a~;~a bytes.~>" fn ans)))




#+Clozure
(defun bytes-used ()
  (multiple-value-bind (dynamic static library frozen-size)
      (ccl::%usedbytes)
    (declare (ignorable library))
    (let* ((sum (+ dynamic static library frozen-size))
           (stack-size (ccl::%stack-space))
           (id (ccl::getpid))
           (rwx-size (rwx-size)))
      (declare (ignorable sum))
      (oft

; (stat (proc-stat id))

;  ~%reserved:   ~15:d~ (ccl::%reservedbytes)

;  ~%library:   ~15:d  library

; ~%memfree:   ~15:d~29tfrom /proc/meminfo~
;  (* 1024 (meminfo "MemFree:")
; ~%swapfree:  ~15:d~29tfrom /proc/meminfo"
; (* 1024 (meminfo "SwapFree:")
; ~%rss:       ~15:d~29tfrom /proc/~a/stat - ram used~
;             (rss-size (* (getf stat :rss) ccl:*host-page-size*))
; ~%jobs:      ~15:d~29tfrom vmstat~" (number-procs-running)
; ~%load avg:  ~15f~29tone minute, from uptime" (load-average)

 "~%(bytes-used)~
  ~%dynamic:   ~15:d~29tlisp-heap-gc-threshold:    ~14:d~
  ~%stack:     ~15:d~29tmax-mem-usage:             ~14:d~
  ~%free:      ~15:d~29tgc-min-threshold:          ~14:d~
  ~%rwx:       ~15:d~29tfrom /proc/~a/maps - virtual used"

 dynamic               (ccl::lisp-heap-gc-threshold)
 stack-size            *max-mem-usage*
 (ccl::%freebytes)     *gc-min-threshold*
 rwx-size              id))))




(defun functions-that-may-be-too-fast-to-sensibly-profile ()
  (let ((ans (loop for fn in (profiled-functions)
                   when (< (total-time fn)
                           (* 1e-6 (number-of-calls fn)))
                   collect fn)))
    (when ans (oft "Too fast to sensibly profile?~%~a" ans))))






;; [Jared]: Removing this since it seems redundant with CSH and is, afaik, unused.

;; (defv *sh-process* nil

;;   "When not NIL, *SH-PROCESS* has as its value the Lisp process
;;   object for an underlying sh process.")

;; (defv *sh-temporary-file-name* nil

;;   "When not NIL, *SH-TEMPORARY-FILE-NAME* has as it value a stream
;;   via which an underlying sh process sends synchronizing info back to
;;   Lisp.")

;; #+Clozure
;; (defn1 sh-stop ()

;;   "(sh-stop) kills the subsidiary sh process if there is one."

;;   (ignore-errors
;;     (when (ccl::external-process-p *sh-process*)
;;       (ccl::signal-external-process *sh-process* 9)))
;;   (setq *sh-process* nil)
;;   (ignore-errors
;;     (when (and *sh-temporary-file-name*
;;                (probe-file *sh-temporary-file-name*))
;;       (delete-file *sh-temporary-file-name*)))
;;   (setq *sh-temporary-file-name* nil))

;; #+Clozure
;; (defv *sh-start-string*
;;   "tm=`mktemp /tmp/acl2-sh-temp.XXXXXX`; echo $tm")

;; #+Clozure
;; (defn1 sh-start ()

;;   "(SH-START) creates a subsidiary sh process.  SH-START
;;   is called automatically by SH."

;;   (sh-stop)
;;   (setq *sh-process*
;;     (ccl::run-program "/bin/sh" nil
;;                       :input :stream
;;                       :output :stream
;;                       :wait nil))
;;   (let ((is (ccl::external-process-input-stream *sh-process*)))
;;     (our-syntax
;;      (write-line *sh-start-string* is)
;;      (finish-output is)
;;      (setq *sh-temporary-file-name*
;;        (read-line
;;         (ccl::external-process-output-stream *sh-process*)
;;         nil
;;         :eof)) ; wait
;;      (cond ((probe-file *sh-temporary-file-name*)
;;             *sh-temporary-file-name*)
;;            (t (ofe "sh-start: failed."))))))

;; #+Clozure
;; (defun sh (&rest args)

;;   "SH is a raw Lisp function.  (SH) returns a status report on a lower
;;   'sh' shell process, which is created if necessary, and which, once
;;   created, is the value of the Lisp variable *SH-PROCESS*.

;;   On each call to SH, one sh shell command is executed.  The same sh
;;   process executes all the commands.  That is, a new process is not
;;   created for each command, but the same sh process is used
;;   repeatedly.  This may significantly reduce the copying overhead
;;   incurred by a call to FORK to create a new process under a big Lisp
;;   job, as the ACL2 function SYSTEM-CALL might on each call.

;;   (SH :STREAM arg1 ... argn) executes a single sh command, namely,
;;   the string obtained by placing spaces between the strings, symbols,
;;   or numbers arg1 ... argn.  A stream of the command's standard output
;;   is returned as the value of SH.  For example,

;;      (SH :STREAM '|gunzip -c foo.gz|)

;;   returns an open input stream that contains the ungzipped contents of
;;   the file 'foo.gz'.

;;   If arg1 is not :STREAM, (SH arg1 ... argn) executes one sh command
;;   exactly as in the :STREAM case, namely, the string obtained by
;;   placing spaces between the strings, symbols, or numbers arg1
;;   ... argn.  But the standard output of the command is printed into a
;;   string, which is returned as the value of SH.  If the last character
;;   of that output is a newline, it is not included in the string
;;   returned.

;;   The standard output from the command is diverted through a unique
;;   /tmp file, whose name is the value of the variable
;;   *SH-TEMPORARY-FILE-NAME*.

;;   If the command sends any output to error output, a Lisp ERROR is
;;   caused and the error output of the command is printed to Lisp's
;;   *STANDARD-OUTPUT*.

;;   SH is almost identical to CSH.

;;   For the best of hacking luck, each single SH command fed to SH
;;   should be only one line long, and should not involve any of the
;;   fancier SH characters such *, ~, !, =, |, <, >, &, \, {, }, single
;;   quote, semicolon, period, question mark, parentheses, square
;;   brackets, double quote, and backquote.  Stick to alphanumeric
;;   characters, space, and hyphen if possible.  Create a separate, small
;;   .sh file to do anything fancy involving sh and such punctuation
;;   characters.  See abc-iprove.csh for one example, which involves
;;   creating a temp file."

;;   (with-standard-io-syntax
;;    (pushnew 'sh-stop ccl::*save-exit-functions*)
;;    (unless (ccl::external-process-p *sh-process*) (sh-start))
;;    (prog*
;;     ((p *sh-process*)
;;      (command (if (eq (car args) :stream) (cdr args) args))
;;      (is (ccl::external-process-input-stream p))
;;      (os (ccl::external-process-output-stream p))
;;      (x nil))

;;     (unless args
;;       (return
;;        (list :status (ccl::external-process-status p)
;;              :process p
;;              :input-stream (ccl::external-process-input-stream p)
;;              :output-stream (ccl::external-process-output-stream p)
;;              :temp-file-name *sh-temporary-file-name*)))

;;     ;; It seems so peculiar to 'print' to an 'input' here, but input
;;     ;; and output are opposite on the other end.

;;     (write-string (args-spaced command) is)
;;     (write-line " > $tm < /dev/null ; echo" is)
;;     (finish-output is)
;;     (setq x (read-char os nil :eof))

;;     ;; If necessary, READ-CHAR will wait.

;;     (unless (and (eql x #\Newline) (null (listen os)))
;;       (loop while (characterp x) do
;;             (write-char x *error-output*)
;;             (force-output *error-output*)
;;             (setq x (read-char-no-hang os nil :eof)))
;;       (sh-stop)
;;       (ofe "SH: ~a." args))
;;     (return
;;      (cond
;;       ((eq :stream (car args))
;;        (open *sh-temporary-file-name*))
;;       (t (with-open-file
;;            (o *sh-temporary-file-name*)
;;            (with-output-to-string
;;              (s)
;;              (loop while
;;                    (and (not (eq :eof (setq x (read-char
;;                                                o nil :eof))))
;;                         (or (not (eql x #\Newline))
;;                             (not (eq :eof (peek-char
;;                                            nil o nil :eof)))))
;;                    do (write-char x s))))))))))





;; [Jared]: removing this, doesn't appear to be used

;; #+Clozure
;; (defun call-with-timeout (function duration)

;;   "(CALL-WITH-TIMEOUT function duration) calls FUNCTION on no
;;   arguments and returns its values unless more than DURATION seconds
;;   elapses before completion, in which case the FUNCTION computation is
;;   interrupted and calls ERROR.

;;   Thanks to Gary Byers for this beaut."

;;    (let* ((semaphore (make-watchdog duration)))
;;       (unwind-protect
;;           (funcall function)
;;         (ccl:signal-semaphore semaphore))))



;; [Jared]: removing these because they're no longer used

;; #+Clozure
;; (defun number-procs-running ()
;;   (with-standard-io-syntax
;;    (with-open-stream (s (csh :stream "vmstat"))
;;      (read-line s)
;;      (read-line s)
;;      (read s))))

;; #+Clozure
;; (defn1 load-average ()
;;   (let ((str (csh "uptime")))
;;     (let ((loc (search "load average: " str)))
;;       (values (read-from-string str nil nil :start (+ 14 loc))))))

;; #+Clozure
;; (defn pid-owner (&optional also-cmdline)
;;   (let ((str (csh "ps -A -o user,pid"))
;;         (ans nil)
;;         (line nil))
;;     (with-standard-io-syntax
;;      (with-input-from-string
;;       (s str)
;;       (read-line s nil nil)
;;       (loop while (setq line (read-line s nil nil))
;;             collect
;;             (let ((items
;;                    (with-input-from-string
;;                     (s line)
;;                     (loop for i below 2 collect
;;                           (ignore-errors (read s nil nil))))))
;;               (let ((owner (car items))
;;                     (pid (cadr items)))
;;                 (when (and (integerp pid)
;;                            (not (equal owner 'root)))
;;                   (let* ((cfile
;;                           (ignore-errors
;;                             (probe-file
;;                              (format nil "/proc/~a/cmdline" pid)))))
;;                     (when cfile
;;                       (let ((cmdline
;;                              (and also-cmdline
;;                                   cfile
;;                                   (with-open-file
;;                                     (s cfile)
;;                                     (read-line s nil nil)))))
;;                         (push (list pid owner cmdline) ans))))))))))
;;      (sort ans '< :key 'car)))

;; #+Clozure
;; (defn rss (&optional verbose)
;;   (with-standard-io-syntax
;;    (let ((ans nil))
;;      (loop for triple in (pid-owner) do
;;            (let ((items (proc-stat (car triple))))
;;              (let ((rss (getf items :rss)))
;;                (when (and (integerp rss) (> rss 1000))
;;                  (push (list (car triple)
;;                              (cadr triple)
;;                              rss
;;                              (getf items :comm))
;;                        ans)))))
;;      (setq ans (sort ans '> :key 'third))
;;      (when verbose
;;        (oft "~%pid       user               rss comm")
;;        (loop for x in ans do
;;              (apply 'format
;;                     *standard-output*
;;                     "~%~a~10t~a~20t~12:d~30t~a"
;;                     x))
;;        (oft "~%from man proc: rss = Resident Set Size.  Number of ~
;;           pages in real memory.")
;;        (oft "~%host-page-size:  ~:d" CCL:*HOST-PAGE-SIZE*))
;;      ans)))


;; [Jared] removing this because it lets me remove more stuff and is only
;; incidentally used in watch

;; #+Clozure
;; (defn print-ancestry (&optional (p (ccl::getpid)))
;;   (with-open-stream
;;    (s (csh :stream "ps ww -A -o pid,ppid,cmd"))
;;    (let (first l ans trip)
;;      (loop (setq first (read s nil nil))
;;            (when (null first) (return nil))
;;            (push (list first (read s nil nil) (read-line s nil nil))
;;                  l))
;;      (loop (setq trip (assoc p l))
;;            (when (null trip) (return nil))
;;            (push (caddr trip) ans)
;;            (setq p (cadr trip)))
;;      (setq ans (nreverse ans))
;;      (loop for i from 0 while ans do
;;            (terpri)
;;            (loop repeat i do (write-char #\Space))
;;            (princ (pop ans))))))

;; #+Clozure
;; (defn print-fds (&optional (p (ccl::getpid)))
;;   (loop for x in (directory (ofn "/proc/~a/fd/*" p))
;;         do
;;         (let ((n (namestring x)))
;;           (unless (or (eql #\/ (char n (1- (length n))))
;;                       (looking-at "/dev/pts/" n)
;;                       (looking-at "/scratch/" n)
;;                       (looking-at "/proc/" n))
;;             (fresh-line)
;;             (princ n)))))

;; #+Clozure
;; (defun watch-shell-command (&rest args)
;;   (let* ((as (args-spaced args))
;;          (output (csh as)))
;;     (oft-wrm "~v<~a~;~a~>" as output)))




;; [Jared] Removing CSH since, with the above, we can get rid of it,
;; and we generally should probably be using tshell anyway

;; ;;   CSH

;; ;
;; ; Here is a quite simple version of OPEN-GZIPPED-FILE that is fine to
;; ; use in CCL for a few files, but perhaps not for thousands of files
;; ; because FORK can take a serious amount of time for a big CCL job such
;; ; as ACL2 since a copy is made by FORK of the entire job.
;; ;
;; ; (defun open-gzipped-file (name)
;; ;    (ccl::external-process-output-stream
;; ;      (ccl::run-program "gunzip" (list "-c"  name)
;; ;                        :output :stream :wait nil)))
;; ;
;; ; To eliminate FORK as a source of such inefficiency, we provide the
;; ; function CSH, which establishes a lasting subsidiary cshell process
;; ; executing a 'read-and-execute one CSH line' loop.  It may be a good
;; ; idea to call CSH very early, even before you need it, simply to get
;; ; that process running when you can, i.e., when your image is small
;; ; enough.

;; (defv *csh-process* nil

;;   "When not NIL, *CSH-PROCESS* has as its value the Lisp process
;;   object for an underlying csh process.")

;; (defv *csh-temporary-file-name* nil

;;   "When not NIL, *CSH-TEMPORARY-FILE-NAME* has as its value a stream
;;   via which an underlying csh process sends synchronizing info back to
;;   Lisp.")

;; #+Clozure
;; (defn1 csh-stop ()

;;   "(csh-stop) kills the subsidiary csh process if there is one."

;;   (ignore-errors
;;     (when (ccl::external-process-p *csh-process*)
;;       (ccl::signal-external-process *csh-process* 9)))
;;   (setq *csh-process* nil)
;;   (ignore-errors
;;     (when (and *csh-temporary-file-name*
;;                (probe-file *csh-temporary-file-name*))
;;       (delete-file *csh-temporary-file-name*)))
;;   (setq *csh-temporary-file-name* nil))

;; #+Clozure
;; (defv *csh-start-string*
;;   "set tm=`mktemp /tmp/acl2-csh-temp.XXXXXX`; echo $tm")

;; #+Clozure
;; (defn1 csh-start ()

;;   "(CSH-START) creates a subsidiary csh process.  CSH-START
;;   is called automatically by CSH."

;;   (csh-stop)
;;   (setq *csh-process*
;;     (ccl::run-program "/bin/csh" (list "-f")
;;                       :input :stream
;;                       :output :stream
;;                       :wait nil))
;;   (let ((is (ccl::external-process-input-stream *csh-process*)))
;;     (our-syntax
;;      (write-line *csh-start-string* is)
;;      (finish-output is)
;;      (setq *csh-temporary-file-name*
;;        (read-line
;;         (ccl::external-process-output-stream *csh-process*)
;;         nil
;;         :eof)) ; wait
;;      (cond ((ignore-errors
;;               (probe-file *csh-temporary-file-name*))
;;             *csh-temporary-file-name*)
;;            (t (ofe "csh-start: failed."))))))

;; (defn1 args-spaced (args)
;;   (cond ((atom args) "")
;;         ((and (atom (cdr args))
;;               (stringp (car args)))
;;          (car args))
;;         (t (with-output-to-string (s)
;;              (loop for tail on args do
;;                    (our-syntax
;;                     (princ (car tail) s)
;;                     (when (cdr tail) (write-char #\Space s))))))))

;; #+Clozure
;; (defun csh (&rest args)

;;   "CSH is a raw Lisp function.  Called with no arguments, (CSH)
;;   returns a status report on a process, which is created if necessary,
;;   and which, once created, is the value of the Lisp variable
;;   *CSH-PROCESS*.

;;   On each call to CSH, one csh shell command is executed.  Unless for
;;   some unusual reason the process is killed, the same process executes
;;   all the commands.  That is, to repeat, a new process is not created
;;   for each command, but the same csh process is used repeatedly.  This
;;   may significantly reduce the copying overhead of a call to FORK to
;;   create a new process under a big Lisp job, as the ACL2 function
;;   SYSTEM-CALL does on each call.

;;   (CSH :STREAM arg1 ... argn) executes a single csh command, namely,
;;   the string obtained by placing spaces between the strings, symbols,
;;   or numbers arg1 ... argn.  A stream of the command's standard output
;;   is returned as the value of CSH.  For example,

;;      (CSH :STREAM '|gunzip -c foo.gz|)

;;   returns an open input stream that contains the ungzipped contents of
;;   the file 'foo.gz'.

;;   If arg1 is not :STREAM, (CSH arg1 ... argn) executes one csh command
;;   exactly as in the :STREAM case, namely, the string obtained by
;;   placing spaces between the strings, symbols, or numbers arg1
;;   ... argn.  But the standard output of the command is printed into a
;;   string, which is returned as the value of CSH.  If the last
;;   character of that output is a newline, it is not included in the
;;   string returned.

;;   The standard output from the command is diverted through a unique
;;   /tmp file, whose name is the value of the variable
;;   *CSH-TEMPORARY-FILE-NAME*.

;;   If the command sends any output to error output, a Lisp ERROR is
;;   caused and the error output of the command is printed to Lisp's
;;   *STANDARD-OUTPUT*.

;;   Each single csh command fed to CSH should be only one line long, and
;;   should not involve any of the fancier csh characters such *, ~, !,
;;   =, |, <, >, &, \, {, }, single quote, semicolon, period, question
;;   mark, parentheses, square brackets, double quote, and backquote.
;;   Stick to alphanumeric characters, space, and hyphen if possible.
;;   Create a separate, small .csh file to do anything fancy involving
;;   csh and those punctuation characters.  See abc-iprove.csh for one
;;   example, which involves creating a temp file."

;;   ;; CSH is at least as dangerous as SYSCALL, so would need a
;;   ;; trust-tag if made into an ACL2 command.

;;   ;; Implementation note: For CSH to work, the csh shell command
;;   ;; 'echo' with no arguments must 'flush' its output, in addition to
;;   ;; printing a newline, or in Lisp terminology, 'echo' must
;;   ;; 'finish-output'.  We believe 'echo' does that, but we have not
;;   ;; tracked down where it officially says so.  If 'echo' does not
;;   ;; flush its output, then the READ-CHAR below may wait forever.
;;   ;; Probably, adding a 'sync' command would guarantee the flushing.

;;   (with-standard-io-syntax
;;    (pushnew 'csh-stop ccl::*save-exit-functions*)
;;    (unless (ccl::external-process-p *csh-process*) (csh-start))
;;    (prog*
;;     ((p *csh-process*)
;;      (command (if (eq (car args) :stream) (cdr args) args))
;;      (is (ccl::external-process-input-stream p))
;;      (os (ccl::external-process-output-stream p))
;;      (x nil))

;;     (unless args
;;       (return
;;        (list :status (ccl::external-process-status p)
;;              :process p
;;              :input-stream (ccl::external-process-input-stream p)
;;              :output-stream (ccl::external-process-output-stream p)
;;              :temp-file-name *csh-temporary-file-name*)))

;;     ;; It seems so peculiar to 'print' to an 'input' here, but input
;;     ;; and output are opposite on the other end.

;;     (write-string (args-spaced command) is)
;;     (write-line " > $tm < /dev/null ; echo" is)
;;     (finish-output is)
;;     (setq x (read-char os nil :eof))

;;     ;; If necessary, READ-CHAR will wait.

;;     (unless (and (eql x #\Newline) (null (listen os)))
;;       (loop while (characterp x) do
;;             (write-char x *error-output*)
;;             (force-output *error-output*)
;;             (setq x (read-char-no-hang os nil :eof)))
;;       (csh-stop)
;;       (ofe "CSH: ~a." args))
;;     (return
;;      (cond
;;       ((eq :stream (car args)) (open *csh-temporary-file-name*))
;;       (t (with-open-file (o *csh-temporary-file-name*)
;;            (with-output-to-string
;;              (s)
;;              (loop while
;;                    (and (not (eq :eof (setq x (read-char
;;                                                o nil :eof))))
;;                         (or (not (eql x #\Newline))
;;                             (not (eq :eof (peek-char
;;                                            nil o nil :eof)))))
;;                    do (write-char x s))))))))))






;; [Jared]: Removing all profiler-if and setup-smashed-if stuff.  Sol and I
;; don't think we have ever used it, and it seems iffy.  I've just replaced
;; uses of profiler-if, etc., above, with their normal Lisp counterparts.

;; ; PROFILER-IF

;; ; See also comments in SETUP-SMASHED-IF.

;; (defg *form-ht* (make-hash-table :test 'eq))

;; (defg *ignore-form-ht* (make-hash-table :test 'eq))

;; (declaim (hash-table *form-ht* *ignore-form-ht*))

;; (defmacro profiler-if (test true &optional false)

;;   "Semantically, PROFILER-IF is the same as IF.  However, the
;;   execution of the PROFILER-IF macro also puts the IF form into
;;   *IGNORE-FORM-HT* so that the compiler macro for IF will not consider
;;   'fixing' it with code to monitor which branch of the IF is taken.
;;   We use PROFILER-IF to avoid monitoring of code that we have
;;   introduced into the user's code for the purpose of profiling."

;;   (let ((val `(if ,test ,true ,false)))
;;     #+Clozure (setf (gethash val *ignore-form-ht*) t)
;;     val))

;; (defmacro profiler-cond (&rest r)
;;   (cond ((null r) nil)
;;         (t `(profiler-if ,(caar r)
;;                      (progn ,@(cdar r))
;;                      (profiler-cond ,@(cdr r))))))

;; (defmacro profiler-and (&rest r)
;;   (cond ((null r) t)
;;         ((null (cdr r)) (car r))
;;         (t `(profiler-if ,(car r)
;;                      (profiler-and ,@(cdr r))
;;                      nil))))

;; (defmacro profiler-or (&rest r)
;;   (cond ((null r) nil)
;;         ((null (cdr r)) (car r))
;;         (t (let ((temp (make-symbol "TEMP")))
;;              `(let ((,temp ,(car r)))
;;                 (profiler-if ,temp
;;                          ,temp
;;                          (profiler-or ,@(cdr r))))))))

;; (defmacro profiler-when (test &rest r)
;;   `(profiler-if ,test (progn ,@r)))

;; (defmacro profiler-unless (test &rest r)
;;   `(profiler-if (not ,test) (progn ,@r)))



;; ; PRINL

;; (defmacro prinl (&rest r)

;;   "PRINL is for debugging.  In general, PRINL PRIN1s the members of r
;;   followed by their values to *STANDARD-OUTPUT*.  The values are first
;;   followed by =>, to indicate evaluation.

;;   For example, (prinl a b (+ a b)) might print:
;;     A => 1
;;     B => 2
;;     (+ A B) => 3
;;   PRINL returns the principal value of the last member of r.  PRINL
;;   does not evaluate the members of r that are neither symbols nor
;;   conses, but it does PRINC those members.  PRINL evalutes (oft ...)
;;   forms, but does not do the printing twice."

;;   (let ((tem (make-symbol "TEM"))
;;         (tem2 (make-symbol "TEM2")))
;;     `(our-syntax-nice
;;       (let ((,tem nil) (,tem2 nil))
;;         (declare (ignorable ,tem2))
;;         ,@(loop for x in r collect
;;                 (cond
;;                  ((or (symbolp x)
;;                       (and (consp x) (not (eq (car x) 'oft))))
;;                   `(progn (oft "~&~:a =>~40t" ',x)
;;                           (setq ,tem ,x)
;;                           (cond ((integerp ,tem)
;;                                  (setq ,tem2 (ofn "~20:d" ,tem)))
;;                                 ((floatp ,tem)
;;                                  (setq ,tem2 (ofn "~20,4f" ,tem)))
;;                                 ((hash-table-p ,tem)
;;                                  (let ((l nil))
;;                                    (maphash (lambda (k v)
;;                                               (push (cons k v) l))
;;                                             ,tem)
;;                                    (setq l (nreverse l))
;;                                    (setq l (list* 'hash-table-size
;;                                                   (hash-table-size
;;                                                    ,tem)
;;                                                   l))
;;                                    (setq ,tem l)))
;;                                 (t (setq ,tem2 (ofn "~a" ,tem))))
;;                           (cond ((and (stringp ,tem2)
;;                                       (< (length ,tem2) 40))
;;                                  (oft "~a" ,tem2))
;;                                 (t (oft "~%  ")
;;                                    (prin1 ,tem *terminal-io*)))))
;;                  ((and (consp x) (eq (car x) 'oft)) x)
;;                  (t `(oft "~&~a" (setq ,tem ',x)))))
;;         ,tem))))


;; [Jared]: I think I'll sleep better knowing that we aren't doing THIS:


;; ; The compiler macro for IF in the Clozure Common Lisp sources circa 2008:

;; ; (define-compiler-macro if (&whole call test true &optional false
;; ;                                   &environment env)
;; ;   (multiple-value-bind (test test-win) (nx-transform test env)
;; ;     (multiple-value-bind (true true-win) (nx-transform true env)
;; ;       (multiple-value-bind (false false-win) (nx-transform false env)
;; ;         (if (or (quoted-form-p test) (self-evaluating-p test))
;; ;           (if (eval test)
;; ;             true
;; ;             false)
;; ;           (if (or test-win true-win false-win)
;; ;             `(if ,test ,true ,false)
;; ;             call))))))

;; #+Clozure
;; (defun setup-smashed-if ()

;; ; SETUP-SMASHED-IF creates COMPILER-MACRO for IF and OR via calls of
;; ; DEFINE-COMPILER-MACRO, stores the compiler macros, and restores the
;; ; previous values.

;;   (let ((ccl::*nx-safety* 0)
;;         (ccl::*nx-speed* 3))

;; ; Warning: In Clozure, (DEFINE-COMPILER-MACRO IF ...) 'seems' to do
;; ; nothing, not even cause an error, if SAFETY=3.

;; ; According to the ANSI standard, one is not supposed to mess with a
;; ; compiler macro for any symbol in the Common Lisp package.  So the
;; ; following hacking of the compiler macros for IF and OR is very
;; ; dubious.  But it seemed easier than writing a code walker for all of
;; ; Common Lisp, with its 50 or so special forms.  Our purpose this is
;; ; to help get statistical performance information, and that is all
;; ; that justifies this dangerous behavior.

;;  (when (and *unsmashed-if* (null *smashed-if*))
;;       (unwind-protect
;;         (progn

;; (define-compiler-macro if
;;   (&whole call test true &optional false &environment env)
;;   (declare (ignorable env))
;;   (when *trace-if-compiler-macro*
;;     (prinl call test true false))
;;   (let
;;     ((ans
;;       (cond
;;        ((gethash call *form-ht*)

;; ; According to the ANSI standard, there is no guarantee that a Common
;; ; Lisp compiler macro ever gets called!  We hope and believe that
;; ; Clozure's compiler arranges that every IF forms gets processed by
;; ; the compiler macro for IF so that we can 'IF-fix' it, when
;; ; approriate.  A form in *FORM-HT* is an IF form that has been
;; ; 'IF-fixed': both its true and false branch first increment a special
;; ; counter for the the number of times that each branch is taken.  We
;; ; do not want to 'IF-fix' again a form that has already been
;; ; 'IF-fixed'; if it has, the new compiler macro for IF returns it as
;; ; the answer.  Any caller of this compiler macro for IF will know, by
;; ; the ANSI rules for compiler macros, not to hope for any further
;; ; improvement on the form.  If an ordinary macro (not a compiler
;; ; macro) returned its input, macro expansion would enter an immediate
;; ; infinite loop.  It is lucky for us that Clozure translates COND and
;; ; CASE into IF via macros.

;;         call)
;;        (t

;; ; Although it may seem very hard to tell, we do closely follow the
;; ; code for the compiler-macro for IF from the Clozure compiler.  See
;; ; that code below.

;;         (multiple-value-bind (test test-win)
;;             (ccl::nx-transform test env)
;;         (multiple-value-bind (true true-win)
;;             (ccl::nx-transform true env)
;;         (multiple-value-bind (false false-win)
;;             (ccl::nx-transform false env)
;;           (cond
;;            ((or (ccl::quoted-form-p test)
;;                 (ccl::self-evaluating-p test))
;;             (when *trace-if-compiler-macro*
;;               (prinl "IF test already settled"))
;;             (if (eval test) true false))
;;            ((gethash call *ignore-form-ht*)

;; ; Forms in *IGNORE-FORM-HT* are not to be 'fixed' because they are
;; ; part of the profiling machinery.  See the definition of PROFILER-IF
;; ; and those macros that use PROFILER-IF, such as PROFILER-AND,
;; ; PROFILER-OR, PROFILER-WHEN, and PROFILER-UNLESS.

;;             (when *trace-if-compiler-macro*
;;               (prinl "ignore case" test true false))
;;             (cond ((or test-win true-win false-win)
;;                    (let ((new `(if ,test ,true ,false)))

;; ; We make ignorability contagious.

;;                      (setf (gethash new *ignore-form-ht*) t)
;;                      new))
;;                   (t call)))
;;            (t
;;             (incf *if-counter*)
;;             (when *trace-if-compiler-macro*
;;               (prinl "*IF-COUNTER* incremented"
;;                      call test true false))

;; ; Our code here would be much simpler if in place of *IF-TRUE-ARRAY*
;; ; and *IF-FALSE-ARRAY* we used two adjustable arrays and the function
;; ; VECTOR-PUSH-EXTEND.  However, an adjustable array is not a
;; ; SIMPLE-ARRAY, and so we possibly could lose efficiency, which we
;; ; need when incrementing IF-branch counters.

;;             (when (>= *if-counter* (length *if-true-array*))
;;               (let ((ar (make-array
;;                          (+ (length *if-true-array*) 1000)
;;                          :element-type 'mfixnum
;;                          :initial-element -1)))
;;                 (declare (type (simple-array mfixnum (*)) ar))
;;                 (loop for i fixnum
;;                       below (length *if-true-array*)
;;                       do (setf (aref ar i)
;;                                (aref *if-true-array* i)))
;;                 (setq *if-true-array* ar)))
;;             (when (>= *if-counter* (length *if-false-array*))
;;               (let ((ar (make-array (+ (length *if-false-array*)
;;                                        1000)
;;                                     :element-type 'mfixnum
;;                                     :initial-element -1)))
;;                 (declare (type (simple-array mfixnum (*)) ar))
;;                 (loop for i fixnum
;;                       below (length *if-false-array*)
;;                       do (setf (aref ar i)
;;                                (aref *if-false-array* i)))
;;                 (setq *if-false-array* ar)))
;;             (setf (aref *if-true-array* *if-counter*) 0)
;;             (setf (aref *if-false-array* *if-counter*) 0)
;;             (let ((new-call `(if ,test
;;                                  (progn
;;                                    (very-very-unsafe-aref-incf
;;                                     *if-true-array*
;;                                     ,*if-counter*)
;;                                    ,true)
;;                                (progn
;;                                  (very-very-unsafe-aref-incf
;;                                   *if-false-array*
;;                                   ,*if-counter*)
;;                                  ,false))))

;; ; The immediately preceding backquoted form is what we call the
;; ; 'IF-fixing' of an expression.

;;               (when *trace-if-compiler-macro*
;;                 (prinl new-call call))
;;               (setf (gethash new-call *form-ht*)
;;                     (list* *if-counter*
;;                            *current-compiler-function*
;;                            call))
;;               new-call))))))))))
;;     (when *trace-if-compiler-macro* (prinl ans))
;;     ans))
;; (setq *smashed-if* (compiler-macro-function 'if)))
;; (setf (compiler-macro-function 'if) *unsmashed-if*))

;; (unwind-protect
;;   (progn

;; ; Apparently some times in CCL compilation, OR is not expanded to IF,
;; ; so we force it here.

;; (define-compiler-macro or (&whole call &rest r &environment env)
;;   (declare (ignore r) (ignorable env))
;;   (cond ((null (cdr call)) nil)
;;         ((null (cddr call)) (cadr call))
;;         ((null (cdddr call))
;;          (cond ((atom (cadr call))
;;                 `(if ,(cadr call)
;;                      ,(cadr call)
;;                    ,(caddr call)))
;;                (t (let ((v (gensym)))
;;                     `(let ((,v ,(cadr call)))
;;                        (if ,v ,v ,(caddr call)))))))
;;         (t (cond ((atom (cadr call))
;;                   `(if ,(cadr call) ,(cadr call) (or ,@(cddr call))))
;;                  (t (let ((v (gensym)))
;;                       `(let ((,v ,(cadr call)))
;;                          (if ,v ,v (or ,@(cddr call))))))))))

;; (setq *smashed-or* (compiler-macro-function 'or)))
;; (setf (compiler-macro-function 'or) *unsmashed-or*))

;; )))





;; [Jared]: removing watch-if stuff

;  WATCH-IF

;; (defg *if-counter* -1)

;; (declaim (type (integer -1 1152921504606846975) *if-counter*))

;; (defg *if-true-array* (make-array 2000
;;                                   :element-type
;;                                   '(integer -1 1152921504606846975)
;;                                   :initial-element -1))

;; (defg *if-false-array* (make-array 2000
;;                                    :element-type
;;                                    '(integer -1 1152921504606846975)
;;                                    :initial-element -1))

;; (declaim (type (simple-array (integer -1 1152921504606846975) (*))
;;                *if-true-array* *if-false-array*))


;; #+Clozure
;; (defg *trace-if-compiler-macro* nil)

;; #+Clozure
;; (defg *watch-if-branches-ht* (make-hash-table :test 'eq))

;; #+Clozure
;; (defg *watch-if-branches-taken-ht* (make-hash-table :test 'eq))

;; (declaim (hash-table *watch-if-branches-ht*
;;                      *watch-if-branches-taken-ht*))

;; (defv *report-ifs* t
;;   "If *REPORT-ON-IFS* is not NIL, information about IF coverage is
;;   printed for those functions memoized with :WATCH-IFS option T.")



;  COMPILER MACRO for IF

;; #+Clozure
;; (ccl::advise ccl::compile-named-function
;;              (when (and (consp ccl::arglist)
;;                         (consp (cdr ccl::arglist))
;;                         (consp (cddr ccl::arglist))
;;                         (symbolp (caddr ccl::arglist)))
;;                (clrhash *ignore-form-ht*)
;;                (setq *current-compiler-function*
;;                  (caddr ccl::arglist)))
;;              )

;; #+Clozure
;; (defun if-report (&optional fn stream)

;;   "(IF-REPORT) prints information about the execution of every branch
;;   of every IF, COND, AND, OR, CASE, WHEN, and UNLESS form of every
;;   memoized/profiled function that was memoized with :WATCH-IFS
;;   non-NIL.  (IF-REPORT fn) prints the same information, but only about
;;   the given function name, FN."

;;   (compute-calls-and-times)
;;   (let ((*print-level* 4)
;;         (*print-length* 4)
;;         (*print-pretty* t)
;;         last-fn n (ifs-found 0) (if-true 0) (if-false 0)
;;         (not-called 0)
;;         (called 0))
;;     (when (>= *if-counter* 0)
;;       (format stream "~2%Report on IF branches taken.")
;;       (let ((form-ar (make-array (the fixnum (1+ *if-counter*))
;;                                  :initial-element 0)))
;;         (declare (type (simple-array t (*)) form-ar))
;;         (maphash (lambda (k v) (declare (ignore k))
;;                    (when (or (null fn)
;;                              (eq (cadr v) fn))
;;                      (setf (aref form-ar (car v))
;;                            (cons (cddr v) (cadr v)))))
;;                  *form-ht*)
;;         (let ((top *if-counter*)
;;               ref)
;;           (declare (type fixnum top))
;;           (loop
;;            for i from 0 to top
;;            unless (eql 0 (setq ref (aref form-ar i)))
;;            do
;;            (let ((call (car ref))
;;                  (fn (cdr ref)))
;;              ;; ref has the form
;;              ;; (orig-call . function)
;;              (cond ((not (eq fn last-fn))
;;                     (setq n (number-of-calls fn))
;;                     (if (eq n 0)
;;                         (incf not-called)
;;                       (incf called))
;;                     (format stream "~2%~a was called ~a time~:P."
;;                          fn n)
;;                     (setq last-fn fn)))
;;              (cond
;;               ((> n 0)
;;                (incf ifs-found)
;;                (cond
;;                 ((eql 0 (aref *if-true-array* i))
;;                  (cond
;;                   ((eql 0 (aref *if-false-array* i))
;;                    (format stream
;;                            "~%Neither branch of ~%~a~%was taken."
;;                            call))
;;                   (t (incf if-true)
;;                      (format
;;                       stream
;;                       "~%The true branch of ~%~a~%was not taken."
;;                       call))))
;;                 ((eql 0 (aref *if-false-array* i))
;;                  (incf if-false)
;;                  (format stream
;;                          "~%The false branch of ~%~a~%was not taken."
;;                          call))
;;                 (t (incf if-true) (incf if-false))))))))
;;         (format stream
;;                 "~3%~:d ~10tnumber of functions called.~
;;               ~%~:d ~10tnumber of functions not called.~
;;               ~%~,2f% ~10tpercentage of functions called.~
;;               ~%~:d ~10tnumber of branches taken.~
;;               ~%~:d ~10tnumber of branches not taken.~
;;               ~%~,2f% ~10tpercentage of branches taken.
;;               ~%"
;;                 called
;;                 not-called
;;                 (if (eql (+ called not-called) 0)
;;                     100
;;                   (* 100
;;                      (/ called
;;                         (float (+ called not-called)))))
;;                 (+ if-true if-false)
;;                 (- (* 2 ifs-found) (+ if-true if-false))
;;                 (if (eql ifs-found 0)
;;                     100
;;                   (* 100
;;                      (float
;;                       (/ (+ if-true if-false)
;;                          (* 2 ifs-found))))))
;;         (format stream "~2%End of report on IF branches taken.~%")))))

;; #+Clozure
;; (defun dump-if-report (&optional (out "if-report.text"))
;;   (with-open-file (stream
;;                    out
;;                    :direction :output
;;                    :if-exists :supersede)
;;     (if-report stream))
;;   "if-report.text")


; (defg *undocumented-symbols* nil)





;; [Jared]: we probably don't need to implement our own raw-lisp help system.



;; (defn1 first-string (l)
;;   (loop for x in l when (stringp x) do (return x)))


;; (defn1 print-some-documentation (x)
;;   (let ((state *the-live-state*)
;;         (types-of-documentation
;;          '(compiler-macro function
;;                           method-combination
;;                           setf structure type variable
;;                           t)))

;; ; 0. Print it, evaluate it, and print the value, if possible.

;;     (oft "~&~%~a" x)
;;     (let* ((avrc (cons nil nil))
;;            (value avrc))
;;       (cond ((symbolp x)
;;              (cond ((boundp x)
;;                     (setq value (symbol-value x)))
;;                    ((fboundp x) nil)
;;                    (t (setq value "unbound"))))
;;             (t (setq value "error-in-evaluation")
;;                (ignore-errors
;;                  (setq value
;;                    (multiple-value-list (eval x))))))
;;       (cond ((not (eq value avrc))
;;              (when (and (consp value) (null (cdr value)))
;;                (setq value (car value)))
;;              (let ((str (format nil "~a" value)))
;;                (cond ((numberp value) (oft " => ~:d." value))
;;                      ((> (length str) 40)
;;                       (oft " =>~%~a." str))
;;                      (t (oft " => ~a." str)))))
;;             (t (oft "."))))
;;     (cond
;;      ((not (symbolp x)) nil)
;;      ((get-doc-string x state)

;; ; 1. For a symbol with regular ACL2 documentation, use :doc!.

;;       (oft "~%:doc! ")
;;       (let ((*acl2-unwind-protect-stack*
;;              (cons nil *acl2-unwind-protect-stack*)))
;;         (doc!-fn x state)))
;;      (t (let* ((tem nil)
;;                (found nil)
;;                (w (w state))
;;                (def (first-string (cltl-def-from-name x w))))
;;           (cond
;;            (def

;; ; 2. Else, for an ACL2 function symbol with a DOC string, print it.

;;             (oft "~%(first-string (cltl-def-from-name '~a (w ~
;;                    *the-live-state*))) =>~%~a"
;;                  x def))
;;            (t

;; ; 3. Else, for a symbol with some Common Lisp DOCUMENTATION, print
;; ; that.

;;             (loop for type in types-of-documentation
;;                   when (setq tem (documentation x type)) do
;;                   (oft "~%(documentation '~a '~a) => ~% ~a"
;;                        type x tem)
;;                   (setq found t))
;;             (loop for type-pair in '((function saved-function)
;;                                      (variable saved-variable))
;;                   when (and (null (documentation x (car type-pair)))
;;                             (setq tem (documentation
;;                                        x
;;                                        (cadr type-pair))))
;;                   do
;;                   (oft "~%(documentation '~a '~a) => ~% ~a"
;;                        (cadr type-pair) x tem)
;;                   (setq found t))
;;             (cond ((null found)

;; ; 4. Else, call DESCRIBE.

;;                    ;; (pushnew x *undocumented-symbols*)

;;                    (oft "~%(describe '~a) =>~%" x)
;;                    (describe x))))))))))

;; (defmacro print-documentation (&rest r)

;;   "(PRINT-DOCUMENTATION x) prints out some things about the symbols in
;;   r, such as values and documentation."

;;   `(progn
;;      (oft "~%For further information about these ~a items, see ~
;;            below.~%"
;;           (length ',r))
;;      (loop for x in ',r as i from 1 do
;;            (oft "~% ~3d.~4t~a" i x))
;;      (terpri)
;;      (terpri)
;;      (mapc 'print-some-documentation ',r)
;;      (values)))

;; (defn1 watch-help ()

;;   "(WATCH-HELP) prints some documentation for WATCH, MEMOIZE, PROFILE,
;;   etc."

;;   (print-documentation
;;    watch
;;    watch-dump
;;    #+Clozure maybe-watch-dump
;;    watch-kill

;;    memoize-summary
;;    memoized-values
;;    *memoize-summary-order-list*
;;    *memoize-summary-limit*
;;    *memoize-summary-order-reversed*
;;    hons-acons-summary
;;    if-report

;;    #+Clozure bytes-allocated
;;    hons-calls
;;    hons-statistics
;;    hons-summary
;;    number-of-memoized-entries
;;    number-of-mht-calls
;;    print-call-stack
;;    symbol-name-order

;;    clear-memoize-call-array
;;    clear-memoize-tables
;;    clear-memoize-table

;;    profile
;;    profile-acl2
;;    profile-all
;;    profile-file

;;    memoize
;;    memoize-fn

;;    pons-summary
;;    print-call-stack

;;    unmemoize
;;    unmemoize-all
;;    unmemoize-profiled

;;    print-documentation
;;    compact-print-file
;;    compact-read-file

;;    *watch-items*
;;    *watch-forms*
;;    *watch-file-form*
;;    *watch-string*
;;    *watch-file*
;;    *watch-startup-process*
;;    *watch-last-real-time*
;;    *watch-last-run-time*
;;    *watch-real-seconds-between-dumps*
;;    #+Clozure
;;    *watch-lock-ht*

;;    #+Clozure
;;    *watch-dog-process*
;;    #+Clozure
;;    watch-kill

;;    bytes-allocated
;;    bytes-allocated/call
;;    event-number
;;    execution-order
;;    hits/calls
;;    hons-calls
;;    pons-calls
;;    number-of-calls
;;    number-of-hits
;;    number-of-memoized-entries
;;    number-of-mht-calls
;;    symbol-name-order
;;    time-for-non-hits/call
;;    time/call
;;    total-time

;;    resize-memo
;;    resize-pons

;;    ))



;; This stuff is never used

;; (defg *gnu-linux-proc-stat-fields*
;;   '((:pid "Process ID.")
;;     (:comm "Filename of executable.")
;;     (:state "Run,Sleep,D=Wait,Zombie,Traced or stopped,W=paging.")
;;     (:ppid "PID of parent.")
;;     (:pgrp "Process group ID.")
;;     (:session "Session ID.")
;;     (:tty_nr "TTY.")
;;     (:tpgid "Process group ID of tty owner.")
;;     (:flags "Kernel flags word.")
;;     (:minflt "Minor faults no loading from disk.")
;;     (:cminflt "Minor faults of waited-for children.")
;;     (:majflt "Major faults loading from disk.")
;;     (:cmajflt "Major faults of waited-for children.")
;;     (:utime "User time.")
;;     (:stime "Kernel time.")
;;     (:cutime "User time of waited-for children.")
;;     (:cstime "Kernel time of waited-for children.")
;;     (:priority "Nice+15.")
;;     (:nice "Nice. 19 (nicest) to -19 (not  nice to others).")
;;     (:zero "Always 0.")
;;     (:itrealvalue "Time before SIGALRM.")
;;     (:starttime "Time started after system boot.")
;;     (:vsize "Virtual memory size.")
;;     (:rss "RSS - pages in real memory.")
;;     (:rlim "RSS limit.")
;;     (:startcode "Address above which program text can run.")
;;     (:endcode "Address below which program text can run.")
;;     (:startstack "Address of start of the stack.")
;;     (:kstkesp "ESP (:stack pointer).")
;;     (:kstkeip "EIP (:instruction pointer).")
;;     (:signal "Bitmap of pending signals.")
;;     (:blocked "Bitmap of blocked signals.")
;;     (:sigignore "Bitmap of ignored signals.")
;;     (:sigcatch "Bitmap of caught signals.")
;;     (:wchan "Channel in which waiting.")
;;     (:nswap "(not maintained).")
;;     (:cnswap "(not maintained).")
;;     (:exit_signal "To be sent to parent when we die.")
;;     (:processor "CPU number last executed on.")
;;     (:rt_priority "Real-time scheduling.")
;;     (:policy "Scheduling.")))






;; (defn print-proc-stat (pid)
;;   (with-standard-io-syntax
;;   (ignore-errors
;;     (with-open-file
;;       (s (format nil "/proc/~a/stat" pid))
;;       (loop for key in *gnu-linux-proc-stat-fields* do
;;             (let ((x (read s)))
;;               (unless (member (car key)
;;                               '(nswap zero cnswap rlim kstkesp kstkeip
;;                                       startstack wchan policy
;;                                       rt_policy))
;;                 (format *standard-output*
;;                         "~%~a~12t~15:d~30t~a"
;;                         (car key)
;;                         x
;;                         (cadr key)))))))))

;; (defn proc-stat (pid)
;;   (with-standard-io-syntax
;;    (ignore-errors
;;      (with-open-file
;;        (s (format nil "/proc/~a/stat" pid))
;;        (loop for key in *gnu-linux-proc-stat-fields*
;;              nconc (list (car key) (read s)))))))


;; ; We use DEFVAR for *UNSMASHED-IF* and *UNSMASHED-OR* so we don't set
;; ; them; that could accidentally pick up the wrong value if this file
;; ; were loaded twice.

;; (defvar *unsmashed-if* (compiler-macro-function 'if))

;; (defvar *unsmashed-or* (compiler-macro-function 'or))

;; (defg *smashed-if* nil)

;; (defg *smashed-or* nil)


;; #+Clozure
;; (defg *current-compiler-function* 'unknown)

;; (defg *print-pprint-dispatch-orig* *print-pprint-dispatch*)

;; #+Clozure
;; (defun rwx-size (&optional verbose)

;;   "(RWX-SIZE) returns two numbers: (a) the number of bytes that are in
;;   use by the current CCL process, according to Gary Byers, as detailed
;;   below, and (b) the number of bytes that are not in use by the
;;   current Lisp process, but that have been merely imagined in secret
;;   correspondence between CCL and Gnu-Linux.  Do not worry about (b).

;;   If the optional argument, VERBOSE, is T, then information about
;;   memory chunks that both contribute to (a) and that exceed
;;   1 million bytes are printed to *debug-io*."

;; ;; From an email sent by Gary Byers:

;; ;; If you want a meaningful and accurate answer to the question of how
;; ;; much memory the process is using, I don't know of a more accurate
;; ;; or meaningful answer than what you'd get if you looked at each line
;; ;; in the pseudofile

;; ;; /proc/<pid>/maps

;; ;; on Linux (where <pid> is the process ID of the process) and totaled
;; ;; the sizes of each region that was readable, writable, or
;; ;; executable.  The regions are described by lines that look something
;; ;; like:

;; ;; 300040eef000-300042f60000 rwxp 300040eef000 00:00 0
;; ;; 300042f60000-307c00000000 ---p 300042f60000 00:00 0

;; ;; The first of these lines describes a region that's readable (r),
;; ;; writable (w), and executable (x); the second line descibes a much
;; ;; larger region that has none of these attributes.  The first region
;; ;; costs something: we have to have some physical memory in order to
;; ;; read/write/execute the contents of those pages (and if we're low on
;; ;; physical memory the OS might move those contents to swap space, and
;; ;; if this happens a lot we'll see delays like those that you
;; ;; describe.)  It's sometimes said that the first region is
;; ;; "committed" memory (the OS has to commit some real resources in
;; ;; order for you to be able to read and write to it) and the second
;; ;; region isn't committed.

;; ; The following code by Boyer is not to be blamed on Byers.

;;   (let ((fn (format nil "/proc/~a/maps" (ccl::getpid)))
;;         (count '?)
;;         potential
;;         int1 int2 pos1 pos2 next)
;;     (with-standard-io-syntax
;;      (when (ignore-errors (probe-file fn))
;;        (setq count 0)
;;        (setq potential 0)
;;        (with-open-file (s fn)
;;          (loop while (setq next (read-line s nil nil)) do
;;                (multiple-value-setq (int1 pos1)
;;                  (parse-integer next :radix 16 :junk-allowed t))
;;                (multiple-value-setq (int2 pos2)
;;                  (parse-integer next :start (1+ pos1)
;;                                 :radix 16 :junk-allowed t))
;;                (let ((add (- int2 int1)))
;;                  (cond ((loop for i from (+ pos2 1) to (+ pos2 3)
;;                               thereis
;;                               (member (char next i) '(#\r #\w #\x)))
;;                         (incf count add)
;;                         (when verbose
;;                           (format *debug-io*
;;                                   "~&~a~%adds ~:d"
;;                                   next (- int2 int1))))
;;                        (t (incf potential add))))))))
;;     (when verbose (format *debug-io* "~%(rwx-size)=~:d" count))
;;     (values count potential)))

