
;; BOZO copyright stuff.

; h-watch.lisp
;
; This is WATCH stuff that Jared pulled out of memoize-raw.lisp.  I don't
; really know how WATCH is supposed to work, or if it works at all.

(in-package "ACL2")


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



(defn print-ancestry (&optional (p (ccl::getpid)))
  (with-open-stream
   (s (csh :stream "ps ww -A -o pid,ppid,cmd"))
   (let (first l ans trip)
     (loop (setq first (read s nil nil))
           (when (null first) (return nil))
           (push (list first (read s nil nil) (read-line s nil nil))
                 l))
     (loop (setq trip (assoc p l))
           (when (null trip) (return nil))
           (push (caddr trip) ans)
           (setq p (cadr trip)))
     (setq ans (nreverse ans))
     (loop for i from 0 while ans do
           (terpri)
           (loop repeat i do (write-char #\Space))
           (princ (pop ans))))))

(defn print-fds (&optional (p (ccl::getpid)))
  (loop for x in (directory (ofn "/proc/~a/fd/*" p))
        do
        (let ((n (namestring x)))
          (unless (or (eql #\/ (char n (1- (length n))))
                      (looking-at "/dev/pts/" n)
                      (looking-at "/scratch/" n)
                      (looking-at "/proc/" n))
            (fresh-line)
            (princ n)))))

(defg *watch-forms*
  '("\"A string or a quoted form in *WATCH-FORMS* is ignored.\""
    (print-call-stack)
    #+Clozure '(bytes-used)
    (memoize-summary)
    (time-since-watch-start)
    (time-of-last-watch-update)
    '(mapc 'print-some-documentation *watch-items*)
    '(hons-acons-summary)
    '(pons-summary)
    '(hons-summary)
    '(print-fds)
    '(print-ancestry)
    #+Clozure '(watch-shell-command "pwd")
    '(functions-that-may-be-too-fast-to-sensibly-profile)
    '(physical-memory-on-this-machine)
    #+Clozure '(number-of-cpus-on-this-machine)
    #+Clozure (gc-count)
    )

  "The forms in *WATCH-FORMS* are evaluated periodically and the
  output is written to *WATCH-FILE*.  Change *WATCH-FORMS*
  to produce whatever watch output you want.")

(defg *watch-items*
  '(
    *memoize-summary-limit*
    *memoize-summary-order-list*
    *memoize-summary-order-reversed*
    *max-mem-usage*

    *watch-forms*
    *watch-file*
    *watch-items*

    *memoize-summary-order-list*
    *memoize-summary-order-reversed*
    *memoize-summary-limit*

    *record-bytes*
    *record-calls*
    *record-hits*
    *record-mht-calls*
    *record-time*

    *report-bytes*
    *report-calls*
    *report-calls-from*
    *report-calls-to*
    *report-hits*
    *report-mht-calls*
    *report-time*
    *report-on-memo-tables*
    *report-on-pons-tables*

    #+Clozure (ccl::lisp-heap-gc-threshold)
    #+Clozure (ccl::%freebytes)

    )
  "*WATCH-ITEMS* is a list of forms that are printed with their values
  and documentation if (MAPC 'PRINT-SOME-DOCUMENTATION *WATCH-ITEMS*)
  is a member of *WATCH-FORMS* and (WATCH-DO) is invoked.")

(defg *watch-last-real-time*  0)
(defg *watch-last-run-time*   0)
(defg *watch-start-real-time* 0)
(defg *watch-start-run-time*  0)
(defg *watch-start-gc-count*  0)
(defg *watch-start-gc-time*   0)

(defg *watch-start-heap-bytes-allocated* 0)

(declaim (mfixnum *watch-last-real-time* *watch-last-run-time*
                  *watch-start-real-time* *watch-start-run-time*
                  *watch-start-gc-count* *watch-start-gc-time*))

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

(defmacro ofto (&rest r) ; For writing to *terminal-io*
  ;; only used in watch-condition
  `(progn (format *terminal-io* ,@r)
          (force-output *terminal-io*)))

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
            (format t "~%; WITH-WATCH-LOCK: ** Only the ~
                       *WATCH-STARTUP-PROCESS* may obtain the watch lock."))
           ((not (eql 0 ccl::*break-level*))
            (format t "~%; WITH-WATCH-LOCK: ** (eql 0 ccl::*break-level*)."))
           ((not *watch-file*)
            (format t "~%; *WATCH-FILE* is NIL.  Invoke (watch)."))
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
                          (t (format t "~%; WITH-WATCH-LOCK: ** the watch ~
                                        lock is currently taken."))))
                (remhash id *watch-lock-ht*))

; The watch lock is released as of now, if it was obtained.

              ))
           (t (format t "~%; WITH-WATCH-LOCK: ** the watch lock is currently ~
                         taken.")))
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
             (format t "~&; real-time-out when evaluating:~%~s." ',form)
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
             (format t "~&; run-time-out when evaluating:~%~s." ',form)
             (setq *with-run-timer-raw-limit* old)
             ',time-out-value)
            (t (error c)))))))

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
                   (format t "~&~s~50t? error in eval ?~%" form)))
           (fresh-line)))
   (with-open-file (stream *watch-file* :direction :output
                           :if-exists :supersede)
     (write-string *watch-string* stream))
   (setq *watch-last-real-time* (get-internal-real-time))
   (setq *watch-last-run-time* (get-internal-run-time)))
  *watch-file*)

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
           (format t "~%; MAYBE-WATCH-DUMP: An error is being ignored:~% ~a."
                   x)
           (incf-watch-count)))
         (incf-watch-count)
         *watch-file*)
        (t (incf-watch-count)
           (format t "~%; MAYBE-WATCH-DUMP may only be called by the ~
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

  #+Clozure
  (ccl::cpu-count)
  (watch-kill)
  #+Clozure
  (pushnew 'watch-kill ccl::*save-exit-functions*)
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
    (error "; WATCH: evaluation of *WATCH-FILE-FORM* failed to ~
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
  (watch-dump))




(defn1 first-string (l)
  (loop for x in l when (stringp x) do (return x)))

(defn1 print-some-documentation (x)
  (let ((state *the-live-state*)
        (types-of-documentation
         '(compiler-macro function
                          method-combination
                          setf structure type variable
                          t)))

; 0. Print it, evaluate it, and print the value, if possible.

    (format t "~&~%~a" x)
    (let* ((avrc (cons nil nil))
           (value avrc))
      (cond ((symbolp x)
             (cond ((boundp x)
                    (setq value (symbol-value x)))
                   ((fboundp x) nil)
                   (t (setq value "unbound"))))
            (t (setq value "error-in-evaluation")
               (ignore-errors
                 (setq value
                   (multiple-value-list (eval x))))))
      (cond ((not (eq value avrc))
             (when (and (consp value) (null (cdr value)))
               (setq value (car value)))
             (let ((str (format nil "~a" value)))
               (cond ((numberp value) (format t " => ~:d." value))
                     ((> (length str) 40)
                      (format t " =>~%~a." str))
                     (t (format t " => ~a." str)))))
            (t (format t "."))))
    (cond
     ((not (symbolp x)) nil)
     ((get-doc-string x state)

; 1. For a symbol with regular ACL2 documentation, use :doc!.

      (format t "~%:doc! ")
      (let ((*acl2-unwind-protect-stack*
             (cons nil *acl2-unwind-protect-stack*)))
        (doc!-fn x state)))
     (t (let* ((tem nil)
               (found nil)
               (w (w state))
               (def (first-string (cltl-def-from-name x nil w))))
          (cond
           (def

; 2. Else, for an ACL2 function symbol with a DOC string, print it.

            (format t "~%(first-string (cltl-def-from-name '~a nil (w ~
                   *the-live-state*))) =>~%~a"
                 x def))
           (t

; 3. Else, for a symbol with some Common Lisp DOCUMENTATION, print
; that.

            (loop for type in types-of-documentation
                  when (setq tem (documentation x type)) do
                  (format t "~%(documentation '~a '~a) => ~% ~a"
                       type x tem)
                  (setq found t))
            (loop for type-pair in '((function saved-function)
                                     (variable saved-variable))
                  when (and (null (documentation x (car type-pair)))
                            (setq tem (documentation
                                       x
                                       (cadr type-pair))))
                  do
                  (format t "~%(documentation '~a '~a) => ~% ~a"
                       (cadr type-pair) x tem)
                  (setq found t))
            (cond ((null found)

; 4. Else, call DESCRIBE.

                   (format t "~%(describe '~a) =>~%" x)
                   (describe x))))))))))

(defmacro print-documentation (&rest r)

  "(PRINT-DOCUMENTATION x) prints out some things about the symbols in
  r, such as values and documentation."

  `(progn
     (format t "~%For further information about these ~a items, see below.~%"
             (length ',r))
     (loop for x in ',r as i from 1 do
           (format t "~% ~3d.~4t~a" i x))
     (terpri)
     (terpri)
     (mapc 'print-some-documentation ',r)
     (values)))

(defn1 watch-help ()

  "(WATCH-HELP) prints some documentation for WATCH, MEMOIZE, PROFILE,
  etc."

  (print-documentation
   watch
   watch-dump
   #+Clozure maybe-watch-dump
   watch-kill

   memoize-summary
   memoized-values
   *memoize-summary-order-list*
   *memoize-summary-limit*
   *memoize-summary-order-reversed*
   hons-acons-summary
   if-report

   bytes-allocated
   hons-statistics
   hons-summary
   number-of-memoized-entries
   number-of-mht-calls
   print-call-stack

   clear-memoize-call-array
   clear-memoize-tables
   clear-memoize-table

   profile
   profile-acl2
   profile-all
   profile-file

   memoize
   memoize-fn

   pons-summary
   print-call-stack

   unmemoize
   unmemoize-all
   unmemoize-profiled

   print-documentation
   compact-print-file
   compact-read-file

   *watch-items*
   *watch-forms*
   *watch-file-form*
   *watch-string*
   *watch-file*
   *watch-startup-process*
   *watch-last-real-time*
   *watch-last-run-time*
   *watch-real-seconds-between-dumps*
   *watch-lock-ht*

   #+Clozure
   *watch-dog-process*
   #+Clozure
   watch-kill

   bytes-allocated
   bytes-allocated/call
   event-number
   hits/calls
   number-of-calls
   number-of-hits
   number-of-memoized-entries
   number-of-mht-calls
   time-for-non-hits/call
   time/call
   total-time

   resize-memo
   resize-pons

   ))





;  USER MALEABLE WATCH FUNCTIONS AND VARIABLES

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
      (format t

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


(defmacro defw (fn &rest r)
  `(defn ,fn ()
     (let ((fn (string-capitalize (symbol-name ',fn))))
       ,@r)))

(defmacro oft-wrm (str &rest r)
  `(format t ,str (or *print-right-margin* 70) ,@r))

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

(defun functions-that-may-be-too-fast-to-sensibly-profile ()
  (let ((ans (loop for fn in (profiled-functions)
                   when (< (total-time fn)
                           (* 1e-6 (number-of-calls fn)))
                   collect fn)))
    (when ans (format t "Too fast to sensibly profile?~%~a" ans))))

#+Clozure
(defw number-of-cpus-on-this-machine
  (let* ((ans (ofn "~:d" (ccl::cpu-count))))
    (oft-wrm "~v<~a~;~a~>" fn ans)))

(defw physical-memory-on-this-machine
  (let* ((ans (ofn "~:d" (physical-memory))))
    (oft-wrm "~v<~a~;~a bytes.~>" fn ans)))

#+Clozure
(defun watch-shell-command (&rest args)
  (let* ((as (args-spaced args))
         (output (csh as)))
    (oft-wrm "~v<~a~;~a~>" as output)))

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
(defun call-with-timeout (function duration)

  "(CALL-WITH-TIMEOUT function duration) calls FUNCTION on no
  arguments and returns its values unless more than DURATION seconds
  elapses before completion, in which case the FUNCTION computation is
  interrupted and calls ERROR.

  Thanks to Gary Byers for this beaut."

   (let* ((semaphore (make-watchdog duration)))
      (unwind-protect
          (funcall function)
        (ccl:signal-semaphore semaphore))))

