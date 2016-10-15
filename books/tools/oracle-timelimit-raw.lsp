; Oracle Timing
; Copyright (C) 2015 Kestrel Institute (http://www.kestrel.edu)
;
; License: (An MIT license):
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
; Original authors: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

(declaim (optimize (safety 3) (speed 0) (space 1)))

(defun fudge-heap-bytes-allocated ()
  ;; BOZO copied and pasted in oracle-time-raw.lsp
  #+(or ccl sbcl)
  (heap-bytes-allocated)
  #-(or ccl sbcl) ;; BOZO why doesn't ACL2 do it this way?
  0)

(defvar *oracle-timelimit-debug*
  ;; Change this to T to enable copious debugging messages
  nil)

(defvar *oracle-timelimit-stack*
  ;; Holds frames of the form
  ;;    (successp elapsed-time total-alloc)
  nil)

(defmacro oracle-timelimit-debug (&rest args)
  `(and *oracle-timelimit-debug* (format t . ,args)))


(defun current-global-allocation ()
  ;; Similar to heap-bytes-allocated, but not specific to the current thread
  #-Clozure
  0
  #+Clozure
  (multiple-value-bind
   (dynamic-used static-used library-used frozen-space-size)
   (ccl::%usedbytes)
   (+ dynamic-used static-used library-used frozen-space-size)))

(defmacro oracle-timelimit-exec-raw (extra-args form)
  (let* ((main-thread          (gensym))
         (lock                 (gensym))
         (main-thread-state    (gensym))
         (timeout-thread       (gensym))
         (start-time           (gensym))
         (start-alloc          (gensym))
         (end-time             (gensym))
         (end-alloc            (gensym))
         (ans                  (gensym))
         (limit                (gensym))
         (num-returns          (gensym))
         (maxmem               (gensym))
         (suppress-lisp-errors (gensym))
         (extra-args-eval      (gensym))
         (suppressed-error     (gensym)))
    ;; (format t "Main-thread: ~s~%" main-thread)
    ;; (format t "lock: ~s~%" lock)
    ;; (format t "main-thread-state: ~s~%" main-thread-state)
    ;; (format t "timeout-thread: ~s~%" timeout-thread)
    ;; (format t "start-time: ~s~%" start-time)
    ;; (format t "start-alloc: ~s~%" start-alloc)
    ;; (format t "end-time: ~s~%" end-time)
    ;; (format t "end-alloc: ~s~%" end-alloc)
    ;; (format t "ans: ~s~%" ans)
    ;; (format t "limit: ~s~%" limit)
    ;; (format t "num-returns: ~s~%" num-returns)
    ;; (format t "lafv-eval: ~s~%" lafv-eval)
    `(let* ((,extra-args-eval ,extra-args)
            (,limit                (first  ,extra-args-eval))
            (,num-returns          (second ,extra-args-eval))
            (,maxmem               (third  ,extra-args-eval))
            (,suppress-lisp-errors (fourth ,extra-args-eval))
            ;; We want the computation to run in the main thread to ensure that
            ;; any special variables (e.g., the hons space, stobjs, etc.)  are
            ;; all still bound to their current values.
            (,main-thread (bt:current-thread))
            (,timeout-thread nil)
            (timeout-tag (gensym))
            ;; We explicitly keep track of the main thread's state so that the
            ;; timeout thread knows when to exit.  Any updates/accesses to this
            ;; state should be protected by LOCK.  The only possible transitions
            ;; are:
            ;;    Starting -> Being Killed
            ;;    Starting -> Finished On Time
            ;;    Starting -> Execution Error
            ;; And only one such transition will be made!
            (,lock              (bt:make-lock))
            (,main-thread-state :starting)
            (,ans nil)
            (,suppressed-error nil)
            (,start-alloc (fudge-heap-bytes-allocated))
            (,start-time  (get-internal-real-time)))

       (oracle-timelimit-debug "OTL: Running ~s:~%" ',form)
       (oracle-timelimit-debug "OTL: Limit: ~s~%" ,limit)
       (oracle-timelimit-debug "OTL: Num returns: ~s~%" ,num-returns)

       ;; In case of a timeout, the timeout will interrupt the main thread and
       ;; cause it to throw to ,timeout-tag.  Our use of a gensym here should
       ;; ensure that any exits other than a timeout (e.g., a raw Lisp error or
       ;; similar) are NOT misinterpreted as timeouts.
       (catch timeout-tag

         ;; ** Launch the timeout thread in the background.
         (setq ,timeout-thread
               (bt:make-thread
                (lambda ()
                  ;; The timeout thread should basically just sleep for ,limit
                  ;; seconds and then interrupt the main thread.  Well, that's
                  ;; not quite good enough.  Say we run a fast computation with
                  ;; a generous time limit.  We don't want the timeout thread
                  ;; sitting around in the background wasting resources for
                  ;; thousands of seconds after the computation is already
                  ;; done.  I originally tried wrapping the whole timeout
                  ;; thread in a catch, and having the main thread interrupt
                  ;; it.  But it seemed really error prone to have both threads
                  ;; trying to interrupt each other.  So now, instead, I just
                  ;; make the timeout thread check, once a second, whether the
                  ;; main thread has finished.  This way the timeout thread
                  ;; should never stay around for more than a second after the
                  ;; main computation has exited.  This also works well for
                  ;; imposing a memory ceiling.
                  (loop do
                        (oracle-timelimit-debug
                         "OTL: Timeout thread: waiting ~s more secs~%" ,limit)
                        (when (< ,limit 1)
                          (sleep ,limit)
                          (loop-finish))
                        (when (and ,maxmem
                                   (let* ((current-alloc (current-global-allocation)))
                                     (oracle-timelimit-debug
                                      "OTL timeout thread: maxmem ~s, current ~s~%"
                                      ,maxmem current-alloc)
                                     (> current-alloc ,maxmem)))
                          (oracle-timelimit-debug
                           "OTL: Timeout thread: memory ceiling exceeded~%")
                          (loop-finish))
                        (sleep 1)
                        (decf ,limit 1)
                        (bt:with-lock-held (,lock)
                           (oracle-timelimit-debug
                            "OTL: Timeout thread: main thread is ~s~%" ,main-thread-state)
                           (unless (eq ,main-thread-state :starting)
                             (loop-finish))))

                  ;; All done waiting, so see whether we need to interrupt the
                  ;; main thread now.
                  (bt:with-lock-held (,lock)
                     (oracle-timelimit-debug
                      "OTL: Timeout thread: done waiting, main thread is ~s~%" ,main-thread-state)
                     (when (eq ,main-thread-state :starting)
                       (oracle-timelimit-debug
                        "OTL: Timeout thread: killing main thread.~%")
                       (setq ,main-thread-state :being-killed)
                       (bordeaux-threads:interrupt-thread
                        ,main-thread
                        (lambda () (throw timeout-tag nil)))))

                  (oracle-timelimit-debug
                   "OTL: Timeout thread: exiting.~%"))))

         ;; ** In parallel: (2) do the computation.
         (oracle-timelimit-debug "OTL: Running the form.~%")
         (unwind-protect

             (handler-case
               (progn

                 ;; Main execution step.
                 ,(if suppress-lisp-errors
                      ;; Ugh.  ACL2 signals hard errors by throwing to
                      ;; 'raw-ev-fncall instead of calling error.  The
                      ;; handler-case form won't catch these.  Instead, we have
                      ;; to catch them explicitly.
                      ;;
                      ;; BOZO it'd be nice to be able to print the error that
                      ;; we are suppressing.  However, even when I try to bind
                      ;; *error-output* here to (make-string-output-stream), it
                      ;; still just prints it to the terminal instead.  Looking
                      ;; at ACL2's code for printing errors, I'm not sure why
                      ;; this doesn't work.  At any rate, it doesn't work, so
                      ;; I guess for now we'll just let ACL2 print the error and
                      ;; then say that we've suppressed an error.
                      `(unless (eq :did-not-catch-acl2-error
                                   (catch 'raw-ev-fncall
                                     (setq ,ans (multiple-value-list ,form))
                                     :did-not-catch-acl2-error))
                         (error "ACL2 Error"))
                    ;; Not suppressing lisp errors, so just try to evaluate the form.
                    `(setq ,ans (multiple-value-list ,form)))

                 (bt:with-lock-held (,lock)
                                    (oracle-timelimit-debug
                                     "OTL: Finished running the form, status is ~s~%" ,main-thread-state)
                                    (when (eq ,main-thread-state :starting)
                                      ;; The timeout thread doesn't want to kill us yet.  Mark
                                      ;; that we've finished on time so that it won't try to kill
                                      ;; us.  It will notice that we've finished and exit itself.
                                      (oracle-timelimit-debug
                                       "OTL: Marking successful finish.~%")
                                      (setq ,main-thread-state :finished-on-time))))
               ,@(and suppress-lisp-errors
                      `((error (condition)
                               (progn
                                 (format t "oracle-timelimit: suppressing error ~a~%" condition)
                                 (setq ,suppressed-error t)))
                        (storage-condition (condition)
                                           (progn
                                             (format t "oracle-timelimit: suppressing error ~a~%" condition)
                                             (setq ,suppressed-error t))))))

           ;; In case of any exit, whether we are suppressing errors or not, we
           ;; want to make sure that the timeout thread doesn't try to
           ;; interrupt us!
           (progn
             (oracle-timelimit-debug
              "OTL: Protect: Main computation done, state is ~s~%" ,main-thread-state)
             (bt:with-lock-held (,lock)
                                (when (eq ,main-thread-state :starting)
                                  (oracle-timelimit-debug
                                   "OTL: Protect: Marking computation as error.~%")
                                  (setq ,main-thread-state :raw-lisp-error)))))

         (oracle-timelimit-debug
          "OTL: Done with main computation, state ~s~%" ,main-thread-state)

         (when (eq ,main-thread-state :being-killed)
           ;; Special race condition happened: we timeout thread woke up just
           ;; as we finished and it decided to kill us.  The interrupt is
           ;; coming and there's nothing we can do to stop it.  We need to make
           ;; sure we don't exit the catch until it's done!
           (loop do
                 (oracle-timelimit-debug
                  "OTL: Waiting for death.~%")
                 (sleep 1))))

       (oracle-timelimit-debug " -- End of catch --~%")

       (let ((,end-time    (get-internal-real-time))
             (,end-alloc   (fudge-heap-bytes-allocated)))
         (oracle-timelimit-debug "OTL: Start time ~s, end time ~s~%" ,start-time ,end-time)
         (oracle-timelimit-debug "OTL: Start alloc ~s, end alloc ~s~%" ,start-alloc ,end-alloc)
         (oracle-timelimit-debug "OTL: Successful ontime finish? ~s~%"
                                 (eq ,main-thread-state :finished-on-time))

         ;; Record whether we succeeded and how long it took, etc., so that we
         ;; can extract this information later.
         (push (list (eq ,main-thread-state :finished-on-time)
                     (/ (coerce (- ,end-time ,start-time) 'rational)
                        internal-time-units-per-second)
                     (- ,end-alloc ,start-alloc))
               *oracle-timelimit-stack*)

         (cond ((eq ,main-thread-state :finished-on-time)
                ;; Return the answer from the computation
                (values-list ,ans))
               ;; Otherwise, we ran out of time or suppressed an error.  We We
               ;; don't actually need to produce the failure values, just
               ;; repeat NIL however many times, to get the arity right.
               ((eql ,num-returns 1)
                (oracle-timelimit-debug "Only 1 return value so just returning NIL.~%")
                nil)
               (t
                (oracle-timelimit-debug "Returning ~x0 NIL values.~%" ,num-returns)
                (values-list (make-list ,num-returns))))))))


(defun oracle-timelimit-extract (state)
  (unless (live-state-p state)
    (er hard? 'oracle-timelimit "A live state is required!"))

  (unless (consp *oracle-timelimit-stack*)
    (er hard? 'oracle-timelimit
        "Trying to extract timing info, but the *oracle-timelimit-stack* is empty! ~
         Jared thinks this should never happen."))

  (let ((val (pop *oracle-timelimit-stack*)))

    (unless (and (true-listp val)
                 (equal (len val) 3)
                 (booleanp (first val))
                 (and (rationalp (second val))
                      (<= 0 (second val)))
                 (natp (third val)))
      (er hard? 'oracle-timelimit
          "*oracle-timelimit-stack* had corrupt value ~x0.  Jared thinks this ~
           should never happen." val))

    (mv (first val) (second val) (third val) state)))



