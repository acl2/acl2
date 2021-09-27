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

; This file is divided into the following sections.

; Section:  Single-threaded Futures
; Section:  Multi-threaded Futures
; Section:  Futures Interface

(in-package "ACL2")

; Essay on Futures

; This futures library provides three primitives for creating, reading, and
; aborting futures.  We then use the futures library to implement
; spec-mv-let.  Building spec-mv-let upon the futures library makes it more
; easily maintained than if it were built directly upon the low-level
; multi-threading interface.

; Parallelism wart: add to the above "Essay on Futures", with the intent that
; the essay should act as a guide to this file.

; Parallelism wart: clean up this file by removing blank lines that are
; inconsistent with the ACL2 style guide and making other improvements as
; appropriate (e.g., clean up comments about pending work).

;---------------------------------------------------------------------
; Section:  Single-threaded Futures

(defstruct st-future

; Unlike mt-future objects, st-future objects execute lazily, i.e., only when
; reading them.

  (value nil)
  (valid nil) ; whether the value is valid
  (closure nil)
  (aborted nil))

(defmacro st-future (x)

; Speculatively creating a single-threaded future will not cause the future's
; value to be computed.  Only reading the future causes such evaluation.

  `(let ((st-future (make-st-future)))
     (setf (st-future-closure st-future) (lambda () ,x))
     (setf (st-future-valid st-future) nil) ; set to T once the value is known
     st-future))

(defun st-future-read (st-future)

; Speculatively reading from a single-threaded future will consume unnecessary
; CPU cycles (and could even lead to infinite recursion), so make sure all
; reading is necessary.

  (assert (st-future-p st-future))
  (if (st-future-valid st-future)
      (values-list (st-future-value st-future))
    (progn (setf (st-future-value st-future)
                 (multiple-value-list (funcall (st-future-closure st-future))))
           (setf (st-future-valid st-future) t)
           (values-list (st-future-value st-future)))))

(defun st-future-abort (st-future)

; We could do nothing in this function and it would be fine.  However, we mark
; it as aborted for book keeping and clear the closure for [earlier] garbage
; collection.

  (assert (st-future-p st-future))
  (setf (st-future-aborted st-future) t)
  (setf (st-future-closure st-future) nil)
  st-future)

;---------------------------------------------------------------------
; Section:  Multi-threaded Futures

; Parallelism wart: discuss these notes with Matt.

; Notes on the implementation of adding, removing, and aborting the evaluation
; of closures:

; (1) Producer is responsible for *always* placing the closure on the queue.
;
; (2) Consumer is responsible for *always* removing the closure from the queue,
; regardless of whether there was early termination.  Upon early termination,
; it is optional as to whether the early terminated future's barrier is
; signaled.  (See defstruct barrier below for information about barriers.)  For
; now, the barrier should not be signaled.
;
; (3) Only the producer of a particular future should abort that future.  (The
; use of futures by spec-mv-let observes this protocol.  Perhaps we should
; consider storing the thread in the future so that an eq test can be used to
; enforce this discipline.)  The producer does so by first setting the abort
; flag of the future and then throwing any consumer that could be evaluating
; that future.
;
; (4) When a consumer evaluates a future, it first sets a pointer to itself in
; thread array and secondly checks the future's abort flag.
;
; (5) The combination of (3) and (4) results in the following six potential
; race conditions/scenarios.  The first column contains things the producer can
; do, and the second column contains things the consumer might do.
;
;  (A) - 12AB
;
;  Producer sets the abort flag
;  Producer looks for a thread to throw, continues
;                      Consumer sets the thread
;                      Consumer checks abort flag, aborts
;  WIN
;
;
;  (B) 1A2[B]
;
;  Producer sets the abort flag
;                      Consumer sets the thread
;  Producer looks for a thread to throw, throws
;
;  NON-TRIVIAL to implement, need to check
;
;
;  (C) 1AB[2]
;
;  Producer sets the abort flag
;                      Consumer sets the thread
;                      Consumer checks abort flag, aborts
;  SUBSUMED by A
;
;
;  (D) A12[B]
;
;                      Consumer sets the thread
;  Producer sets the abort flag
;  Producer looks for a thread to throw, throws
;
;  NON-TRIVIAL to implement, need to check
;
;
;  (E) A1B[2]
;
;                      Consumer sets the thread
;  Producer sets the abort flag
;                      Consumer checks abort flag, aborts
;  WIN
;
;
;  (F) AB12
;                      Consumer sets the thread
;                      Consumer checks abort flag, continues
;  Producer sets the abort flag
;  Producer looks for a thread to throw, throws
;
;  WIN
;
;
;  LEGEND
;  1 = Producer sets the abort flag
;  2 = Producer looks for a thread to throw, continues/throws
;  A = Consumer sets the thread
;  B = Consumer checks abort flag, continues/aborts
;
;  RULES
;  1 comes before 2
;  A comes before B
;
;
; (6) With the current design, it is assumed that only one thread will be
; issuing early termination orders -- the thread that generated the future
; stored at the given index.  It's possible to change the design, but it would
; require more locking and be slower.

; We currently use a feature to control whether resources are tested for
; availability at the level of futures.  Since this feature only controls
; futures, it only impacts the implementation underlying spec-mv-let.  Thus,
; plet, pargs, pand, and por are unaffected.

(push :skip-resource-availability-test *features*)

(defstruct atomic-notification
  (value nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Closure evaluators
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Parallelism wart: probably delete the following two paragraphs.

; We continue our array-based approach for storing and grabbing pieces of
; parallelism work.  This time, however, we do things a little differently.
; Instead of saving "pieces of parallelism work" to a queue, we only store
; closures.  I'm not sure how this will pan out WRT early termination.  I might
; end up making it more than just closures.

; There are some optimizations we can make if we assume that only one thread
; will be reading the future's value.  E.g., we can remove the wait-count from
; barrier, because there will always be only one thread waiting.

(defstruct barrier

; Our version of a barrier is a hybrid between a semaphore and a condition
; variable.  What we need is something that once it's signaled once, any thread
; that waits on it will be allowed to proceed.

; Point of clarification that is a little distracting: Our notion of barrier is
; different from the traditional definition of a "multi-threaded programming
; barrier" in the following way: in the traditional definition, a barrier is a
; spot in the program's execution that _n_ threads will eventually reach.  Once
; a thread reaches the barrier, it blocks (waits) until _n_ threads have
; reached the barrier.  Once all of the _n_ threads have reached the barrier,
; they are all given the green light to proceed.  Our notion of a barrier is
; different from this, in that there is no "global wait by _n_ threads".  In
; our notion of a barrier, any number of threads can wait on the barrier.  Each
; of these threads will block until the barrier is signaled.  Once the barrier
; is signaled, all of the blocked threads are allowed to proceed, and any
; thread that waits upon the barrier in the future is also allowed to
; immediately proceed.

  (value nil)
  (lock (make-lock))
  (wait-count 0)
  (sem (make-semaphore)))

(defun broadcast-barrier (barrier)

; Update the barrier as "clear to proceed" and notify all threads waiting for
; such clearance.

  (without-interrupts ; we can be stuck in a non-interruptible deadlock
   (setf (barrier-value barrier) t)
   (with-lock (barrier-lock barrier)
              (let ((count (barrier-wait-count barrier)))
                (loop for i from 0 to count do
                      (signal-semaphore (barrier-sem barrier))
                      (decf (barrier-wait-count barrier)))))))

(defun wait-on-barrier (barrier)
  (if (barrier-value barrier)
      t
    (progn
      (with-lock (barrier-lock barrier)
                 (incf (barrier-wait-count barrier)))
; There has to be another test after holding the lock.
      (when (not (barrier-value barrier))
        (wait-on-semaphore (barrier-sem barrier))))))

(defstruct mt-future

; Unlike st-future objects, mt-future objects execute eagerly.

  (index nil)
  (value nil)
  (valid (make-barrier)) ; initially contains a nil valid bit for the barrier
  (closure nil)
  (aborted nil)
  (thrown-tag nil))

(define-atomically-modifiable-counter *last-slot-saved* 0)
(define-atomically-modifiable-counter *last-slot-taken* 0)

; The three arrays defined below all have the same length, *future-array-size*.
; They correspond as follows: for a future F stored in the ith element of
; *future-array*, the ith element of *thread-array* is the thread executing F,
; and the ith element of *future-dependencies* is a list of all indices (in
; *future-array*) of futures created by F.

; Perhaps we should be concerned that the array elements will be so close
; together, that they'll be in the same cache lines, and the CPU cores will get
; bogged down just keeping the writes to the cache "current".  The exact impact
; on performance of this thrashing is unknown.  (However, correctness is not an
; issue, since semantically caches are just an optimization, as enforced by
; cache coherency schemes.)  Followup: After further thought, David Rager
; believes that this thrashing will be negligible when compared to the rest of
; the parallelism overhead.

(defvar *future-array*)
(defvar *thread-array*)
(defvar *future-dependencies*)

(defparameter *future-queue-length-history*

; supports dmr as modified for ACL2(p)

  nil)

(defvar *current-thread-index*

; For this variable, we take advantage of the fact that special variables are
; thread-local.  Here we set it to 0 for the main thread.

  0)

(defconstant *starting-core* 'start)
(defconstant *resumptive-core* 'resumptive)

(defvar *allocated-core*

; The value of this variable is always *starting-core*, *resumptive-core*, or
; nil.

; We now document a rather strange behavior that resulted in a bug in the
; parallelism system for a good while.  This strange behavior justifies giving
; *allocated-core* an initial value of *resumptive-core* instead of
; *starting-core*.  To understand why, suppose we instead gave *allocated-core*
; the initial value of *starting-core*.  Then, when the main thread encountered
; its first parallelism primitive, it would set *allocated-core* to nil and
; then, when it resumed execution after the parallelized portion was done, it
; would claim a resumptive core, and the main thread would then have
; *resumptive-core* for its value of *allocated-core*.  This would be fine,
; except that we'll never reclaim the original *starting-core* for the main
; thread.  So, rather than worry about this problem, we side-step it entirely
; and start the main thread as a "resumptive" core.

; Parallelism blemish: the above correction may also need to be made for the
; other parallelism implementation that supports plet/pargs/pand/por.

  *resumptive-core*)

(defvar *decremented-idle-future-thread-count* nil)

(defvar *idle-future-core-count*
  (make-atomically-modifiable-counter *core-count*))
(defvar *idle-future-resumptive-core-count*
  (make-atomically-modifiable-counter (1- *core-count*)))
(defvar *idle-core* (make-semaphore))

(define-atomically-modifiable-counter *idle-future-thread-count*

; Parallelism blemish: on April 6, 2012, Rager observed that
; *idle-future-thread-count* and *threads-waiting-for-starting-core* can sync
; up and obtain the same value.  As such, it occurs to Rager that maybe we
; still consider threads that are waiting for a CPU core to be "idle."  This
; labeling might be fine, but it's inconsistent with our heuristic for
; determining whether to spawn a closure consumer (but as we explain below, in
; practice, it does not present a problem).  Investigate when a thread is
; considered to no longer be idle, and revise the heuristic as needed.  Note
; that this investigation isn't absolutely necessary, because we currently
; ensure that the total number of threads that are idle or waiting on a CPU
; core (we call these classifications "available" below) are at least twice the
; number of CPU cores in the system.  Thus, counting the same thread twice
; still results in having a number of available threads that's at least the
; number of CPU cores, which is fine.

  0)

(defvar *future-added* (make-semaphore))

(defvar *idle-resumptive-core* (make-semaphore))

; Debug variable:
(defvar *threads-spawned* 0)

(define-atomically-modifiable-counter *unassigned-and-active-future-count*

; We count the number of futures that are in the unassigned or active
; (including both started and resumed) state.  Thus, we are not including
; futures that are in the pending state.  See also *total-future-count*.

; We treat the initial thread as an active future.

  1)

(define-atomically-modifiable-counter *total-future-count*

; We count the total number of futures, each of which is in the unassigned,
; active (including both started and resumed), or pending state.  See also
; *unassigned-and-active-future-count*, which does not count those in the
; pending state.

; An invariant is that the value of this counter is always less than the value
; of ACL2 state global 'total-parallelism-work-limit.

  0)

(defconstant *future-array-size* 200000)

(defmacro faref (array subscript)
  `(aref ,array
; Avoid reusing slot 0, which is always reserved for the initial thread.
         (if (equal 0 ,subscript)
             0
           (1+ (mod ,subscript (1- *future-array-size*))))))

(defvar *resource-and-timing-based-parallelizations*
  0
  "Tracks the number of times that we parallelize execution when
  waterfall-parallelism is set to :resource-and-timing-based")

(defvar *resource-and-timing-based-serializations*
  0
  "Tracks the number of times that we do not parallelize execution when
  waterfall-parallelism is set to :resource-and-timing-based")

(defvar *resource-based-parallelizations*
  0
  "Tracks the number of times that we parallelize execution when
  waterfall-parallelism is set to :resource-based")

(defvar *resource-based-serializations*
  0
  "Tracks the number of times that we do not parallelize execution when
  waterfall-parallelism is set to :resource-based")

(defun reset-future-queue-length-history ()
  (setf *future-queue-length-history* nil))

(defun reset-future-parallelism-variables ()

; Warning: this function should only be called after calling
; reset-parallelism-variables, which calls
; send-die-to-worker-threads to kill all worker threads.

; This function is not to be confused with reset-parallelism-variables
; (although it is similar in nature).  Both are called by
; reset-all-parallelism-variables.

; Parallelism wart: some relevant variables may be unintentionally omitted from
; this reset.

  (setf *thread-array*
        (make-array *future-array-size* :initial-element nil))
  (setf *future-array*
        (make-array *future-array-size* :initial-element nil))
  (setf *future-dependencies*
        (make-array *future-array-size* :initial-element nil))

  (setf *future-added* (make-semaphore))

  (setf *idle-future-core-count*
        (make-atomically-modifiable-counter *core-count*))

  (setf *idle-future-resumptive-core-count*
        (make-atomically-modifiable-counter (1- *core-count*)))

  (setf *idle-core* (make-semaphore))
  (setf *idle-resumptive-core* (make-semaphore))

  (dotimes (i *core-count*) (signal-semaphore *idle-core*))
  (dotimes (i (1- *core-count*)) (signal-semaphore *idle-resumptive-core*))

; The last slot taken and saved starts at zero, because slot zero is always
; reserved for the initial thread.

  (setf *last-slot-taken* (make-atomically-modifiable-counter 0))
  (setf *last-slot-saved* (make-atomically-modifiable-counter 0))
  (setf *threads-spawned* 0)

  (setf *total-future-count* (make-atomically-modifiable-counter 0))
  (setf *unassigned-and-active-future-count*
        (make-atomically-modifiable-counter 1))

; If we let the threads expire naturally instead of calling the above
; send-die-to-worker-threads, then this setting is unnecessary.
  (setf *idle-future-thread-count* (make-atomically-modifiable-counter 0))
; (setf *pending-future-thread-count* (make-atomically-modifiable-counter 0))
; (setf *resumptive-future-thread-count* (make-atomically-modifiable-counter 0))

; (setf *acl2-par-arrays-lock* (make-lock))

  (setf *resource-and-timing-based-parallelizations* 0)
  (setf *resource-and-timing-based-serializations* 0)

  (setf *resource-based-parallelizations* 0)
  (setf *resource-based-serializations* 0)
;  (setf *aborted-futures-total* 0)

  (reset-future-queue-length-history)

  t ; return t
)

; The following invocation would cause errors in Lispworks.  It probably isn't
; needed for other Lisps either.  But it seems harmless to leave it in, which
; has the advantage of testing reset-future-parallelism-variables during the
; build.
#-lispworks
(reset-future-parallelism-variables)

(defun reset-all-parallelism-variables ()
  (format t "Resetting parallelism and futures variables.  This may take a ~
             few seconds (often either~% 0 or 15).~%")
  (reset-parallelism-variables)
  (reset-future-parallelism-variables)
  (format t "Done resetting parallelism and futures variables.~%"))

(defun futures-parallelism-buffer-has-space-available ()

; This test is used only to implement resource-based parallelism for futures.

  (< (atomically-modifiable-counter-read *unassigned-and-active-future-count*)
     *unassigned-and-active-work-count-limit*))

(defun not-too-many-futures-already-in-existence ()

; See :DOC topic set-total-parallelism-work-limit and :DOC topic
; set-total-parallelism-work-limit-error for more details.

  (let ((total-parallelism-work-limit
         (f-get-global 'total-parallelism-work-limit *the-live-state*)))
    (cond ((equal total-parallelism-work-limit :none)

; If the value is :none, then there is no limit.

           t)
          ((< (atomically-modifiable-counter-read *total-future-count*)
              total-parallelism-work-limit)
           t)
          (t

; We are above the total-parallelism-work-limit.  Now the question is whether we
; notify the user with an error.

           (let ((total-parallelism-work-limit-error
                  (f-get-global 'total-parallelism-work-limit-error
                                *the-live-state*)))
             (cond ((equal total-parallelism-work-limit-error t)

; Cause an error to notify the user that they need to either increase the limit
; or disable the error by setting the global variable
; total-parallelism-work-limit to nil.  This is the default behavior.

                    (er hard 'not-too-many-futures-already-in-existence
                        "The system has encountered the limit placed upon the ~
                         total amount of parallelism work allowed.  Either ~
                         the limit must be increased, or this error must be ~
                         disabled.  See :DOC set-total-parallelism-work-limit ~
                         and :DOC set-total-parallelism-work-limit-error for ~
                         more information."))
                   ((null total-parallelism-work-limit-error)
                    nil)
                   (t (er hard 'not-too-many-futures-already-in-existence
                          "The value for global variable ~
                           total-parallelism-work-limit-error must be one of ~
                           t or nil.  Please change the value of this global ~
                           variable to either of those values."))))))))

(defun futures-resources-available ()

; This function is our attempt to guess when resources are available.  When
; this function returns true, then resources are probably available, and a
; parallelism primitive call will opt to parallelize.  We say "probably"
; because correctness does not depend on our answering exactly.  For
; performance, we prefer that this function is reasonably close to an accurate
; implementation that would use locks.  Perhaps even more important for
; performance, however, is that we avoid the cost of locks to try to remove
; bottlenecks.

; In summary, it is unnecessary to acquire a lock, because we just don't care
; if we miss a few chances to parallelize, or parallelize a few extra times.

  (and (f-get-global 'parallel-execution-enabled *the-live-state*)
       (futures-parallelism-buffer-has-space-available)
       (not-too-many-futures-already-in-existence)))

(define-atomically-modifiable-counter *threads-waiting-for-starting-core*

; Once upon a time this variable was only used for debugging purposes, so we
; didn't make its updates atomic.  However, we actually observed this variable
; going to a value of -37 (it should never go below 0) when we weren't using
; atomic updates.  Plus, now we actually use this variable's value to determine
; whether we spawn closure consumers.  So, as of April 2012, it is an atomic
; variable.

  0)

(defun claim-starting-core ()

; Parallelism wart: consider the possibility that the atomic-incf completes,
; and then a control-c causes an interrupt before the unwind-protect is entered
; -- so we leave *threads-waiting-for-starting-core* incremented, and its value
; creeps up this way during the ACL2 session.  A solution may be to have a flag
; that is set when the atomic-incf is completed, and set that flag within a
; without-interrupts.

  (atomic-incf *threads-waiting-for-starting-core*)
  (let ((notification (make-semaphore-notification)))
    (unwind-protect-disable-interrupts-during-cleanup
     (wait-on-semaphore *idle-core* :notification notification)
     (progn
       (when (semaphore-notification-status notification)
         (setf *allocated-core* *starting-core*)
         (atomic-decf *idle-future-core-count*)

; Parallelism blemish: is this really the right place to do the following setf?

         (setf *decremented-idle-future-thread-count* t)
         (atomic-decf *idle-future-thread-count*))
       (atomic-decf *threads-waiting-for-starting-core*)))))

(defun claim-resumptive-core ()

; Parallelism blemish: the following script provokes a bug where the
; *idle-resumptive-core* semaphore signal isn't being appropriately
; received... most likely because it's not being signaled (otherwise it would
; be a CCL issue).

;; (defun make-and-read-future ()
;;   (future-read (future 3)))

;; (time$ (dotimes (i 100000)
;;          (make-and-read-future)))

;; (defvar *making-and-reading-done*
;;   (make-semaphore))

;; (defun make-and-read-future-100000-times ()
;;   (time$ (dotimes (i 100000)
;;            (make-and-read-future)))
;;   (signal-semaphore *making-and-reading-done*))

;; (defun make-and-read-future-in-multiple-threads (thread-count)
;;   (time
;;    (dotimes (i thread-count)
;;      (run-thread "making and reading futures"
;;                  #'make-and-read-future-100000-times))
;;    (dotimes (i thread-count)
;;      (wait-on-semaphore *making-and-reading-done*))))

;; (make-and-read-future-in-multiple-threads 2)

  (let ((notification (make-semaphore-notification)))
    (unwind-protect-disable-interrupts-during-cleanup
     (wait-on-semaphore *idle-resumptive-core* :notification notification)
     (when (semaphore-notification-status notification)
       (setf *allocated-core* *resumptive-core*)
       (atomic-decf *idle-future-resumptive-core-count*)))))

(defun free-allocated-core ()

; This function frees an allocated core only if there is one!  Thus, it is
; perfectly safe to call this function even when a core has not been allocated
; to the current thread.  This notion is thread-local, as is the special
; variable *allocated-core*.

  (without-interrupts
   (cond ((eq *allocated-core* *starting-core*)
          (atomic-incf *idle-future-core-count*)
          (signal-semaphore *idle-core*)
          (setf *allocated-core* nil))

         ((eq *allocated-core* *resumptive-core*)
          (atomic-incf *idle-future-resumptive-core-count*)
          (signal-semaphore *idle-resumptive-core*)
          (setf *allocated-core* nil))
; Under early termination, the early terminated thread doesn't acquire a
; resumptive core.
         (t nil))
   t))

(defun early-terminate-children (index)

; With the current design, it is assumed that only one thread will be issuing
; an early termination order to any given future -- the thread that generated
; the future stored at the given index.  It's possible to change the design,
; but it would require more locking.

; Due to this more specific design, the function is named
; "early-terminate-children.  A more general function could be named
; "early-terminate-relatives".

  (abort-future-indices (faref *future-dependencies* index))
  (setf (faref *future-dependencies* index) nil))

; Debug variables:
(defvar *aborted-futures-via-flag* 0)
(defvar *aborted-futures-total* 0)

; Debug variables:
(defvar *futures-resources-available-count* 0)
(defvar *futures-resources-unavailable-count* 0)

(defun set-thread-check-for-abort-and-funcall (future)

; This function sets the current index in *thread-array* to the current thread,
; checks whether the given future has been marked as aborted, and if not then
; executes the closure field of the given future.

  (let* ((index (mt-future-index future))
         (closure (mt-future-closure future))
; Bind thread-local versions of special variables here.
         (*allocated-core* nil)
         (*current-thread-index* index)
         (*decremented-idle-future-thread-count* nil)
         (early-terminated t))
    (unwind-protect-disable-interrupts-during-cleanup
     (progn

; It might not be necessary to claim a starting core until after we check
; whether the future has been marked as aborted.  But David Rager believes that
; he had a reason for doing things in this order, and the resulting
; inefficiency seems very minor, so we leave this as is.

       (claim-starting-core) ; It is common to wait here.
       (setf (faref *thread-array* index) (current-thread))
       (if (mt-future-aborted future)
           (incf *aborted-futures-via-flag*)
         (progn ;(format t "starting index ~s~%" *current-thread-index*)
                (setf (mt-future-value future)
                      (multiple-value-list (funcall closure)))
                ;(format t "done with index ~s~%" *current-thread-index*)
                (setq early-terminated nil)
; This broadcast used to occur outside the "if", but I think that was a
; potential bug.
                (broadcast-barrier (mt-future-valid future)))))
     (progn
; terminate first since we're about to free a cpu core, which would allow
; worker threads to pickup the children sooner
       (setf (faref *thread-array* index) nil)
       (when early-terminated (early-terminate-children index))
       (setf (faref *future-dependencies* index) nil)

       (when *decremented-idle-future-thread-count*
; increment paired with decrement in (claim-starting-core)
         (atomic-incf *idle-future-thread-count*))
       (free-allocated-core)

       (setf (faref *future-array* index) nil)
       ;; (setf *current-thread-index* -1) ; falls out of scope
       ))))

(defvar *throwable-future-worker-thread*

; A given thread may be interrupted and told to throw the tag
; :result-no-longer-needed, as a means to abort a future.  However, it will
; ignore that request if and only if this (thread-local) variable is nil.  In
; the case that this variable is nil, there's no point in throwing said tag,
; because there is no work to abort.
;
; *Throwable-future-worker-thread* is unrelated to tag
; :worker-thread-no-longer-needed.

; Parallelism blemish: pick a name that makes it more obvious that this
; variable is unrelated to variable *throwable-worker-thread*.

 nil)

(defun wait-for-a-closure ()

; To understand this function, first consider *last-slot-saved* and
; *last-slot-taken*.  These are indices into *future-array*, where
; *last-slot-saved* is the maximum index at which a future produced to be
; executed was placed, while *last-slot-taken* is the maximum index from which
; a future has been consumed by a worker thread.  So when taken < saved, the
; indices inbetween hold futures that are awaiting execution.  Thus, when taken
; >= saved, there is no work waiting to be started.  Note that these "indices"
; actually can grow without bound; function faref comprehends the wrap-around
; nature of *future-array*, converting them to actual indices.

  (loop while (>= (atomically-modifiable-counter-read *last-slot-taken*)
                  (atomically-modifiable-counter-read *last-slot-saved*))
        do

; There is no work to be done, so wait on a semaphore that signals the
; placement of a new future in *future-array*.  The code below returns when
; either there is a timeout during that wait, or else a new future has been
; added to *future-array*.  In the latter case, *last-slot-saved* will have
; been increased.  Typically, *last-slot-taken* will not yet have been
; increased -- the current thread will increment it soon after returning from
; this function.  (Note that the increment happens before execution of the new
; future by this thread, which will take place when a core becomes available --
; and that may take awhile).

; Why are we in a while loop?  Even though *last-slot-saved* has been increased
; and the current thread has not yet increased *last-slot-taken*, it is
; possible for some other thread to increase *last-slot-taken*.  That can
; happen when another thread comes along just after the semaphore notification
; comes to the current thread, below, and the other thread sees the test above
; as false -- so for that thread, the present function does nothing and that
; thread goes on to increment *last-slot-taken*.

; But how long do we wait on the semaphore, below, before timing out?

; As of Feb 19, 2012, instead of picking a somewhat random duration to wait, we
; would always wait 15 seconds.  This was fine, except that a proof done by
; Robert Krug caused over 3000 threads to become active at the same time,
; because Rager's Lisp of choice (CCL) was so efficient in its handling of
; threads and semaphore signals.  Our solution to this problem involves calling
; the function random, below.  Here are more details:

; Put briefly, the implementation of timeouts in CCL is so good, that once a
; proof finishes, if there was a tree of subgoals (suppose those subgoals are
; named Subgoal 10000, Subgoal 9999, ... Subgoal 2) blocked on Subgoal 1
; finishing (which his how the implementation of waterfall1-lst works as of Feb
; 19, 2012), once Subgoal 1 finishes, each thread associated with Subgoal
; 10000, Subgoal 9999, ... Subgoal 2, Subgoal 1 will finish computing at
; approximately the same time (Subgoal 10000 is waiting for Subgoal 9999,
; Subgoal 9999 is waiting on Subgoal 9998... and so forth).  As such, once all
; 10,000 of these threads decide to wait on the semaphore *future-added*, as
; below, they were all enqueued to run at almost exactly the same time (15
; seconds from when they finished proving their subgoal) by the CPU scheduler.
; This results in the 1-minute Average Load-time (a Linux term, see
; http://www.linuxjournal.com/article/9001 for further info) shooting through
; the roof (upwards of 1000 in some cases), and then the Linux daemon process
; "watchdog" (see the Linux man page for watchdog) tells the machine to reboot,
; because "watchdog" thinks all chaos has broken loose (but, of course, chaos
; has not broken loose).  We _could_ argue with system maintainers about what
; an appropriate threshold is for determining when chaos breaks loose, but it
; would be silly.  We're not even coding ACL2(p) just for use in one
; environment -- we want it to work at all institutions without having to
; trouble sysadmins.  As such, rather than worry about this anymore, we
; circumvent the problem by doing the following: Instead of having every thread
; wait 15 seconds for new parallelism work to enter the system, we have every
; thread wait a random amount of time, within a reasonable range.

; One can see Section "Another Granularity Issue Related to Thread Limitations"
; inside :DOC topic parallelism-tutorial for an explanation of how user-level
; programs can have trees of nested computation.

        (let ((random-amount-of-time (+ 10 (random 110.0))))
          (when (not (wait-on-semaphore *future-added*
                                        :timeout random-amount-of-time))

; Then we timed out.  (If the semaphore had been obtained, then the above call
; of wait-on-semaphore would have returned t.)

            (throw :worker-thread-no-longer-needed nil)))))

; Debug variables:
(defvar *busy-wait-var* 0)
(defvar *current-waiting-thread* nil)
(defvar *fresh-waiting-threads* 0)

; We now develop support for our throw-catch-let macro.  Note that "tclet"
; abbreviates "throw-catch-let".

(defun make-tclet-thrown-symbol1 (tags first-tag)
  (if (endp tags)
      ""
    (concatenate 'string
                 (if first-tag
                     ""
                   "-OR-")
                 (symbol-name (car tags))
                 "-THROWN"
                 (make-tclet-thrown-symbol1 (cdr tags) nil))))

(defun make-tclet-thrown-symbol (tags)
  (intern (make-tclet-thrown-symbol1 tags t) "ACL2"))

(defun make-tclet-bindings1 (tags)
  (if (endp tags)
      nil
    (cons (list (make-tclet-thrown-symbol (reverse tags))
                t)
          (make-tclet-bindings1 (cdr tags)))))

(defun make-tclet-bindings (tags)
  (Reverse (make-tclet-bindings1 (reverse tags))))

(defun make-tclet-thrown-tags1 (tags)
  (if (endp tags)
      nil
    (cons (make-tclet-thrown-symbol (reverse tags))
          (make-tclet-thrown-tags1 (cdr tags)))))

(defun make-tclet-thrown-tags (tags)
  (reverse (make-tclet-thrown-tags1 (reverse tags))))

(defun make-tclet-catches (rtags body thrown-tag-bindings)
  (if (endp rtags)
      body
    (list 'catch
          (list 'quote (car rtags))
          (list 'prog1 ; 'our-multiple-value-prog1 ; we don't support multiple-values at all
           (make-tclet-catches (cdr rtags) body (cdr thrown-tag-bindings))
           `(setq ,(car thrown-tag-bindings) nil)))))


(defun make-tclet-cleanups (thrown-tags cleanups)
  (if (endp thrown-tags)
      '((t nil))
    (cons (list (car thrown-tags)
                (car cleanups))
          (make-tclet-cleanups (cdr thrown-tags)
                         (cdr cleanups)))))

(defmacro throw-catch-let (tags body cleanups)

; This macro takes three arguments:

; Tags is a list of tags that can be thrown from within body.

; Body is the body to execute.

; Cleanups is a list of forms, one of which will be executed in the event that
; the corresponding tag is thrown.  The tags and cleanup forms are given their
; association with each other by their order.  So, if tag 'x-tag is the third
; element in tags, the cleanup form for 'x-tag should similarly be the third
; form in cleanups.

; This macro does not support throwing multiple-values as a throw's return
; value.  (Probably it could, however, by replacing prog1 by
; multiple-value-prog1.)

; Consider the following example.

;   (throw-catch-let
;    (one two three)
;    ; The following might invoke (throw 'one), (throw 'two), and/or
;    ; (throw 'three).
;    (arbitrary-code-here)
;    ((handle-one)
;     (handle-two)
;     (handle-three)))

; Here is the single-step macroexpansion of the above example.

;   (let ((one-thrown t)
;         (one-thrown-or-two-thrown t)
;         (one-thrown-or-two-thrown-or-three-thrown t))
;     (let ((tclet-result
;            (catch 'one
;              (prog1 (catch 'two
;                       (prog1 (catch 'three
;                                (prog1
;                                 (arbitrary-code-here)
;                                 (setq
;                                  one-thrown-or-two-thrown-or-three-thrown
;                                  nil)))
;                              (setq one-thrown-or-two-thrown nil)))
;                     (setq one-thrown nil)))))
;       (prog2 (cond (one-thrown (handle-one))
;                    (one-thrown-or-two-thrown (handle-two))
;                    (one-thrown-or-two-thrown-or-three-thrown
;                     (handle-three))
;                    (t nil))
;              tclet-result)))

; Here is a more concrete example use of throw-catch-let.

;   (throw-catch-let
;    (x y)
;    (cond ((equal *flg* 3) (throw 'x 10))
;          ((equal *flg* 4) (throw 'y 11))
;          (t 7))
;    ((setq *x-thrown* t)
;     (setq *y-thrown* t)))

; While Rager wrote this macro, he thanks Nathan Wetzler for co-development of
; the main ideas.

  (let* ((thrown-tags (make-tclet-thrown-tags tags)))
    `(let ,(make-tclet-bindings tags)
       (let ((tclet-result ,(make-tclet-catches tags body thrown-tags)))
         (prog2 (cond ,@(make-tclet-cleanups thrown-tags cleanups))
             tclet-result)))))

(defun eval-a-closure ()
  (let* ((index (atomic-incf *last-slot-taken*))
         (*current-thread-index* index)
         (thrown-tag nil)
         (thrown-val nil)
         (future nil))

; Hopefully very rarely, we busy wait for the future to arrive.  That can
; happen because *last-slot-saved* is incremented before the future is actually
; put there.

    (loop while (not (faref *future-array* index)) do

; Set debugging variables *busy-wait-var*, *current-waiting-thread*, and
; *fresh-waiting-threads*.

          (incf *busy-wait-var*)
          (when (not (equal (current-thread) *current-waiting-thread*))
            (setf *current-waiting-thread* (current-thread))
            (incf *fresh-waiting-threads*)))

; The tags we need to catch for throwing again later are raw-ev-fncall,
; local-top-level, time-limit5-tag, and step-limit-tag.  We do not bother
; catching missing-compiled-book, because the code that throws it says it would
; be an ACL2 implementation error to actually execute the throw.  If other tags
; are later added to the ACL2 source code, we should add them to the below
; throw-catch-let.

    (throw-catch-let
     (raw-ev-fncall local-top-level time-limit5-tag step-limit-tag)
     (catch :result-no-longer-needed
         (let ((*throwable-future-worker-thread* t))
           (progn (setq future (faref *future-array* index))
                  (set-thread-check-for-abort-and-funcall future))))
     ((progn (setf thrown-tag 'raw-ev-fncall) (setf thrown-val tclet-result))
      (progn (setf thrown-tag 'local-top-level) (setf thrown-val tclet-result))
      (progn (setf thrown-tag 'time-limit5-tag) (setf thrown-val tclet-result))
      (progn (setf thrown-tag 'step-limit-tag) (setf thrown-val tclet-result))))

; The following does not need to be inside an unwind-protect-cleanup because
; set-thread-check-for-abort-and-funcall also removes the pointer to this
; thread in *thread-array*.

    (atomic-decf *unassigned-and-active-future-count*)
    (atomic-decf *total-future-count*)
    (when thrown-tag
      (setf (mt-future-thrown-tag future)
            (cons thrown-tag thrown-val))

; A future that threw a tag is still a legal future to read.  In fact, the
; throw does not re-occur until the future is read; see the throw in
; mt-future-read.

      (broadcast-barrier (mt-future-valid future)))))

(defun eval-closures ()

; Worker threads are initialized to run this function; see the call of
; run-thread in spawn-closure-consumers.

; The following is done inside the spawner, spawn-closure-consumers.
; (atomic-incf *idle-future-thread-count*)

  (catch :worker-thread-no-longer-needed

; The catch of a somewhat analogous tag :result-no-longer-needed, is performed
; inside eval-a-closure (called below).

    (let ((*throwable-worker-thread*

; Note that at the place we consider throwing to
; :worker-thread-no-longer-needed, we check that *throwable-worker-thread* is t
; as an indicator that the corresponding catcher is set up.

           t)

; We must bind *default-hs* to NIL so that each thread will get its own hons
; space whenever it uses honsing code.  We could alternately call
; (hl-hspace-init) here, but using NIL allows us to avoid the overhead of
; initializing a hons space unless honsing is used in this thread.  See also
; the notes in hons-raw.lisp.

          (*default-hs* nil))
      (declare (special *default-hs*)) ; special declared in hons-raw.lisp

; The following loop is exited by a throw to :worker-thread-no-longer-needed,
; which is performed by wait-for-a-closure when there has been no closure to
; execute for a random-amount-of-time (see wait-for-a-closure; currently from
; 10 to 120 seconds).

      (loop
       (wait-for-a-closure)
       (eval-a-closure))))

; The following decrement will always execute, unless the user terminates the
; thread in raw Lisp in an unsupported manner.

  (atomic-decf *idle-future-thread-count*))

(defun number-of-idle-threads-and-threads-waiting-for-a-starting-core ()

; See (A) and (B) in the Essay on Parallelism [etc.].

  (+ (atomically-modifiable-counter-read ; (A)
      *idle-future-thread-count*)
     (atomically-modifiable-counter-read ; (B)
      *threads-waiting-for-starting-core*)))

(defun spawn-closure-consumers ()

; A call of a parallelism primitive invokes this function in order to ensure
; that there are threads available to pick up the piece of work that it has
; created (by adding a future to the work queue).  As far as we know, we could
; get by just fine by spawning at most one thread, rather than spawning threads
; to bring the total in the (A) or (B) state (see the Essay on Parallelism
; [etc.]) up to *max-idle-thread-count*, as we do here.  But in case we have
; missed something in our design that could cause us to have insufficient
; threads ready to do work, we try to keep the number of threads in the (A) or
; (B) state at the limit we have chosen, i.e., *max-idle-thread-count*.

  (without-interrupts

; Parallelism blemish: there may be a bug where *idle-future-thread-count* is
; incremented to 64 under early termination.

; We bring the number of threads in state (A) or (B), as described above, up to
; our specified limit.  Why not count just those in state (A)?  In fact, we did
; so up to April, 2012.  The problem was that this function could create
; threads in state (A), which transition to (B) and wait for a core, and then
; this function could continue to do this repeatedly, resulting in a huge
; number of threads (in state (B)), which could swamp the system.  Our current
; approach solves this problem.  Note that it can be common for
; *idle-future-thread-count* to be 0, because the created threads have moved to
; state (B) but not yet been allocated a core.

   (loop while (< (number-of-idle-threads-and-threads-waiting-for-a-starting-core)
                  *max-idle-thread-count*)
     do
     (progn (atomic-incf *idle-future-thread-count*)
            (incf *threads-spawned*) ; debug variable
            (run-thread "Worker thread" 'eval-closures)))))

(defun make-future-with-closure (closure)

; Create a future with the indicated closure.

; The assertions below can fire if a long-running future is created before the
; current index (*last-slot-saved*) of the *future-array* wraps around to 0 and
; then back to the index of the long-running future.  This could happen in the
; use of futures in the ACL2(p) code, i.e., for parallelizing the waterfall,
; but only if very many subgoals (never seen as of April, 2012) are created
; during a single call of the waterfall, so large in fact that a goal's future
; remains active after creating *future-array-size* more futures.

; The basic problem, of potentially overwriting an entry in an array after
; wrapping around, could in principle be solved by just skipping over any such
; indices until finding an available index.  Then an error would only occur if
; all *future-array-size* entries are active.  However, David Rager has
; explained that the current implementation relies upon incrementing the
; current index by just 1, and in fact takes advantage of that in communication
; between producers and consumers of futures.  If we change the implementation
; to allow such skipping, we need to think about communication between
; producers and consumers, and we should think about whether we will lose
; efficiency.  And we might well lose efficiency, because we may need to lock
; down the entire array as we look for a free index, rather than using atomic
; increments (and avoiding locks entirely) as we do now.

  (let ((future (make-mt-future))
        (index (atomic-incf *last-slot-saved*)))
    (assert (not (faref *thread-array* index)))
    (assert (not (faref *future-array* index)))
    (assert (not (faref *future-dependencies* index)))
    (setf (mt-future-index future) index)
    (setf (faref *future-dependencies* *current-thread-index*)

; Add the index of the new future to the list of futures that must be aborted
; if the current thread is aborted.

          (cons index (faref *future-dependencies* *current-thread-index*)))
    (setf (mt-future-closure future) closure)
    future))

(defun add-future-to-queue (future)

; This function must be called with interrupts disabled.

  (setf (faref *future-array* (mt-future-index future))
        future)
  (atomic-incf *total-future-count*)
  (atomic-incf *unassigned-and-active-future-count*)
  (spawn-closure-consumers)
  (signal-semaphore *future-added*)
  future)

(defun make-closure-expr-with-acl2-bindings (body)

; This function returns an expression that evaluates to a closure.  When the
; resulting closure is called later, it will be in an ACL2 environment that
; respects certain special variables.

; We need to set up bindings for some special variables to have appropriate
; values when the given body is ultimately executed, as occurs when executing
; closures that are executed by mt-future and closure-for-expression.  Note
; that the current value of a special variable is irrelevant for its value in a
; newly created thread, as illustrated in the following log.

;   ? [RAW LISP] (defvar foo 1)
;   FOO
;   ? [RAW LISP] (let ((foo 2))
;                  (run-thread "asdf"
;                              (lambda ()
;                                (list (print foo)
;                                      (print (symbol-value 'foo))))))
;   #<PROCESS asdf(3) [Reset] #x302003CEE58D>
;   ? [RAW LISP]
;   1
;   1

; Parallelism no-fix: we have considered causing child threads to inherit
; ld-specials from their parents, or even other state globals such as
; *ev-shortcut-okp* and raw-guard-warningp, as the following comment from
; David Rager suggests.  But this now seems too difficult to justify that
; effort, and we do not feel obligated to do so; see the "IMPORTANT NOTE" in
; :doc parallelism.

;   At one point, in an effort to fix printing in parallel from within
;   wormholes, I tried rebinding the ld-specials.  I now know that my approach
;   at that time was doomed to fail, because these specials aren't implemented
;   as global variables but instead as a setq of a variable in a completely
;   different package.  Now that I understand how state global variables work
;   in ACL2, it may be worth coming back to this code and trying once again to
;   inherit the ld-specials (listed in *initial-ld-special-bindings*).  We
;   could also consider binding *deep-gstack*, and it seems that we also should
;   bind *wormhole-cleanup-form* since we bind *wormholep*, but we haven't done
;   so.

  (let ((ld-level-sym (gensym))
        (ld-level-state-sym (gensym))
        (wormholep-sym (gensym))
        (local-safe-mode-sym (gensym))
        (local-gc-on-sym (gensym)))
    `(let* ((,ld-level-sym *ld-level*)
            (,ld-level-state-sym

; We have discussed with David Rager whether it is an invariant of ACL2 that
; *ld-level* and (@ ld-level) have the same value, except perhaps when cleaning
; up with acl2-unwind-protect.  If it is, then David believes that it's also an
; invariant of ACL2(p).  We add an assertion here to check that.

             (assert$ (equal *ld-level*
                             (f-get-global 'ld-level *the-live-state*))
                      (f-get-global 'ld-level *the-live-state*)))
            (acl2-unwind-protect-stack *acl2-unwind-protect-stack*)
            (,wormholep-sym *wormholep*)
            (,local-safe-mode-sym (f-get-global 'safe-mode *the-live-state*))
            (,local-gc-on-sym (f-get-global 'guard-checking-on
                                            *the-live-state*)))
       (lambda ()
         (let ((*ld-level* ,ld-level-sym)
               (*acl2-unwind-protect-stack*
                acl2-unwind-protect-stack)
               (*wormholep* ,wormholep-sym))
           (state-free-global-let*
            ((ld-level ,ld-level-state-sym)
             (safe-mode ,local-safe-mode-sym)
             (guard-checking-on ,local-gc-on-sym))
            ,body))))))

(defmacro mt-future (x)

; Return a future whose closure, when executed, will execute the given form, x.
; Note that (future x) macroexpands to (mt-future x).

  `(cond
    (#-skip-resource-availability-test
     (not (futures-resources-available))
     #+skip-resource-availability-test
     nil

; need to return a "single-threaded" future

     (incf *futures-resources-unavailable-count*)
     (st-future ,x))
    (t ; normal case
     (incf *futures-resources-available-count*)
     (without-interrupts
      (let ((future (make-future-with-closure
                     ,(make-closure-expr-with-acl2-bindings x))))
        (without-interrupts ; probably not needed
         (add-future-to-queue future))
        future)))))

(defun mt-future-read (future)
  (cond ((st-future-p future)
         (st-future-read future))
        ((mt-future-p future)
         (when (not (barrier-value (mt-future-valid future)))

; Block until the value in the future is available (valid).

           (let ((notif nil))
             (unwind-protect-disable-interrupts-during-cleanup
              (progn
                (without-interrupts
                 (free-allocated-core)

; David Rager believes that at one time, he was concerned that the following
; atomic decrement may be broken under early termination, though he didn't see
; how.

                 (atomic-decf *unassigned-and-active-future-count*)
                 (setq notif t))

; Although we are about to wait for the valid bit to be set, it's possible that
; (barrier-value (mt-future-valid future)) has become true by now, so maybe
; it's tempting to add such a test.  However, the call of wait-on-barrier below
; is already doing such a test, and it would save little or no time to do it
; explicitly before calling wait-on-barrier.

                (wait-on-barrier (mt-future-valid future))

; The following claiming isn't necessary under early termination, and in fact,
; under early termination, the claiming usually doesn't occur because it's in
; the unprotected part of the unwind-protect.  It's unnecessary because if
; we're terminating early, we don't really care whether we "claim" the core.
; In fact, we actually prefer to leave the core unclaimed, because claiming the
; core would require blocking until we temporarily receive a semaphore signal.

                (claim-resumptive-core))
              (when notif ; clean up
                (atomic-incf *unassigned-and-active-future-count*)))))
         (when (mt-future-thrown-tag future)
           (throw (car (mt-future-thrown-tag future))
                  (cdr (mt-future-thrown-tag future))))
         (values-list (mt-future-value future)))
        (t
         (error "future-read was given a non-future argument"))))

; Debug variables:
(defvar *aborted-futures-via-throw* 0)
(defvar *almost-aborted-future-count* 0)

(defun mt-future-abort (future)

; All calls to mt-future-abort must be made by the parent of the future being
; aborted.  This gives us some notion of single-threadedness, which removes the
; need for locking in some of the code below.  This means the aborting
; mechanism would not work for pand/por.

; We might consider relaxing the above precondition, but we would need to think
; first about whether we need to make corresponding changes, even beyond the
; definition of this function.  For example, under the above precondition it is
; impossible to interrupt the current thread more than once.  Without that
; precondition, we might have two such interrupts, both of which are executing
; code that potentially throws to tag :result-no-longer-needed.  As things
; stand, we believe that probably only one such throw will actually take place,
; since the actual throw is conditionalized on a variable that is only true
; when a catcher is in place.  Still, if we do indeed relax the above
; precondition, we should think this through carefully.

; But there is an even more serious problem with relaxing the precondition.
; Due to the reading and writing of slots in *future-dependencies*, only one
; thread should be able to create and abort its children.  Otherwise those
; slots could become corrupt.

; This abortion is non-blocking; i.e., it will issue an abort and return.  It
; doesn't know when the abort will actually occur.

; It's possible that future will be nil.  This happens when the future has
; already finished execution and set its position in *future-array* to nil.

  (incf *aborted-futures-total*)
  (cond ((st-future-p future)
         (st-future-abort future))
        ((mt-future-p future)

; Parallelism wart: consider deleting the comment just below.

; It doesn't make sense to abort a future that's really just a value.  We
; assume that we can't return a future in a future... which may not be
; valid... ouch.  We're probably okay, simply because an abort means the value
; doesn't matter. TODO: fix that maybe?

         (acl2::without-interrupts
          (let ((index (mt-future-index future)))
            (assert index)
            (setf (mt-future-aborted future) t)
            (let ((thread (faref *thread-array* index)))
              (when thread
                (interrupt-thread
                 thread
                 (lambda ()
                   (if (equal (mt-future-index future)
                              *current-thread-index*)

; Parallelism wart: review the comment below, perhaps clarifying it, that
; explains how the equal test above could fail.  David thinks it has to do with
; the six cases in how a future aborts computation.

; *Almost-aborted-future-count* can be incremented when the
; *current-thread-index* has fallen back to its default value, 0, for when the
; thread is unassociated with any future.  It can also be incremented when the
; thread has already picked up a new piece of work, but in practice this latter
; occurrence will almost never happen.

                       (when *throwable-future-worker-thread*
                         (incf *aborted-futures-via-throw*)
                         (throw :result-no-longer-needed nil))
                     (incf *almost-aborted-future-count*)))))))))
        ((null future) t) ; future already removed from the future-array
        (t
         (error "future-abort was given a non-future argument")))
  future)

(defun abort-future-indices (indices)

; Parallelism wart: clarify the following comment.

; Only call from future-abort, which has a theoretical read-lock on the value
; of indices (I quite literally mean "theoretical", as only by reasoning can we
; deduce that the source of the argument "indices", array
; *future-dependencies*, is not changing underneath us).

  (if (endp indices)
      t
    (progn (mt-future-abort (faref *future-array* (car indices)))
           (abort-future-indices (cdr indices)))))

(defun print-non-nils-in-array (array n)
  (if (equal n (length array))
      "end"
    (if (null (faref array n))
        (print-non-nils-in-array array (1+ n))
      (progn (print n)
             (print (faref array n))
             (print-non-nils-in-array array (1+ n))))))

(defun futures-still-in-flight ()

; Returns t if there are futures still in the work-queue to process or if there
; are futures already being processed.

  (< 1 (atomically-modifiable-counter-read
        *unassigned-and-active-future-count*)))


;---------------------------------------------------------------------
; Section:  Futures Interface

(defmacro future (x)
  `(mt-future ,x))

(defun future-read (x)
  (mt-future-read x))

(defun future-abort (x)
  (mt-future-abort x))

(defun abort-futures (futures)
  (cond ((endp futures)
         t)
        (t (future-abort (car futures))
           (abort-futures (cdr futures)))))
