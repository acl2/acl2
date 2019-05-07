; ACL2 Version 8.2 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2019, Regents of the University of Texas

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

; Section:  Parallelism Basis
; Section:  Work Consumer Code
; Section:  Work Producer Code
; Section:  Parallelism Primitives

; In particular, see the Essay on Parallelism Definitions and the Essay on
; Parallelism Strategy for overviews on this implementation of parallel
; evaluation.

(in-package "ACL2")

;---------------------------------------------------------------------
; Section:  Parallelism Basis

; In this section we outline definitions and strategies for parallel evaluation
; and define constants, structures, variables, and other basic parallelism
; infrastructure.

; Essay on Parallelism Definitions

; Core
;
; A core is a unit inside a computer that can do useful work.  It has its own
; instruction pointers and usually accesses shared memory.  In the old days, we
; had "dual processors."  This is an example of a two core system.  A
; 2006-vintage example of a four core system is "dual sockets" with "dual core
; technology."

; Process
;
; We generally use the term "process" as a verb, meaning: run a set of
; instructions.  For example, the system can process a closure.

; Thread
;
; We use the OS definition of a thread as a lightweight process that shares
; memory with other threads in the same process.  A thread in our system is in
; one of the following three states.
;
;   1. Idle - The thread is waiting until both a piece of work (see below) and
;   a core are available.
;
;   2. Active - The thread has been allocated a core and is processing some
;   work.
;
;   3. Pending - This state occurs iff the thread in this state is associated
;   with a parent piece of work, and it is waiting for the children of that
;   piece of work to complete and for sufficient CPU core resources.  A thread
;   in this state is often waiting on a signaling mechanism.

; Closure
;
; We use the term "closure" in the Lisp sense: a function that captures values
; of variables from the lexical environment in which it is formed.  A closure
; thus contains enough information to be applied to a list of arguments.  We
; create closures in the process of saving work to be performed.

; Work
;
; A piece of work contains all the data necessary for a worker thread to
; process one closure, save its result somewhere that a parent can read it, and
; communicate that it is finished.  It also contains some data necessary to
; implement features like the early termination of parallel and/or.  Comments
; at parallelism-piece give implementation details.

; Roughly, work can be in any of four states: unassigned, starting, pending, or
; resumed.  A piece of work will be processed by a single worker thread (not
; including, of course, child work, which will be processed by other worker
; threads).  When a core becomes available, a thread can grab an unassigned
; piece of work, at which time the thread and the piece of work leave their
; initial states together.  From that point forward until the piece of work is
; complete, the piece of work and its associated worker thread are considered
; to be in corresponding states (active/started,resumed or pending).  Initially
; they are in their active/started states.  Later, if child work is created,
; then at that time the thread and its associated piece of work both enter the
; pending state.  When all child work terminates and either a CPU core becomes
; available or a heuristic allows an exception to that requirement, the piece
; of work enters the resumed state and its associated worker thread re-enters
; the active state.  This heuristic (implemented in
; wait-for-resumptive-parallelism-resources) gives priority to such resumptions
; over starting new pieces of work.

; Parallelism Primitive
;
; A macro that enables the user to introduce parallelism into a computation:
; one of plet, pargs, pand, and por.

; End of Essay on Parallelism Definitions

; Essay on Parallelism Strategy

; Whenever a parallelism primitive is used, the following steps occur.  The
; text between the < and > describes the state after the previous step
; finishes.

;  1. If there is a granularity form, the form is evaluated.  If the form
;     returns nil, the parallelism primitive expands to the serial equivalent;
;     otherwise we continue.

; < granularity form has returned true or was omitted - the system was given a
; "large" amount of work >

;  2. If we heuristically determine that the system is already overwhelmed with
;     too much work (see parallelism-resources-available for details), then the
;     primitive expands to its serial equivalent; otherwise we continue.

;  3. Create closures for each primitive's arguments, as follows.
;     - Plet:  one closure for each form assigned to a bound variable
;     - Pargs:  one closure for each argument to the function call
;     - Pand/Por: one closure for each argument

; < have closures in memory representing computation to parallelize >

;  4. Create the data structures for pieces of work that worker threads are to
;     process.  One such data structure (documented in *work-queue* below) is
;     created for each computation to be spawned.  Among the fields of each
;     such structure is a closure that represents that computation.  Siblings
;     have data structures that share some fields, such as a result-array that
;     is to contain the values returned by the sibling computations.
;
;     The system then adds these pieces of work to the global *work-queue* for
;     worker threads to pop off the queue and process.
;
;     Note that Step 2 avoids creating undesirably many pieces of work.
;     (Actually the heuristics used in Step 2 don't provide exact guarantees,
;     since two computations that reach Step 2 simultaneously might both
;     receive the go-ahead even though together, they create work that exceeds
;     the heuristic work limit).

; < now have unassigned work in the work-queue >

; 5.  After the parent thread adds the work to the queue, it will check to see
;     if more worker threads are needed and spawn them if necessary.  Note
;     however that if there are more threads than cores, then any newly spawned
;     thread will wait on a semaphore, and only begins evaluating the work when
;     a core becomes available.  Each core is assigned to at most one thread at
;     any time (but if this decision is revisited, then it should be documented
;     here and in the Parallelism Variables section.  Note that this decision
;     is implemented by setting *idle-core-count* to (1- *core-count*) in
;     reset-parallelism-variables).


;     Note that by limiting the amount of work in the system at Step 2, we
;     avoid creating more threads than the system can handle.

; < now have enough worker threads to process the work >

;  6. The parent thread waits for its children to signal their completion.  It
;     is crucial for efficiency that this waiting be implemented using a
;     signaling mechanism rather than as busy waiting.

; < the parent is waiting for the worker threads to process the work >

; 7.  At this point, the child threads begin processing the work on the queue.
;     As they are allocated resources, they each pull off a piece of work from
;     the work queue and save their results in the associated result-array.
;     After a child thread finishes a piece of work, it will check to see if
;     its siblings' computations are still necessary.  If not, the child will
;     remove these computations from the work queue and interrupt each of its
;     running sibling threads with a primitive that supplies a function for
;     that thread to execute.  This function throws to the tag
;     :result-no-longer-needed, causing the interrupted sibling to abort
;     evaluation of that piece of work, signal the parent (in an
;     unwind-protect's cleanup form on the way out to the catch), catch that
;     tag, and finally reenter the stalled state (where the controlling loop
;     will find it something new to do).  We take care to guarantee that this
;     mechanism works even if a child receives more than one interrupt.  Note
;     that when a child is interrupted in this manner, the value stored for the
;     child is a don't-care.

; < all of the children are done computing, the required results are in the
;   results-array, and the parent has been signaled a number of times equal to
;   the number of children >

; 8.  The parent thread (from steps 1-6) resumes.  It finds the results stored
;     in its results array.  If the primitive is a:
;     - Plet:  it executes the body of the plet with the calculated bindings
;     - Pargs:  it applies the called function to the calculated arguments
;     - Pand, Por:  it applies a functionalized "and" or "or" to the calculated
;                   arguments.  The result is Booleanized.

; End of Essay on Parallelism Strategy

; Parallelism Structures

; If the shape of parallelism-piece changes, update the *work-queue*
; documentation in the section "Parallelism Variables."

(defstruct parallelism-piece ; piece of work

; A data item in the work queue has the following contents, and we often call
; each a "piece of work."

; thread-array - the array that holds the threads spawned for that closure's
; particular parent

; result-array - the array that holds the results for that closure's particular
; parent, where each value is either nil (no result yet) or a cons whose cdr is
; the result

; array-index - the index into the above two arrays for this particular closure

; semaphore-to-signal-as-last-act - the semaphore to signal right before the
; spawned thread dies

; closure - the closure to process by spawning a thread

; throw-siblings-when-function - the function to funcall on the current
; thread's result to see if its siblings should be terminated.  The function
; will also remove work from the work-queue and throw the siblings if
; termination should occur.

  (thread-array nil)
  (result-array nil)
  (array-index -1)
  (semaphore-to-signal-as-last-act nil)
  (closure nil)
  (throw-siblings-when-function nil))

; Parallelism Variables

(progn

; Keep this progn in sync with reset-parallelism-variables, which resets the
; variables defined here.  Note that none of the variables are initialized
; here, so reset-parallelism-variables must be called before evaluating
; parallelism primitives (an exception is *throwable-worker-thread* since it is
; first called in reset-parallelism-variables).

; *Idle-thread-count* is updated both when a thread is created and right before
; it expires.  It is also updated when a worker thread gets some work to do and
; after it is done with that work.

  (define-atomically-modifiable-counter *idle-thread-count* 0)

; *Idle-core-count* is only used to estimate resource availability.  The number
; itself is always kept accurate using atomic writes.  Since atomic increments
; also stall reads, the value read is no longer only an estimate.  But since we
; don't perform the action associated with a test of the read result while
; holding a lock, it's as if the number read is just an estimate.  It defaults
; to (1- *core-count*), because the current thread is considered active.

; There are two pairs of places that *idle-core-count* is updated.  First,
; whenever a worker thread begins processing work, the count is decremented.
; This decrement is paired with the increment that occurs after a worker thread
; finishes work.  It is also incremented and decremented in
; eval-and-save-result, before and after a parent waits for its children.

; Note: At different stages of development we have contemplated having a
; "*virtual-core-count*", exceeding the number of CPU cores, that bounds the
; number of active threads.  Since our initial tests did not show a performance
; improvement by using this trick, we have not employed a *virtual-core-count*.
; If we later do employ this trick, the documentation in step 5 of the Essay on
; Parallelism Strategy will need to be updated.

  (define-atomically-modifiable-counter *idle-core-count* 0)

; *Unassigned-and-active-work-count* tracks the amount of parallelism work in
; the system, other than pending work.  It is increased when a parallelism
; primitive adds work to the system.  This increase is paired with the final
; decrease in consume-work-on-work-queue-when-there, which occurs when a
; piece of work finishes.  It is decremented and incremented (respectively)
; when a parent waits on children and when it resumes after waiting on
; children.

  (define-atomically-modifiable-counter *unassigned-and-active-work-count* 0)

; *Total-work-count* tracks the total amount of parallelism work.  This
; includes unassigned, started, pending, and resumed work.

  (define-atomically-modifiable-counter *total-work-count* 0)

; We maintain a queue of work to process.  See parallelism-piece for
; documentation on pieces of work.  Even though *work-queue* is a list, we
; think of it as a structure that can be destructively modified -- so beware
; sharing any structure with *work-queue*!

  (defvar *work-queue*)
  (deflock *work-queue-lock*)

; An idle thread waits for the signaling mechanism
; *check-work-and-core-availability* to be signaled, at which time it looks for
; work on the *work-queue* and an idle core to use.  This condition can be
; signaled by the addition of new work or by the availability of a CPU core.

; Warning: In the former case, a parent thread must always signal this
; semaphore *after* it has already added the work to the queue.  Otherwise, a
; child can attempt to acquire work, fail, and then go wait on the signaling
; mechanism again.  Since the parent has already signaled, there is no
; guarantee that the work they place on the queue will ever be processed.  (The
; latter case also requires analogous care.)

; Why are there two distinct signaling mechanisms, one for idle threads and one
; for resuming threads?  Suppose that idle and resuming threads waited on the
; same mechanism.  We would then have no guarantee that resuming threads would
; be signaled before the idle threads (which is necessary to establish the
; priority explained in wait-for-resumptive-parallelism-resources).  Using
; separate signaling mechanisms allows both an idle and resuming thread to be
; signaled.  Then whichever thread's heuristics allow it to execute will claim
; access to the CPU core.  There is no problem if both their heuristics allow
; them to continue.

; We omit the suffix "sem" from the following two variable names, because we do
; not want to think about the counter that resides inside semaphores.  Our
; intent is only to use them as a lockless signaling mechanism.

  (defvar *check-work-and-core-availability*)
  (defvar *check-core-availability-for-resuming*)

; *total-parallelism-piece-historical-count* tracks the total number of pieces
; of parallelism work processed over the lifetime of the ACL2 session.  It is
; reset whenever the parallelism variables are reset.  It is only used for
; informational purposes, and the system does not depend on its accuracy in any
; way.  We therefore perform no locking/synchronization when modifying its
; value.

  (defvar *total-parallelism-piece-historical-count*)

) ; end of parallelism variables

; Following are definitions of functions that help us restore the
; parallelism system to a stable state after an interrupt occurs.

(defparameter *reset-parallelism-variables* nil)

(defparameter *reset-core-count-too*

; This variable has a relatively unsophisticated use: When Rager runs his
; dissertation performance test scripts, sometimes he adjusts the number of
; cpu-cores to be a factor of the actual cpu-core count.  In this case we are
; just testing, and, to avoid resetting the core count variable every time we
; reset the parallelism system, we will want to set this variable to nil.

  t)

(defun reset-parallelism-variables ()

; We use this function (a) to kill all worker threads, (b) to reset "most" of
; the parallelism variables, and (c) to reset the lock and semaphore recycling
; systems.  Keep (b) in sync with the progn above that declares the variables
; reset here, in the sense that this function assigns values to exactly those
; variables.

; If a user kills threads directly from raw Lisp, for example using functions
; above, then they should call reset-parallelism-variables.  Note that
; reset-parallelism-variables is called automatically on any top-level call of
; LD (i.e., a call with *ld-level* = 0), as well as any time we return to the
; prompt after entering a raw Lisp break (using
; *reset-parallelism-variables*).

; This function is not to be confused with reset-future-parallelism-variables
; (although it is similar in nature).

; (a) Kill all worker threads.

  (send-die-to-worker-threads)

; (b) Reset "most" of the parallelism variables.

  (when *reset-core-count-too*

; We reset *core-count* and related variable(s) in case the current platform
; has a different number of CPU cores than the compilation platform had.

    (setf *core-count* (core-count-raw))
    (setf *unassigned-and-active-work-count-limit* (* 4 *core-count*)))

  (setf *idle-thread-count* (make-atomically-modifiable-counter 0))

  (setf *idle-core-count*
        (make-atomically-modifiable-counter (1- *core-count*)))

  (setf *unassigned-and-active-work-count*
        (make-atomically-modifiable-counter 1))

  (setf *total-work-count* (make-atomically-modifiable-counter 1))

  (setf *work-queue* nil)
  (reset-lock *work-queue-lock*)

  (setf *check-work-and-core-availability* (make-semaphore))
  (setf *check-core-availability-for-resuming* (make-semaphore))

  (setf *throwable-worker-thread* nil)

  (setf *total-parallelism-piece-historical-count* 0)

  (setf *reset-parallelism-variables* nil)

  t ; return t
)

;---------------------------------------------------------------------
; Section:  Work Consumer Code

; We develop functions that assign threads to process work.

(defun eval-and-save-result (work)

; Work is a piece of parallelism work.  Among its fields are a closure and an
; array.  We evaluate this closure and save the result into this array.  No
; lock is required because no other thread will be writing to the same position
; in the array.

; Keep this in sync with the comment in parallelism-piece, where we explain
; that the result is the cdr of the cons stored in the result array at the
; appropriate position.

  (assert work)
  (let ((result-array (parallelism-piece-result-array work))
        (array-index (parallelism-piece-array-index work))
        (closure (parallelism-piece-closure work)))
    (setf (aref result-array array-index)
          (cons t (funcall closure)))))

(defun pop-work-and-set-thread ()

; Once we exit the without-interrupts that must enclose a call to
; pop-work-and-set-thread, our siblings can interrupt us so that we execute a
; throw to the tag :result-no-longer-needed.  The reason they can access us is
; that they will have a pointer to us in the thread array.

; There is a race condition between when work is popped from the *work-queue*
; and when the current thread is stored in the thread-array.  This race
; condition could be eliminated by holding *work-queue-lock* during the
; function's entire execution.  Since (1) we want to minimize the duration
; locks are held, (2) the chance of this race condition occurring is small and
; (3) there is no safety penalty when this race condition occurs (instead an
; opportunity for early termination is missed), we only hold the lock for the
; amount of time it takes to read and modify the *work-queue*.

  (let ((work (with-lock *work-queue-lock*
                         (when (consp *work-queue*)
                           (pop *work-queue*))))
        (thread (current-thread)))
    (when work
      (assert thread)
      (assert (parallelism-piece-thread-array work))

; Record that the current thread is the one assigned to do this piece of work:

      (setf (aref (parallelism-piece-thread-array work)
                  (parallelism-piece-array-index work))
            thread))
    work))

(defun consume-work-on-work-queue-when-there ()

; This function is an infinite loop.  However, the thread running it can be
; waiting on a condition variable and will expire if it waits too long.

; Each iteration through the main loop will start by trying to grab a piece of
; work to process.  When it succeeds, then it will process that piece of work
; and wait again on a condition variable before starting the next iteration.
; But ideally, if it has to wait too long for a piece of work to grab then we
; return from this function (with expiration of the current thread); see below.

  (catch :worker-thread-no-longer-needed
    (let ((*throwable-worker-thread* t)

; If #+hons is set, we must bind *default-hs* to NIL so that each thread will
; get its own hons space whenever it uses honsing code.  We could alternately
; call (hl-hspace-init) here, but using NIL allows us to avoid the overhead of
; initializing a hons space unless honsing is used in this thread.  See also
; the notes in hons-raw.lisp.

           #+hons
           (*default-hs* nil))
      #+hons
      (declare (special *default-hs*)) ; special declared in hons-raw.lisp
      (loop ; "forever" - really until :worker-thread-no-longer-needed thrown

; Wait until there are both a piece of work and an idle core.  In CCL, if
; the thread waits too long, it throws to the catch above and returns from this
; function.

       (loop while (not (and *work-queue*
                             (< 0 (atomically-modifiable-counter-read
                                   *idle-core-count*))))

; We can't grab work yet, so we wait until somebody signals us to try again, by
; returning a non-nil value to the call of not, just below.  If however nobody
; signals us then ideally (and in CCL but not SBCL) a timeout occurs that
; returns nil to this call of not, so we give up with a throw.

             do (when (not (wait-on-semaphore
                            *check-work-and-core-availability* :timeout 15))
                  (throw :worker-thread-no-longer-needed nil)))

; Now very likely there are both a piece of work and an idle core to process
; it.  But a race condition allows either of these to disappear before we can
; claim a piece of work and a CPU core, which explains the use of `when'
; below.

       (unwind-protect-disable-interrupts-during-cleanup
        (when (<= 0  ; allocate CPU core

; We will do a corresponding increment of *idle-core-count* in the cleanup form
; of this unwind-protect.  Note that the current thread cannot be interrupted
; (except by direct user intervention, for which we may provide only minimal
; protection) until the call of pop-work-and-set-thread below (see long comment
; above that call), because no other thread has a pointer to this one until
; that time.

                  (atomic-decf *idle-core-count*))
          (catch :result-no-longer-needed
            (let ((work nil))
              (unwind-protect-disable-interrupts-during-cleanup
               (progn
                 (without-interrupts
                  (setq work

; The following call has the side effect of putting the current thread into a
; thread array, such that this presence allows the current thread to be
; interrupted by another (via interrupt-thread, in throw-threads-in-array).  So
; until this point, the current thread will not be told to do a throw.

; We rely on the following claim: If any state has been changed by this call of
; pop-work-and-set-thread, then that call completes and work is set to a
; non-nil value.  This claim guarantees that if any state has been changed,
; then the cleanup form just below will be executed and will clean up properly.
; For example, we would have a problem if pop-work-and-set-thread were
; interrupted after the decrement of *idle-thread-count*, but before work is
; set, since then the matching increment in the cleanup form below would be
; skipped.  For another example, if we complete the call of
; pop-work-and-set-thread but not the enclosing setq for work, then we miss the
; semaphore signaling in the cleanup form below.

                        (pop-work-and-set-thread))
                  (when work (atomic-decf *idle-thread-count*)))
                 (when work

; The consumer now has a core (see the <= test above) and a piece of work.

                   (eval-and-save-result work)

                   (let* ((thread-array (parallelism-piece-thread-array work))
                          (result-array (parallelism-piece-result-array work))
                          (array-index (parallelism-piece-array-index work))
                          (throw-siblings-when-function
                           (parallelism-piece-throw-siblings-when-function work)))
                     (setf (aref thread-array array-index) nil)

; The nil setting just above guarantees that the current thread doesn't
; interrupt itself by way of the early termination function.

                     (when throw-siblings-when-function
                       (funcall throw-siblings-when-function
                                (aref result-array array-index))))))

               (when work ; process this cleanup form if we acquired work
                 (let* ((semaphore-to-signal-as-last-act
                         (parallelism-piece-semaphore-to-signal-as-last-act
                          work))
                        (thread-array (parallelism-piece-thread-array work))
                        (array-index (parallelism-piece-array-index work)))

; We don't use a thread-safe increment because we don't care if it's off by a
; few.  The variable is just used for debugging.

                   (incf *total-parallelism-piece-historical-count*)
                   (setf (aref thread-array array-index) nil)

; Above we argued that if *idle-thread-count* is decremented, then work is set
; and hence we get to this point so that we can do the corresponding
; increment.  In the other direction, if we get here, then how do we know that
; *idle-thread-count* was decremented?  We know because if we get here, then
; work is non-nil and hence pop-work-and-set-thread must have completed.

                   (atomic-incf *idle-thread-count*)

; Each of the following two decrements undoes the corresponding increment done
; when the piece of work was first created and queued.

                   (atomic-decf *total-work-count*)
                   (atomic-decf *unassigned-and-active-work-count*)
                   (assert (semaphorep semaphore-to-signal-as-last-act))
                   (signal-semaphore semaphore-to-signal-as-last-act)))))
            ) ; end catch :result-no-longer-needed
          ) ; end when CPU core allocation

        (atomic-incf *idle-core-count*)
        (signal-semaphore *check-work-and-core-availability*)
        (signal-semaphore *check-core-availability-for-resuming*))))

    ) ; end catch :worker-thread-no-longer-needed

; The current thread is about to expire because all it was given to do was to
; run this function.

  (atomic-decf *idle-thread-count*))

(defun spawn-worker-threads-if-needed ()

; This function must be called with interrupts disabled.  Otherwise it is
; possible for the *idle-thread-count* to be incremented even though no new
; worker thread is spawned.

  (loop while (< (atomically-modifiable-counter-read *idle-thread-count*)
                 *max-idle-thread-count*)

; Note that the above test could be true, yet *idle-thread-count* could be
; incremented before we get to the lock just below.  But we want as little
; bottleneck as possible for scaling later, and the practical worst consequence is
; that we spawn extra threads here.

; Another possibility is that we spawn too few threads here, because the final
; decrement of *idle-thread-count* in consume-work-on-work-queue-when-there
; has not occurred even though a worker thread has decided to expire.  If this
; occurs, then we may not have the expected allotment of idle threads for
; awhile, but we expect the other idle threads (if any) and the active threads
; to suffice.  Eventually a new parallelism primitive call will invoke this
; function again, at a time when the about-to-expire threads have already
; updated *idle-thread-count*, which will allow this function to create the
; expected number of threads.  The chance of any of this kind of issue arising
; is probably extremely small.

; NOTE: Consider coming up with a design that's easier to understand.

    do
    (progn (atomic-incf *idle-thread-count*)
           ;(format t "param parent thread ~a: ~s~%" (current-thread) acl2::*param*)
           (run-thread
            "Worker thread"
            'consume-work-on-work-queue-when-there))))

;---------------------------------------------------------------------
; Section:  Work Producer Code

; We develop functions that create work, to be later processed by threads.  Our
; main concern is to keep the work queue sufficiently populated so as to keep
; CPU cores busy, while limiting the total amount of work so that the number of
; threads necessary to evaluate that work does not exceed the number of
; threads that the underlying Lisp supports creating.  (See also comments in
; default-total-parallelism-work-limit.)

(defun add-work-list-to-queue (work-list)

; Call this function inside without-interrupts, in order to maintain the
; invariant that when this function exits, the counts are accurate.

; WARNING!  This function destructively modifies *work-queue*.

  (let ((work-list-length (length work-list)))
    (with-lock *work-queue-lock*

; In naive performance tests using a parallel version of Fibonacci, we found
; that (pfib 45) took about 19.35 seconds with (nconc *work-queue* work-list),
; as opposed to 19.7 seconds when we reversed the argument order.  We have
; other evidence that suggests switching the argument order.  But we follow
; Halstead's 1989 paper "New Ideas in Parallel Lisp: Language Design,
; Implementation, and Programming Tools", by doing the oldest work first.

               (setf *work-queue*
                     (nconc *work-queue* work-list)))
    (atomic-incf-multiple *total-work-count* work-list-length)
    (atomic-incf-multiple *unassigned-and-active-work-count* work-list-length)
    (dotimes (i work-list-length)
      (signal-semaphore *check-work-and-core-availability*))))

(defun combine-array-results-into-list (result-array current-position acc)
  (if (< current-position 0)
      acc
    (combine-array-results-into-list
     result-array
     (1- current-position)
     (cons (cdr ; entry is a cons whose cdr is the result
            (aref result-array current-position))
           acc))))

(defun remove-thread-array-from-work-queue-rec
  (work-queue thread-array array-positions-left)

; The function calling remove-thread-array-from-work-queue must hold the lock
; *work-queue-lock*.

; This function must be called with interrupts disabled.

  (cond ((eql array-positions-left 0)
         work-queue)
        ((atom work-queue)
         nil)
        ((eq thread-array (parallelism-piece-thread-array (car work-queue)))
         (progn
           (atomic-decf *total-work-count*)
           (atomic-decf *unassigned-and-active-work-count*)

; we must signal the parent

           (assert
            (semaphorep (parallelism-piece-semaphore-to-signal-as-last-act
                         (car work-queue))))
           (signal-semaphore
            (parallelism-piece-semaphore-to-signal-as-last-act
             (car work-queue)))
           (remove-thread-array-from-work-queue-rec (cdr work-queue)
                                                    thread-array
                                                    (1- array-positions-left))))
        (t (cons (car work-queue)
                 (remove-thread-array-from-work-queue-rec
                  (cdr work-queue)
                  thread-array
                  (1- array-positions-left))))))

(defun remove-thread-array-from-work-queue (thread-array)
  (without-interrupts
   (with-lock *work-queue-lock*
              (setf *work-queue*
                    (remove-thread-array-from-work-queue-rec
                     *work-queue*
                     thread-array
                     (length thread-array))))))

(defun terminate-siblings (thread-array)

; This function supports early termination by eliminating further computation
; by siblings.  Siblings not yet assigned a thread are removed from the work
; queue.  Siblings that are already active are interrupted to throw with tag
; :result-no-longer-needed.  The order of these two operations is important: if
; we do them in the other order, then we could miss a sibling that is assigned
; a thread (and removed from the work queue) just inbetween the two
; operations.

  (remove-thread-array-from-work-queue thread-array)
  (throw-threads-in-array thread-array (1- (length thread-array))))

(defun generate-work-list-from-closure-list-rec
  (thread-array result-array children-done-semaphore closure-list current-position
                &optional throw-siblings-when-function)
  (if (atom closure-list)
      (assert (equal current-position (length thread-array))) ; returns nil
    (cons (make-parallelism-piece
           :thread-array thread-array
           :result-array result-array
           :array-index current-position
           :semaphore-to-signal-as-last-act children-done-semaphore
           :closure (car closure-list)
           :throw-siblings-when-function throw-siblings-when-function)
          (generate-work-list-from-closure-list-rec
           thread-array
           result-array
           children-done-semaphore
           (cdr closure-list)
           (1+ current-position)
           throw-siblings-when-function))))

(defun generate-work-list-from-closure-list
  (closure-list &optional terminate-early-function)

; Given a list of closures, we need to generate a list of work data structures
; that are in a format ready for the work queue.  Via mv, we also return the
; pointers to the thread, result, and semaphore arrays.

  (let* ((closure-count (length closure-list))
         (thread-array (make-array closure-count :initial-element nil))
         (result-array (make-array closure-count :initial-element nil))
         (children-done-semaphore (make-semaphore)))
    (progn ; warning: avoid prog2 as we need to return multiple value
      (assert (semaphorep children-done-semaphore))
      (mv (generate-work-list-from-closure-list-rec
           thread-array
           result-array
           children-done-semaphore
           closure-list
           0
           (if terminate-early-function
               (lambda (x) ; x is (t . result)
                 (when (funcall terminate-early-function (cdr x))
                   (terminate-siblings thread-array)))
             nil))
          thread-array
          result-array
          children-done-semaphore))))

(defun pargs-parallelism-buffer-has-space-available ()
  (< (atomically-modifiable-counter-read *unassigned-and-active-work-count*)
     *unassigned-and-active-work-count-limit*))

(defun not-too-many-pieces-of-parallelism-work-already-in-existence ()

; Parallelism no-fix: we could fix the plet, pargs, pand, and por parallel
; execution system to cause an error when this limit is exceeded.  However,
; since there is no notion of ":full" parallel execution (like in the ACL2
; waterfall) for these primitives (because these primitives only parallelize
; when resources are available), such an error would be meaningless.

  (< (atomically-modifiable-counter-read *total-work-count*)
     (f-get-global 'total-parallelism-work-limit *the-live-state*)))

(defun parallelism-resources-available ()

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
       (pargs-parallelism-buffer-has-space-available)
       (not-too-many-pieces-of-parallelism-work-already-in-existence)))

(defun throw-threads-in-array (thread-array current-position)

; Call this function to terminate computation for every thread in the given
; thread-array from position current-position down to position 0.  We expect
; that thread-array was either created by the current thread's parent or was
; created by the current thread (for its children).

; We require that the current thread not be in thread-array.  This requirement
; prevents the current thread from interrupting itself, which could conceivably
; abort remaining recursive calls of this function, or cause a hang in some
; Lisps since we may be operating with interrupts disabled (for example, inside
; the cleanup form of an unwind-protect in CCL (OpenMCL 1.1pre or later)).

  (assert thread-array)
  (when (<= 0 current-position)
    (let ((current-thread (aref thread-array current-position)))
      (when current-thread
        (interrupt-thread current-thread

; The delayed evaluation of (aref thread-array...) below is crucial to keep a
; thread from throwing :result-no-longer-needed outside of the catch for that tag.
; Consume-work-on-work-queue-when-there will set the (aref thread-array...)
; to nil when the thread should not be thrown.

                          (lambda ()
                            (when (aref thread-array current-position)
                              (throw :result-no-longer-needed nil))))))
    (throw-threads-in-array thread-array (1- current-position))))

(defun decrement-children-left (children-left-ptr semaphore-notification-obj)

; This function should be called with interrupts disabled.

   (when (semaphore-notification-status semaphore-notification-obj)
     (decf (aref children-left-ptr 0))
     (clear-semaphore-notification-status semaphore-notification-obj)))

(defun wait-for-children-to-finish
  (semaphore children-left-ptr semaphore-notification-obj)

; This function is called both in the normal case and in the early-termination
; case.

  (assert children-left-ptr)
  (when (<= 1 (aref children-left-ptr 0))
    (assert (not (semaphore-notification-status semaphore-notification-obj)))
    (unwind-protect-disable-interrupts-during-cleanup
     (wait-on-semaphore semaphore
                        :notification semaphore-notification-obj)
     (decrement-children-left children-left-ptr
                              semaphore-notification-obj))
    (wait-for-children-to-finish semaphore
                                 children-left-ptr
                                 semaphore-notification-obj)))

(defun wait-for-resumptive-parallelism-resources ()

; A thread resuming execution after its children finish has a higher priority
; than a thread just beginning execution.  As such, resuming threads are
; allowed to "borrow" up to *core-count* CPU cores.  That is implemented by
; waiting until *idle-core-count* is greater than the negation of the
; *core-count*.  This is different from a thread just beginning execution,
; which waits for *idle-core-count* to be greater than 0.

  (loop while (<= (atomically-modifiable-counter-read *idle-core-count*)
                  (- *core-count*))

; So, *idle-core-count* is running a deficit that is at least the number of
; cores: there are already *core-count* additional active threads beyond the
; normal limit of *core-count*.

          do (wait-on-semaphore *check-core-availability-for-resuming*))
  (atomic-incf *unassigned-and-active-work-count*)
  (atomic-decf *idle-core-count*))

(defun early-terminate-children-and-rewait
  (children-done-semaphore children-left-ptr semaphore-notification-obj
                           thread-array)

; This function performs three kinds of actions.

; A. It signals children-done-semaphore once for each child that is unassigned
; (i.e. still on the work queue) and removes that child from the work queue.

; B. It interrupts each assigned child's thread with a throw that terminates
; processing of its work.  Note that we must do Step B after Step A: otherwise
; threads might grab work after Step B but before Step A, resulting in child
; work that is no longer available to terminate unless we call this function
; again.

; C. The above throw from Step B eventually causes the interrupted threads to
; signal children-done-semaphore.  The current thread waits for those remaining
; signals.

  (when (< 0 (aref children-left-ptr 0))
    (remove-thread-array-from-work-queue ; A

; Signal children-done-semaphore, which is in each piece of work in
; closure-list.

     thread-array)
    (throw-threads-in-array thread-array ; B
                            (1- (length thread-array)))
    (wait-for-children-to-finish         ; C
     children-done-semaphore
     children-left-ptr
     semaphore-notification-obj)))

(defun prepare-to-wait-for-children ()

; This function should be executed with interrupts disabled, after all child
; work is added to the work queue but before the current thread waits on such
; work to finish.

; First, since we are about to enter the pending state, we must free CPU core
; resources and notify other threads.

  (atomic-incf *idle-core-count*)
  (signal-semaphore *check-work-and-core-availability*)
  (signal-semaphore *check-core-availability-for-resuming*)

; Second, record that we are no longer active.  (Note: We could avoid the
; following form (thus saving a lock) by incrementing
; *unassigned-and-active-work-count* by one less in add-work-list-to-queue.)

  (atomic-decf *unassigned-and-active-work-count*))

(defun parallelize-closure-list (closure-list &optional terminate-early-function)

; Given a list of closures, we:

; 1. Create a list of pieces of work (see defstruct parallelism-piece).

; 2. If there aren't enough idle worker threads, we spawn a reasonably
; sufficient number of new worker threads, so that CPU cores are kept busy but
; without the needless overhead of useless threads.  Note that when a thread
; isn't already assigned work, it is waiting for notification to look for work
; to do.

; 3. Add the work to the work queue, which notifies the worker threads of the
; additional work.

; 4. Free parallelism resources (specifically, a CPU core), since we are about
; to become idle as we wait children to finish.  Issue the proper notifications
; (via condition variables) so that other threads are aware of the freed
; resources.

; 5. Wait for the children to finish.  In the event of receiving an early
; termination from our parent (a.k.a. the grandparent of our children) or our
; sibling (a.k.a. the uncle of our children), we signal our children to
; terminate early, and we wait again.

; Note that if the current thread's children decide the remaining child results
; are irrelevant, that the current thread will never know it.  The children
; will terminate early amongst themselves without any parent intervention.

; 6. Resume when resources become available, reclaiming parallelism resources
; (see wait-for-resumptive-parallelism-resources).

; 7. Return the result.

; It's silly to parallelize just 1 (or no!) thing.  The definitions of pargs,
; plet, pand, and por should prevent this assertion from failing, but we have
; it here as a check that this is true.

  (assert (and (consp closure-list) (cdr closure-list)))

  (let ((work-list-setup-p nil)
        (semaphore-notification-obj (make-semaphore-notification))
        (children-left-ptr (make-array 1 :initial-element (length closure-list))))

; 1. Create a list of pieces of work.
    (mv-let
     (work-list thread-array result-array children-done-semaphore)
     (generate-work-list-from-closure-list closure-list
                                           terminate-early-function)
     (assert (semaphorep children-done-semaphore))
     (unwind-protect-disable-interrupts-during-cleanup
      (progn
        (without-interrupts

; 2. Spawn worker threads so that CPU cores are kept busy.
         (spawn-worker-threads-if-needed)

; 3. Add the work to the work queue.
         (setq work-list-setup-p (progn (add-work-list-to-queue work-list) t))

; 4. Free parallelism resources.
         (prepare-to-wait-for-children))

; 5a. Wait for children to finish.  But note that we may be interrupted by our
; sibling or our parent before this wait is completed.

; Now that the two operations under the above without-interrupts are complete,
; it is once again OK to be interrupted with a function that throws to the tag
; :results-no-longer-needed.  Note that wait-for-children-to-finish is called
; again in the cleanup form below, so we don't have to worry about dangling
; child threads even if we don't complete evaluation of the following form.

        (wait-for-children-to-finish children-done-semaphore
                                     children-left-ptr
                                     semaphore-notification-obj))

; We are entering the cleanup form, which we always need to run (in particular,
; so that we can resume and return a result).  But why must we run without
; interrupts?  Suppose for example we have been interrupted (to do a throw) by
; the terminate-early-function of one of our siblings or by our parent.  Then
; we must wait for all child pieces of work to terminate (see
; early-terminate-children-and-rewait) before we return.  And this waiting must
; be non-abortable; otherwise, for example, we could be left (after Control-c
; and an abort) with orphaned child threads.

      (progn
        (when work-list-setup-p ; children were added to *work-queue*

; If we were thrown by a sibling or parent, it's possible that our children
; didn't finish.  We now throw our children and wait for them.

; 5b. Complete processing of our children in case we were interrupted when we
; were waiting the first time.
          (early-terminate-children-and-rewait children-done-semaphore
                                               children-left-ptr
                                               semaphore-notification-obj
                                               thread-array)

; AS OF *HERE*, ALL OF THIS PARENT'S CHILD WORK IS "DONE"

; 6. Resume when resources become available.
          (wait-for-resumptive-parallelism-resources)
          (assert (eq (aref children-left-ptr 0) 0)))))

; 7. Return the result.
     (combine-array-results-into-list
      result-array
      (1- (length result-array))
      nil))))

(defun parallelize-fn (parent-fun-name arg-closures &optional terminate-early-function)

; Parallelize-fn Booleanizes the results from pand/por.

; It's inefficient to parallelize just one (or no!) computation.  The
; definitions of pargs, plet, pand, and por should prevent this assertion from
; failing, but we have it here as a check that this is true.

  (assert (cdr arg-closures))
  (let ((parallelize-closures-res
         (parallelize-closure-list arg-closures terminate-early-function)))
    (if (or (equal parent-fun-name 'and-list)
            (equal parent-fun-name 'or-list))
        (funcall parent-fun-name parallelize-closures-res)
      (apply parent-fun-name parallelize-closures-res))))

(defmacro closure-for-expression (x)

; This macro expands to an expression that evaluates to a closure.

  (make-closure-expr-with-acl2-bindings x))

(defmacro closure-list-for-expression-list (x)
  (if (atom x)
      nil
    `(cons (closure-for-expression ,(car x))
           (closure-list-for-expression-list ,(cdr x)))))

;---------------------------------------------------------------------
; Section:  Parallelism Primitives

(defun parallelism-condition (gran-form-exists gran-form)
  (if gran-form-exists
      `(and (parallelism-resources-available)

; We check availability of resources before checking the granularity form,
; since the latter can be arbitrarily expensive.

            ,gran-form)
    '(parallelism-resources-available)))

(defmacro pargs (&rest forms)

; This is the raw lisp version for threaded Lisps.

  (mv-let
   (erp msg gran-form-exists gran-form remainder-forms)
   (check-and-parse-for-granularity-form forms)
   (declare (ignore msg))
   (assert (not erp))
   (let ((function-call (car remainder-forms)))
     (if (null (cddr function-call)) ; whether there are two or more arguments
         function-call
       (list 'if
             (parallelism-condition gran-form-exists gran-form)
             (list 'parallelize-fn
                   (list 'quote (car function-call))
                   (list 'closure-list-for-expression-list
                         (cdr function-call)))
             function-call)))))

(defun plet-doublets (bindings bsym n)
  (cond ((endp bindings)
         nil)
        (t
         (cons (list (caar bindings) (list 'nth n bsym))
               (plet-doublets (cdr bindings) bsym (1+ n))))))

(defun make-closures (bindings)

; We return a list of forms (function (lambda () <expr>)), each of which
; evaluates to a closure, as <expr> ranges over the expression components of
; the given plet bindings.  Note that this function is only called on the
; bindings of a plet expression that has passed translate -- so we know that
; bindings has the proper shape.

  (if (endp bindings)
      nil
    (cons `(function (lambda () ,(cadar bindings)))
          (make-closures (cdr bindings)))))

(defun identity-list (&rest rst) rst)

(defun make-list-until-non-declare (remaining-list acc)
  (if (not (caar-is-declarep remaining-list))
      (mv (reverse acc) remaining-list)
    (make-list-until-non-declare (cdr remaining-list)
                                 (cons (car remaining-list) acc))))

(defun parse-additional-declare-forms-for-let (x)

; X is a list of forms from a well-formed plet, with the plet and optional
; granularity form removed.  It thus starts with bindings and is followed by
; any finite number of valid declare forms, and finally a body.

  (mv-let (declare-forms body)
          (make-list-until-non-declare (cdr x) nil)
          (mv (car x) declare-forms body)))

(defmacro plet (&rest forms)

; This is the raw Lisp version for threaded Lisps.

  (mv-let
   (erp msg gran-form-exists gran-form remainder-forms)
   (check-and-parse-for-granularity-form forms)
   (declare (ignore msg))
   (assert (not erp))
   (mv-let
    (bindings declare-forms body)
    (parse-additional-declare-forms-for-let remainder-forms)
    (cond ((null (cdr bindings)) ; at most one binding
           `(let ,bindings ,@declare-forms ,@body))
          (t (list 'if
                   (parallelism-condition gran-form-exists gran-form)
                   (let ((bsym (acl2-gentemp "plet")))
                     `(let ((,bsym (parallelize-fn 'identity-list
                                                   (list ,@(make-closures bindings)))))
                        (let ,(plet-doublets bindings bsym 0)
                          ,@declare-forms
                          ,@body)))
                   `(let ,bindings ,@declare-forms ,@body)))))))

(defmacro pand (&rest forms)

; This is the raw Lisp version for threaded Lisps.

  (mv-let
   (erp msg gran-form-exists gran-form remainder-forms)
   (check-and-parse-for-granularity-form forms)
   (declare (ignore msg))
   (assert (not erp))
   (if (null (cdr remainder-forms)) ; whether pand has only one argument
       (list 'if (car remainder-forms) t nil)
     (let ((and-early-termination-function
            '(lambda (x) (null x))))
       (list 'if
             (parallelism-condition gran-form-exists gran-form)
             (list 'parallelize-fn ''and-list
                   (list 'closure-list-for-expression-list
                         remainder-forms)
                   and-early-termination-function)
             (list 'if (cons 'and remainder-forms) t nil))))))

(defmacro por (&rest forms)

; This is the raw Lisp version for threaded Lisps.

  (mv-let
   (erp msg gran-form-exists gran-form remainder-forms)
   (check-and-parse-for-granularity-form forms)
   (declare (ignore msg))
   (assert (not erp))

   (if (null (cdr remainder-forms)) ; whether por has one argument
       (list 'if (car remainder-forms) t nil)
     (let ((or-early-termination-function
            '(lambda (x) x)))
       (list 'if
             (parallelism-condition gran-form-exists gran-form)
             (list 'parallelize-fn ''or-list
                   (list 'closure-list-for-expression-list
                         remainder-forms)
                   or-early-termination-function)
             (list 'if (cons 'or remainder-forms) t nil))))))

(defun signal-semaphores (sems)
  (cond ((endp sems)
         nil)
        (t (signal-semaphore (car sems))
           (signal-semaphores (cdr sems)))))

(defmacro spec-mv-let (&whole spec-mv-let-form outer-vars computation body)

; Warning: Keep this in sync with the logical definition of spec-mv-let.

; It is tempting to strip out the error checking code below, under the
; assumption that ACL2 will always do this in the logical definition.  However,
; David Rager has expressed an interest in perhaps making a standalone library
; to support parallel execution, so we leave the checks in place here.

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

; We lay down code that differs a bit from the logical code (which treats
; spec-mv-let essentially as mv?-let), in order to support speculative
; execution, and possible aborting, of the (speculative) computation.

       `(let ((the-very-obscure-feature (future ,computation)))
          (,inner-let
           ,inner-vars
           ,inner-body
           (cond
            (,test
             (mv?-let ,outer-vars
                      (future-read the-very-obscure-feature)
                      ,true-branch))
            (t (future-abort the-very-obscure-feature)
               ,false-branch)))))))
    (& (er hard! 'spec-mv-let
           "Illegal form, ~x0.  See :doc spec-mv-let."
           spec-mv-let-form))))

(defun number-of-active-threads-aux (threads acc)
  #-ccl
  (declare (ignore threads acc))
  #-ccl
  0
  #+ccl
  (cond ((atom threads)
         acc)
        ((equal (ccl:process-whostate (car threads)) "Active")
         (number-of-active-threads-aux (cdr threads) (1+ acc)))
        (t (number-of-active-threads-aux (cdr threads) acc))))

(defun number-of-active-threads ()
  (number-of-active-threads-aux (all-threads) 0))

(defun number-of-threads-waiting-on-a-child-aux (threads acc)
  #-ccl
  (declare (ignore threads acc))
  #-ccl
  0
  #+ccl
  (cond ((atom threads)
         acc)
        ((equal (ccl:process-whostate (car threads)) "semaphore wait")
         (number-of-threads-waiting-on-a-child-aux (cdr threads) (1+ acc)))
        (t (number-of-threads-waiting-on-a-child-aux (cdr threads) acc))))

(defun number-of-threads-waiting-on-a-child ()
  (number-of-threads-waiting-on-a-child-aux (all-threads) 0))

(defun future-queue-length ()

; At one point this was simply the difference between the *last-slot-saved* and
; the *last-slot-taken*.  However, since we grab work from the work queue
; before actually processing it with an idle cpu core, it is also necessary to
; include the number of threads that are waiting for a starting core.

  (+ (- *last-slot-saved* *last-slot-taken*)
     *threads-waiting-for-starting-core*

; I intentionally ignore the threads that have incremented *last-slot-taken*
; but not yet entered claim-starting-core.  I could come up with some mechanism
; to track these, but there should be an insignificant number of them (less
; than the total number of hardware threads, as of 2012-07), and it's not worth
; it right now.

     ))

(defun total-number-of-threads ()
  (length (all-threads)))

(defvar *refresh-rate-indicator* 0)

(defmacro value-of-symbol (var)
  (when (not (or (fboundp var)
                 (symbolp var)))
    (error "value-of-symbol requires a symbol or function name as its argument"))
  (cond ((constantp var)
         `(format nil " Constant ~s is ~s~% " ,(symbol-name var) ,var))
        ((fboundp var)
         `(format nil " Stat     ~s is ~s~% " ,(symbol-name var) (,var)))
        ((boundp-global var *the-live-state*)
         `(format nil " Stat     ~s is ~s~% " ,(symbol-name var)
                  ,(f-get-global var *the-live-state*)))
        (t
         `(format nil " Variable ~s is ~s~% " ,(symbol-name var) ,var))))

(defun acl2p-sum-list1 (lst acc)
  (cond ((endp lst)
         acc)
        (t (acl2p-sum-list1 (cdr lst)
                            (+ (car lst) acc)))))

(defun acl2p-sum-list (lst)

; An arcane name is chosen so that we don't conflict with other implementations
; of "sum-list".

  (acl2p-sum-list1 lst 0))

(defun average-future-queue-size ()
  (* 1.0 (/ (acl2p-sum-list *future-queue-length-history*)
            (length *future-queue-length-history*))))

(defun print-interesting-parallelism-variables-str ()
  (incf *refresh-rate-indicator*)
  (setf *future-queue-length-history*

; Note that this setf isn't thread safe, but if we lose one entry in the
; history, we don't really care -- it's just a debugging tool anyway.

        (cons (future-queue-length)
              *future-queue-length-history*))

  (concatenate
   'string
   (format nil "  Printing stats related to executing proofs in parallel.~% ")
   (value-of-symbol *idle-future-core-count*)
   (value-of-symbol *idle-future-resumptive-core-count*)
   (value-of-symbol *idle-future-thread-count*)
   (value-of-symbol *threads-waiting-for-starting-core*)
   (value-of-symbol number-of-idle-threads-and-threads-waiting-for-a-starting-core)
   (value-of-symbol total-number-of-threads)

   (format nil "~% ")

   (value-of-symbol *unassigned-and-active-future-count*)
   (value-of-symbol *unassigned-and-active-work-count-limit*)

   (value-of-symbol *total-future-count*)
   (value-of-symbol total-parallelism-work-limit)

   (format nil "~% ")
   (value-of-symbol number-of-active-threads)
   (value-of-symbol number-of-threads-waiting-on-a-child)

   (format nil "~% ")
   (value-of-symbol *last-slot-taken*)
   (value-of-symbol *last-slot-saved*)
   (value-of-symbol future-queue-length)
   (value-of-symbol average-future-queue-size)


   (format nil "~% ")
   (value-of-symbol *resource-based-parallelizations*)
   (value-of-symbol *resource-based-serializations*)

   (value-of-symbol *resource-and-timing-based-parallelizations*)
   (value-of-symbol *resource-and-timing-based-serializations*)

   (value-of-symbol *futures-resources-available-count*)
   (value-of-symbol *futures-resources-unavailable-count*)

   (format nil "~% ")
   (format nil " Printing stats related to aborting futures.~% ")
   (value-of-symbol *aborted-futures-total*)
   (value-of-symbol *aborted-futures-via-throw*)
   (value-of-symbol *aborted-futures-via-flag*)
   (value-of-symbol *almost-aborted-future-count*)

   (format nil "~% ")
   (value-of-symbol *refresh-rate-indicator*)))

(defun print-interesting-parallelism-variables ()
  (format t (print-interesting-parallelism-variables-str)))
