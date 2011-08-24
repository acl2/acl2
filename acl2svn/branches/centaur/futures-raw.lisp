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

; This file is divided into the following sections.

; Section:  Single-threaded Futures
; Section:  Multi-threaded Futures
; Section:  Futures Interface

(in-package "ACL2")

; Parallelism wart: create an "Essay on Futures" that should act as a guide to
; this file.

; Parallelism wart: cleanup this file by removing blank lines that are
; inconsistent with the ACL2 style guide (and other improvements that strike 
; the author's fancy).

;---------------------------------------------------------------------
; Section:  Single-threaded Futures

(defstruct st-future
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
  (setf (st-future-closure st-future) nil)
  (setf (st-future-aborted st-future) t)
  st-future)

;---------------------------------------------------------------------
; Section:  Multi-threaded Futures

; Notes on the specification:

; (1) Producer is responsible for *always* placing the closure on the queue
;
; (2) Consumer is responsible for *always* removing the closure from the queue,
; regardless of whether there was early termination.  Upon early termination,
; it is optional as to whether the early terminated future's barrier is
; signaled.  For now, the barrier should not be signaled.
;
; (3) Only the producer of a particular future can abort that future.  The
; producer does so by first setting the abort flag of the future and then
; throwing any consumer that could be evaluating that future.
; 
; (4) When a consumer evaluates a future, it first sets a pointer to itself in
; thread array and secondly checks the future's abort flag.
;
; (5) The combination of (3) and (4) results in the following six potential
; race scenarios (these conditions could be turned into a dissertation
; graphic):
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
; futures, it only impacts the implementation underlying spec-mv-let.  Plet,
; pargs, pand, and por are unaffected.

(push :skip-resource-availability-test *features*)

; Parallelism wart: I leave the pushing of feature :studless-waterfall as
; reference for the dead code (which I should delete) that references this
; feature.

; (push :studless-waterfall *features*)


(defstruct atomic-notification
  (value nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; Closure evaluators
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We continue our array-based approach for storing and grabbing pieces of
; parallelism work.  This time, however, we do things a little differently.
; Instead of saving "pieces of parallelism work" to a queue, we only store
; closures.  I'm not sure how this will pan out WRT early termination.  I might
; end up making it more than just closures.

; There are some optimizations we can make if we assume that only one thread
; will be reading the future's value.  E.g., we can remove the wait-count from
; barrier, because there will always be only one thread waiting.

(defstruct barrier
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

;(load "/u/ragerdl/r/pacl2/futures/futures-st.lisp")

(defstruct mt-future
  (index nil)
  (value nil)
  (valid (make-barrier)) ; whether the value is valid
  (closure nil)
  (aborted nil)
  (thrown-tag nil))

(define-atomically-modifiable-counter *last-slot-saved* 0)
(define-atomically-modifiable-counter *last-slot-taken* 0)

; One concern I have is that the array elements will be so close together, that
; they'll be in the same cache lines, and the CPU cores will get bogged down
; just keeping the writes to the cache "current".  The exact impact of this
; thrashing is unknown. n Followup: After further thought, I realize that this
; thrashing will be negligible when compared to the rest of the parallelism
; overhead.

(defvar *thread-array*)
(defvar *future-array*)
(defvar *future-dependencies*)

(defvar *current-thread-index* 0) ; set to 0 for the main thread
(defconstant *starting-core* 'start)
(defconstant *resumptive-core* 'resumptive)

(defvar *allocated-core* *starting-core*)
(defvar *decremented-idle-future-thread-count* nil)

(defvar *idle-future-core-count* 
  (make-atomically-modifiable-counter (1- *core-count*)))
(defvar *idle-future-resumptive-core-count* 
  (make-atomically-modifiable-counter *core-count*))
(defvar *idle-core* (make-semaphore))

(define-atomically-modifiable-counter *idle-future-thread-count* 0)

(defvar *future-added* (make-semaphore))

(defvar *idle-resumptive-core* (make-semaphore))
(defvar *threads-spawned* 0)


(define-atomically-modifiable-counter *unassigned-and-active-future-count* 0)

(define-atomically-modifiable-counter *total-future-count* 0)

(defconstant *future-array-size* 200000)

(defmacro faref (array subscript)
  `(aref ,array 
; avoid reusing slot 0, which is always reserved for the intial thread.
         (if (equal 0 ,subscript) 
             0
           (1+ (mod ,subscript (1- *future-array-size*))))))

(defun reset-future-parallelism-variables ()
  ;(sleep 30)
; We need to send-die-toall-except-initial-threads when we evaluate save-exec
; to save the ACL2 image at the end of the build process

;  (send-die-to-all-except-initial-threads)

  (setf *thread-array* 
        (make-array *future-array-size* :initial-element nil))
  (setf *future-array* 
        (make-array *future-array-size* :initial-element nil))
  (setf *future-dependencies*
        (make-array *future-array-size* :initial-element nil))

  (setf *future-added* (make-semaphore))

  (setf *idle-future-core-count*
        (make-atomically-modifiable-counter (1- *core-count*)))

  (setf *idle-future-resumptive-core-count* 
        (make-atomically-modifiable-counter *core-count*))

  (setf *idle-core* (make-semaphore))
  (setf *idle-resumptive-core* (make-semaphore))

  (dotimes (i (1- *core-count*)) (signal-semaphore *idle-core*))
  (dotimes (i (1- *core-count*)) (signal-semaphore *idle-resumptive-core*))
  
; The last slot taken and saved starts at zero, because slot zero is always
; reserved for the initial thread.

  (setf *last-slot-taken* (make-atomically-modifiable-counter 0))
  (setf *last-slot-saved* (make-atomically-modifiable-counter 0))
  (setf *threads-spawned* 0)

; If we let the threads expire naturally instead of calling the above
; send-die-to-all-except-initial-threads, then this setting is unnecessary.
  (setf *idle-future-thread-count* (make-atomically-modifiable-counter 0))
; (setf *pending-future-thread-count* (make-atomically-modifiable-counter 0))
; (setf *resumptive-future-thread-count* (make-atomically-modifiable-counter 0))

; (setf *acl2-par-arrays-lock* (make-lock))
  t ; return t
)

#-lispworks
(reset-future-parallelism-variables)

(defun reset-all-parallelism-variables ()
  (format t "Resetting parallelism and futures variables.  This may take a ~
             few seconds (often either~% 0 or 15).~%")
  (reset-parallelism-variables)
  (reset-future-parallelism-variables)
  (format t "Done resetting parallelism and futures variables.~%"))

(defun futures-resources-available ()

; This function is our attempt to guess when resources are available.  When
; this function returns true, then resources are probably available, and a
; parallelism primitive call will opt to parallelize.  We say "probably"
; because correctness does not depend on our answering exactly.  For
; performance, we prefer that this function is reasonably close to an accurate
; implementation that would use locks.  Perhaps even more important for
; performance, however, is that we avoid the cost of locks to try to remove
; bottlenecks.

; In summary, it is unneccessary to acquire a lock, because we just don't care
; if we miss a few chances to parallelize, or parallelize a few extra times.

  (and (f-get-global 'parallel-evaluation-enabled *the-live-state*)
       (< (atomically-modifiable-counter-read *unassigned-and-active-future-count*)
          *unassigned-and-active-work-count-limit*)
       (< (atomically-modifiable-counter-read *total-future-count*)
          *total-work-limit*)))

(defmacro unwind-protect-disable-interrupts-during-cleanup
  (body-form &rest cleanup-forms)

; As the name suggests, this is unwind-protect but with a guarantee that
; cleanup-form cannot be interrupted.  Note that CCL's implementation already
; disables interrupts during cleanup.

  #+ccl
  `(unwind-protect ,body-form ,@cleanup-forms)
  #+sb-thread
  `(unwind-protect ,body-form (without-interrupts ,@cleanup-forms))
  #-(or ccl sb-thread)
  `(unwind-protect ,body-form ,@cleanup-forms))

; Idea: have a queue for both the evaluation of closures and the abortion of
; futures.  Give the abortion queue higher priority.

(defun claim-starting-core ()
  (let ((notification (make-semaphore-notification)))
    (unwind-protect-disable-interrupts-during-cleanup
     (wait-on-semaphore *idle-core* :notification notification)
     (when (semaphore-notification-status notification)
       (setf *allocated-core* *starting-core*)
       (atomic-decf *idle-future-core-count*)
; Is this really the right place to do this?
       (setf *decremented-idle-future-thread-count* t)
       (atomic-decf *idle-future-thread-count*)))))

(defun claim-resumptive-core ()
  (let ((notification (make-semaphore-notification)))
    (unwind-protect-disable-interrupts-during-cleanup
     (wait-on-semaphore *idle-resumptive-core* :notification notification)
     (when (semaphore-notification-status notification)
       (setf *allocated-core* *resumptive-core*)
       (atomic-decf *idle-future-resumptive-core-count*)))))
    
(defun free-allocated-core ()
  (without-interrupts
   (cond ((equal *allocated-core* *starting-core*)
          (atomic-incf *idle-future-core-count*)
          (signal-semaphore *idle-core*)
          (setf *allocated-core* nil))
         
         ((equal *allocated-core* *resumptive-core*)
          (atomic-incf *idle-future-resumptive-core-count*)
          (signal-semaphore *idle-resumptive-core*)
          (setf *allocated-core* nil))
; Under early termination, the early terminated thread doesn't acquire a
; resumptive core.
         (t nil))
   t))

(defun early-terminate-children (index)

; With the current design, it is assumed that only one thread will be issuing
; early termination orders -- the thread that generated the future stored at
; the given index.  It's possible to change the design, but it would require
; more locking.

; Due to this more specific design, the function is named
; "early-terminate-children.  A more general function could be named
; "early-terminate-relatives".

  (abort-future-indexes (faref *future-dependencies* index))
  (setf (faref *future-dependencies* index) nil)
)

(defvar *aborted-futures-via-flag* 0)
(defvar *aborted-futures-total* 0)

(defvar *futures-resources-available-count* 0)
(defvar *futures-resources-unavailable-count* 0)

(defun set-thread-check-for-abort-and-funcall (future)
  (let* ((index (mt-future-index future))
         (closure (mt-future-closure future))
; Bind thread-local versions of special variables here.
         (*allocated-core* nil)
         (*current-thread-index* index)
         (*decremented-idle-future-thread-count* nil)
         (early-terminated t))
    (unwind-protect-disable-interrupts-during-cleanup
     (progn
       (claim-starting-core)
       (setf (faref *thread-array* index) (current-thread))
       ;; (setf *current-thread-index* index) ; redundant
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

; Used for checking whether the thread receiving a :result-no-longer-needed
; throw would have any meaning.  So, if *throwable-future-worker-thread* is
; nil, then there's no point in throwing said tag, because there wouldn't be
; any work to abort.
;
; *Throwable-future-worker-thread* is unrelated to tag
; *:worker-thread-no-longer-needed.

; Parallelism wart: pick a name that makes it more obvious that this variable
; is unrelated to variable *throwable-worker-thread*.

 nil)

(defun wait-for-a-closure ()
  (loop while (>= (atomically-modifiable-counter-read *last-slot-taken*)
                  (atomically-modifiable-counter-read *last-slot-saved*))
        do
        (when (not (wait-on-semaphore *future-added* :timeout 15))
          (throw :worker-thread-no-longer-needed nil))))

(defvar *busy-wait-var* 0)
(defvar *current-waiting-thread* nil)
(defvar *fresh-waiting-threads* 0)

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
; element in tags, the cleanup form for 'x-tag should also be the third form in
; cleanups.

; This macro does not support throwing multiple-values as a throw's return
; value.

; Here is an example of what we expect throw-catch-let to automatically do for
; us.  We let throw-catch-let worry about the details.  Some examples of such
; details are: (1) whether we have the right order for checking one-thrown,
; one-or-two-thrown, et al. (2) whether our catches are in the right order, (3)
; whether the value returned by the catches is the right value (which is why we
; have to use prog1).  Note that this form is missing some of the detail (e.g.,
; the aforementioned prog1).

;; (let ((one-thrown 't)
;;       (one-or-two-thrown 't)
;;       (one-or-two-or-three-thrown 't))
;;   (catch 'one
;;     (catch 'two
;;       (catch 'three
;;         (arbitrary-code-here)
;;         ;; (if X
;;         ;;     (throw 'one)
;;         ;;   (if Y
;;         ;;       (throw 'two)
;;         ;;     (if Z
;;         ;;         (throw 'three)
;;         ;;       nil)))
;;         (setq one-or-two-or-three-thrown nil))
;;       (setq one-or-two-thrown nil))
;;     (setq one-thrown nil))
;;   (cond
;;    (one-thrown (handle-one))
;;    (one-or-two-thrown (handle-two))
;;    (one-or-two-or-three-thrown (handle-three))))

; Here is an example use of throw-catch-let.
       
;; (throw-catch-let
;;  (x y)
;;  (cond ((equal *flg* 3) (throw 'x 10))
;;        ((equal *flg* 4) (throw 'y 11))
;;        (t 7))  
;;  ((setq *x-thrown* t)
;;   (setq *y-thrown* t)))

; While Rager wrote this macro, Nathan Wetzler has his gratitude for helping
; derive the main ideas.

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

; Hopefully very rarely, we busy wait for the future to arrive.

    (loop while (not (faref *future-array* index)) do
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

; The following does not need to be inside an unwindprotect-cleanup because
; set-thread-check-for-abort-and-funcall also removes the pointer to this
; thread in *thread-array*.

    (atomic-decf *unassigned-and-active-future-count*)
    (atomic-decf *total-future-count*)
    (when thrown-tag
      (setf (mt-future-thrown-tag future)
            (cons thrown-tag thrown-val))

; A future that threw a tag is still a legal future to read.  In fact, the
; throw does not re-occur until the future is read.

      (broadcast-barrier (mt-future-valid future)))))

(defun eval-closures ()
  ;; (atomic-incf *idle-future-thread-count*) ; done inside the spawner
  (catch :worker-thread-no-longer-needed
    (let ((*throwable-worker-thread* t))
      (loop 
       (wait-for-a-closure)
; the catch of tag :result-no-longer-needed is performed inside eval-a-closure
       (eval-a-closure))))
; The following decrement will always execute, unless the user terminates the
; thread in some manual raw Lisp way.
  (atomic-decf *idle-future-thread-count*))

(defun spawn-closure-consumers ()
  (without-interrupts
; There may be a bug where *idle-future-thread-count* is incremented to 64
; under early termination.
   (loop while (< (atomically-modifiable-counter-read *idle-future-thread-count*) 
                  *max-idle-thread-count*) 
     do
     (progn (atomic-incf *idle-future-thread-count*)
            (incf *threads-spawned*)
            (run-thread "Worker thread" 'eval-closures)))))

(defun make-future-with-closure (closure)
  (let ((future (make-mt-future))
        (index (atomic-incf *last-slot-saved*)))
    (assert (not (faref *thread-array* index)))
    (assert (not (faref *future-array* index)))
    (assert (not (faref *future-dependencies* index)))
    (setf (mt-future-index future) index)
    (setf (faref *future-dependencies* *current-thread-index*)
          (cons index (faref *future-dependencies* *current-thread-index*)))
    (setf (mt-future-closure future) closure)
    future))

(defun add-future-to-queue (future)

; Must be called with interrupts disabled

  (setf (faref *future-array* (mt-future-index future))
        future)
  (atomic-incf *total-future-count*)
  (atomic-incf *unassigned-and-active-future-count*)
  (spawn-closure-consumers)
  (signal-semaphore *future-added*)
  future)

(defmacro mt-future (x)
  `(if #-skip-resource-availability-test (not (futures-resources-available))
       #+skip-resource-availability-test nil
; need to return a "single-threaded" future, as in futures-st.lisp
     (prog2 (incf *futures-resources-unavailable-count*)
         (st-future ,x))
     ;;     ,(multiple-value-list x)
     (prog2 (incf *futures-resources-available-count*)
         (let* (

; Parallelism wart: if x contains references to any of the following let-bound
; variables, these bindings will shadow the values in x.  We should consider
; using a gensym to ensure that this doesn't occur.

                (ld-level *ld-level*)
; consider also *ev-shortcut-okp* *raw-guard-warningp*
                (acl2-unwind-protect-stack *acl2-unwind-protect-stack*)
                (wormholep *wormholep*)
                ;; (wormhole-cleanup-form *wormhole-cleanup-form*)
                (standard-oi  *standard-oi*)
                (standard-co *standard-co*)
                (local-safe-mode (f-get-global 'safe-mode *the-live-state*))
                (local-gc-on (f-get-global 'guard-checking-on
                                           *the-live-state*)) 

; Parallelism wart: consider inheriting ld-specials, as the following comment
; suggests.

; At one point, in an effort to fix printing in parallel from within wormholes,
; I tried rebinding the ld-special.  I now know that my approach at that time
; was doomed to fail, because these specials aren't implemented as global
; variables but instead as a setq of a variable in a completely different
; package.  Now that I understand how state global variables work in ACL2, it
; may be worth coming back to this code and trying once again to inherit the
; ld-specials.

                ;; *deep-gstack*  ???
                ;; (proofs-co *standard-co*)
                ;; (ld-skip-proofsp (f-get-global 'ld-skip-proofsp
                ;;                                 *the-live-state*)) 
                ;; (ld-redefinition-action . nil)
                ;; (ld-prompt . t)
                ;; (ld-keyword-aliases . nil)
                ;; (ld-pre-eval-filter . :all)
                ;; (ld-pre-eval-print . nil)
                ;; (ld-post-eval-print . :command-conventions)
                ;; (ld-evisc-tuple . nil)
                ;; (ld-error-triples . t)
                ;; (ld-error-action . :continue)
                ;; (ld-query-control-alist . nil)
                ;; (ld-verbose 
    
                (closure (lambda () 
                           (let ((*ld-level* ld-level)
                                 (*acl2-unwind-protect-stack*
                                  acl2-unwind-protect-stack) 
                                 (*wormholep* wormholep)
                                 ;; (*wormhole-cleanup-form*
                                 ;;  wormhole-cleanup-form)
                                 (*standard-oi* standard-oi)
                                 (*standard-co* standard-co)
                                 ;; (*proofs-co* proofs-co)
                                 )
                             (state-free-global-let*
                              ((safe-mode local-safe-mode)
                               (guard-checking-on local-gc-on))
                              ,x)))))
           (without-interrupts
            (let ((future (make-future-with-closure closure)))
              (without-interrupts (add-future-to-queue future))
              future))))))

(defun mt-future-read (future)
  (cond ((st-future-p future)
         (st-future-read future))
        ((mt-future-p future)
         (progn
           (when (not (barrier-value (mt-future-valid future)))
             (let ((notif nil))
               (unwind-protect-disable-interrupts-during-cleanup
                (progn

; It's possible for (barrier-value (mt-future-valid future)) to be true.  It's a
; race condition.  However, since testing the future for validity before
; performing some waits is merely an optimization, there's no need to worry
; about the race condition.  It's rare anyway.

                  (free-allocated-core)

; TODO: this may be broken under early termination, but I don't see how.

                  (without-interrupts 
                   (atomic-decf *unassigned-and-active-future-count*)
                   (setq notif t))
                  (wait-on-barrier (mt-future-valid future))

; The following claiming isn't necessary under early termination, and in fact,
; it usually doesn't occur because it's in the the unprotected part of the
; unwind-protect.  It's unnecessary because if we're terminating early, we
; don't really care whether we "claim" the core.  In fact, we actually prefer
; to leave the core unclaimed, because claiming the core would require
; receiving a semaphore signal.

                  (claim-resumptive-core))
                
                (progn
                  (when notif
                    (atomic-incf *unassigned-and-active-future-count*))))))
           (when (mt-future-thrown-tag future)
             (throw (car (mt-future-thrown-tag future)) 
                    (cdr (mt-future-thrown-tag future))))
           (values-list (mt-future-value future))))
        (t
         (error "future-read was given a non-future argument"))))

(defvar *aborted-futures-via-throw* 0)

(defvar *almost-aborted-future-count* 

; TODO: document *almost-aborted-future-count*

  0)

(defun mt-future-abort (future)

; All calls to future-abort must be made by the parent of the future being
; aborted.  This gives us some notion of single-threadedness, which removes the
; need for locking in some of the code below.  This means the aborting
; mechanism would not work for pand/por.

; After further consideration, I'm not sure whether the above matters.  It'd be
; nice to think that a thread can only be aborted once, but so long as we
; conditionalize the throw correctly, it's probably even okay to throw abort a
; future more than once

; We do require that a future be "setup" before being thrown.  By this, we mean
; that all events associated with storing it in the *future-array* before the
; signaling are allowed to occur.

; Woops, due to the reading and writing of slots in *future-dependencies*, only
; one thread should be able to create and abort its children.  Otherwise those
; slots could become corrupt.

; This abortion is non-blocking; i.e., it will issue an abort and return.  It
; doesn't know when the abort will finish.

; It's possible that future will be nil.  This happens when the future has
; already finished evluation and set its position in *future-array* to nil.  We
; also don't abort if it's just a computed value.

  (incf *aborted-futures-total*)
  (cond ((st-future-p future)
         (st-future-abort future))
        ((mt-future-p future)

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
                 (lambda()
                   (if (equal (mt-future-index future)
                              *current-thread-index*)
                       (when *throwable-future-worker-thread*
                         (incf *aborted-futures-via-throw*)
                         (throw :result-no-longer-needed nil))
                     
; *Almost-aborted-future-count* can be incremented when the
; *current-thread-index* has fallen back to its value for when the thread is
; unassociated with any future (0).  It can also be incremented when the thread
; has already picked up a new piece of work, but in practice this latter
; occurence will almost never happen.
                     
                     (incf *almost-aborted-future-count*)))))))))
        ((null future) t) ; future already removed from the future-array
        (t 
         (error "future-abort was given a non-future argument")))
  future)

(defun abort-future-indexes (indexes)

; Only call from future-abort, which has a theoretical read-lock on the value
; of indexes (I quite literally mean "theoretical", as only by reasoning can we
; deduce that the source of the argument "indexes", array
; *future-dependencies*, is not changing underneath us).

  (if (endp indexes)
      t
    (progn (mt-future-abort (faref *future-array* (car indexes)))
           (abort-future-indexes (cdr indexes)))))

(defun print-non-nils-in-array (array n) 
  (if (equal n (length array))
      "end"
    (if (null (faref array n))
        (print-non-nils-in-array array (1+ n))
      (progn (print n) 
             (print (faref array n)) 
             (print-non-nils-in-array array (1+ n))))))

;---------------------------------------------------------------------
; Section:  Futures Interface

(defmacro future (x)
  `(mt-future ,x))

(defun future-read (x)
  (mt-future-read x))

(defun future-abort (x)
  (mt-future-abort x))

(defun abort-futures (futures)
  (if (atom futures)
      t
    (prog2 (future-abort (car futures))
        (abort-futures (cdr futures)))))
