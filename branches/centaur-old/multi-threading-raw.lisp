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

; This file is divided into the following sections.

; Section:  Enabling and Disabling Interrupts
; Section:  Threading Interface

(in-package "ACL2")

; For readability we use #+sb-thread" instead of #+(and sbcl sbl-thread).  We
; therefore make the following check to ensure that these two readtime
; conditionals are equivalent.

#+(and (not sbcl) sb-thread)
(error "Feature sb-thread not supported on Lisps other than SBCL")

;---------------------------------------------------------------------
; Section:  Enabling and Disabling Interrupts

; "Without-interrupts" means that there will be no interrupt from the Lisp
; system, including ctrl+c from the user or an interrupt from another
; thread/process.  For example, if *thread1* is running (progn
; (without-interrupts (process0)) (process1)), then execution of
; (interrupt-thread *thread1* (lambda () (break))) will not interrupt
; (process0).

; But note that "without-interrupts" does not guarantee atomicity; for example,
; it does not mean "without-setq".

(defmacro without-interrupts (&rest forms)

; This macro prevents interrupting evaluation of any of the indicated forms in
; a parallel lisp.  In a non-parallel environment (#-(or ccl sb-thread)),
; we simply evaluate the forms.  This behavior takes priority over any
; enclosing call of with-interrupts.  Since we do not have a good use case for
; providing with-interrupts, we omit it from this interface.

  #+ccl
  `(ccl:without-interrupts ,@forms)
  #+sb-thread
  `(sb-sys:without-interrupts ,@forms)
  #-(or ccl sb-thread)
  `(progn ,@forms))

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

;---------------------------------------------------------------------
; Section:  Threading Interface
;
; The threading interface is intended for system level programmers.  It is not
; intended for the ACL2 user.  When writing system-level multi-threaded code,
; we use implementation-independent interfaces.  If you need a function not
; covered in this interface, create the interface!

; Many of the functions in this interface (lockp, make-lock, and so on) are not
; used elsewhere, but are included here in case we find a use for them later.

; We take a conservative approach for implementations that do not support
; parallelism.  For example, if the programmer asks for a semaphore or lock in
; an unsupported Lisp, then nil is returned.

; We employ counting semaphores.  For details, including a discussion of
; ordering, see comments in the definition of function make-semaphore.

; Note: We use parts of the threading interface for our implementation of the
; parallelism primitives.

#+sb-thread
(defstruct (atomically-modifiable-counter
            (:constructor make-atomically-modifiable-counter-raw))
  (val 0 :type (unsigned-byte #+x86-64 64 #-x86-64 32)))

(defun make-atomically-modifiable-counter (initial-value)
  #+ccl
  initial-value
  #+sb-thread
  (make-atomically-modifiable-counter-raw :val initial-value)
  #-(or ccl sb-thread)
  initial-value)

(defmacro define-atomically-modifiable-counter (name initial-value)
  `(defvar ,name (make-atomically-modifiable-counter ,initial-value)))

(defmacro atomically-modifiable-counter-read (counter)
  #+ccl
  counter
  #+sb-thread
  `(atomically-modifiable-counter-val ,counter)
  #-(or ccl sb-thread)
  counter)

(defmacro atomic-incf (x)

; Warning: CCL and SBCL return different values for atomic-incf.  As of Oct
; 2009, CCL returns the new value, but SBCL returns the old value.  We
; artificially add one to the SBCL return value to make them consistent.  Both
; the CCL maintainer Gary Byers and the SBCL community have confirmed the
; return value of atomic-incf/decf to be reliable.

  #+ccl
  `(ccl::atomic-incf ,x)
  #+sb-thread
  `(1+ (sb-ext:atomic-incf (atomically-modifiable-counter-val ,x)))
  #-(or ccl sb-thread)
  `(incf ,x))

(defmacro atomic-incf-multiple (counter count)

; Warning: CCL and SBCL return different values for atomic-incf.  As of Oct
; 2009, CCL returns the new value, but SBCL returns the old value.  We
; artificially add one to the SBCL return value to make them consistent.  Both
; the CCL maintainer Gary Byers and the SBCL community have confirmed the
; return value of atomic-incf/decf to be reliable.

  #+ccl
  `(without-interrupts (dotimes (i ,count) (ccl::atomic-incf ,counter)))
  #+sb-thread
  `(+ (sb-ext:atomic-incf (atomically-modifiable-counter-val ,counter) ,count)
      ,count)
  #-(or ccl sb-thread)
  `(incf ,counter ,count))

(defmacro atomic-decf (x)

; Warning: CCL and SBCL return different values for atomic-incf.  As of Oct
; 2009, CCL returns the new value, but SBCL returns the old value.  We
; artificially add one to the SBCL return value to make them consistent.  Both
; the CCL maintainer Gary Byers and the SBCL community have confirmed the
; return value of atomic-incf/decf to be reliable.

  #+ccl
  `(ccl::atomic-decf ,x)
  #+sb-thread
  `(1- (sb-ext::atomic-incf (atomically-modifiable-counter-val ,x) -1))
  #-(or ccl sb-thread)
  `(decf ,x))

(defun lockp (x)
  #+ccl (cl:typep x 'ccl::recursive-lock)
  #+sb-thread (cl:typep x 'sb-thread::mutex)
  #-(or ccl sb-thread)

; We return nil in the uni-threaded case in order to stay in sync with
; make-lock, which returns nil in this case.  In a sense, we want (lockp
; (make-lock x)) to be a theorem if there is no error.

  (null x))

(defun make-lock (&optional lock-name)

; See also deflock.

; Even though CCL nearly always uses a FIFO for threads blocking on a lock,
; it does not guarantee so: no such promise is made by the CCL
; documentation or implementor (in fact, we are aware of a race condition that
; would violate FIFO properties for locks).  Thus, we make absolutely no
; guarantees about ordering; for example, we do not guarantee that the
; longest-blocked thread for a given lock is the one that would enter a
; lock-guarded section first.  However, we suspect that this is usually the
; case for most implementations, so assuming such an ordering property is
; probably a reasonable heuristic.  We would be somewhat surprised to find
; significant performance problems in our own application to ACL2's parallelism
; primitives due to the ordering provided by the underlying system.

  #-(or ccl sb-thread)
  (declare (ignore lock-name))
  #+ccl (ccl:make-lock lock-name)
  #+sb-thread (sb-thread:make-mutex :name lock-name)
  #-(or ccl sb-thread)

; We return nil in the uni-threaded case in order to stay in sync with lockp.

  nil)

(defmacro deflock (lock-symbol)

; Deflock defines what some Lisps call a "recursive lock", namely a lock that
; can be grabbed more than once by the same thread, but such that if a thread
; outside the owner tries to grab it, that thread will block.

; Note that if lock-symbol is already bound, then deflock will not re-bind
; lock-symbol.

  `(defvar ,lock-symbol
     (make-lock (symbol-name ',lock-symbol))))

(defmacro reset-lock (bound-symbol)

; This macro binds the given global (but not necessarily special) variable to a
; lock that is new, at least from a programmer's perspective.

; Reset-lock should only be applied to bound-symbol if deflock has previously
; been applied to bound-symbol.

  `(setq ,bound-symbol (make-lock ,(symbol-name bound-symbol))))

(defmacro with-lock (bound-symbol &rest forms)

; Grab the lock, blocking until it is acquired; evaluate forms; and then
; release the lock.  This macro guarantees mutual exclusion.

  #-(or ccl sb-thread)
  (declare (ignore bound-symbol))
  (let ((forms

; We ensure that forms is not empty because otherwise, in CCL alone,
; (with-lock some-lock) evaluates to t.  We keep the code simple and consistent
; by modifying forms here for all cases, not just CCL.

         (or forms '(nil))))
    #+ccl
    `(ccl:with-lock-grabbed (,bound-symbol) nil ,@forms)
    #+sb-thread
    `(sb-thread:with-recursive-lock (,bound-symbol) nil ,@forms)
    #-(or ccl sb-thread)
    `(progn ,@forms)))

(defun run-thread (name fn-symbol &rest args)

; Apply fn-symbol to args.  We follow the precedent set by LISP machines (and
; in turn CCL), which allowed the user to spawn a thread whose initial
; function receives an arbitrary number of arguments.

; We expect this application to occur in a fresh thread with the given name.
; When a call of this function returns, we imagine that this fresh thread can
; be garbage collected; at any rate, we don't hang on to it!

; Note that run-thread returns different types in different Lisps.

; A by-product of our use of lambdas is that fn-symbol doesn't have to be a
; function symbol.  It's quite fine to call run-thread with a lambda, e.g.
;
; (run-thread "hello" (lambda () (print "hi")))
;
; A more sophisticated version of run-thread would probably check whether
; fn-symbol was indeed a symbol and only create a new lambda if it was.

  #-(or ccl sb-thread)
  (declare (ignore name))
  #+ccl
  (ccl:process-run-function name (lambda () (apply fn-symbol args)))
  #+sb-thread
  (sb-thread:make-thread (lambda () (apply fn-symbol args)) :name name)

; We're going to be nice and let the user's function still run, even though
; it's not split off.

  #-(or ccl sb-thread)
  (apply fn-symbol args))

(defun interrupt-thread (thread function &rest args)

; Interrupt the indicated thread and then, in that thread, apply function to
; args.  Note that function and args are all evaluated.  When this function
; application returns, the thread resumes from the interrupt (from where it
; left off).

  #-(or ccl sb-thread)
  (declare (ignore thread function args))
  #+ccl
  (apply #'ccl:process-interrupt thread function args)
  #+sb-thread
  (if args
      (error "Passing arguments to interrupt-thread not supported in SBCL.")
    (sb-thread:interrupt-thread thread function))
  #-(or ccl sb-thread)
  nil)

(defun kill-thread (thread)
  #-(or ccl sb-thread)
  (declare (ignore thread))
  #+ccl
  (ccl:process-kill thread)
  #+sb-thread
  (sb-thread:terminate-thread thread)
  #-(or ccl sb-thread)
  nil)

(defun all-threads ()
  #+ccl
  (ccl:all-processes)
  #+sb-thread
  (sb-thread:list-all-threads)
  #-(or ccl sb-thread)
  (error "We don't know how to list threads in this Lisp."))

(defun current-thread ()
  #+ccl
  ccl:*current-process*
  #+sb-thread
  sb-thread:*current-thread*
  #-(or ccl sb-thread)
  nil)

(defun thread-wait (fn &rest args)

; Thread-wait provides an inefficient mechanism for the current thread to wait
; until a given condition, defined by the application of fn to args, is true.
; When performance matters, we advise using a signaling mechanism over this
; hacker's function.

  #+ccl
  (apply #'ccl:process-wait "Asynchronously waiting on a condition" fn args)
  #-ccl
  (loop while (not (apply fn args)) do (sleep 0.05)))

#+sb-thread
(defstruct sbcl-semaphore
  (lock (sb-thread:make-mutex))
  (cv (sb-thread:make-waitqueue)) ; condition variable
  (count 0))

#+sb-thread
(defmacro with-potential-sbcl-timeout (body &key timeout)

; There is no implicit progn for the body argument.  This is different from
; sb-sys:with-deadline, but we figure the simplicity is more valuable than
; randomly passing in a :timeout value.

    `(if ,timeout
         (handler-case
          (sb-sys:with-deadline
           (:seconds ,timeout)
           ,body)

          (sb-ext:timeout ()))
       ,body))

; We would like to find a clean way to provide the user with an implicit progn,
; while still maintaining timeout as a keyword argument.

; #+sb-thread
; (defmacro with-potential-sbcl-timeout (&rest body &key timeout)
; 
; ; The below use of labels is only neccessary because we provide an implicit
; ; progn for the body of with-potential-sbcl-timeout.
; 
;   (let ((correct-body
;          (labels ((remove-keyword-from-list
;                    (lst keyword)
;                    (if (or (atom lst) (atom (cdr lst)))
;                        lst
;                      (if (equal (car lst) :timeout)
;                          (cddr lst)
;                        (cons (car lst) (remove-keyword-from-args (cdr lst)))))))
;                  (remove-keyword-from-args body :timeout))))
; 
; 
;     `(if ,timeout
;          (handler-case
;           (sb-sys:with-deadline
;            (:seconds ,timeout)
;            ,@correct-body)
; 
;           (sb-ext:timeout ()))
;        ,@correct-body)))

(defun make-semaphore (&optional name)

; Make-semaphore, signal-semaphore, and semaphorep work together to implement
; counting semaphores for the threading interface.

; This function creates "counting semaphores", which are data structures that
; include a "count" field, which is a natural number.  A thread can "wait on" a
; counting semaphore, and it will block in the case that the semaphore's count
; is 0.  To "signal" such a semaphore means to increment that field and to
; notify a unique waiting thread (we will discuss a relaxation of this
; uniqueness shortly) that the semaphore's count has been incremented.  Then
; this thread, which is said to "receive" the signal, decrements the
; semaphore's count and is then unblocked.  This mechanism is typically much
; faster than busy waiting.

; In principle more than one waiting thread could be notified (though this
; seems rare in practice).  In this case, only one would be the receiving
; thread, i.e., the one that decrements the semaphore's count and is then
; unblocked.

; If semaphore usage seems to perform inefficiently, could this be due to
; ordering issues?  For example, even though CCL nearly always uses a FIFO
; for blocked threads, it does not guarantee so: no such promise is made by the
; CCL documentation or implementor.  Thus, we make absolutely no guarantees
; about ordering; for example, we do not guarantee that the longest-blocked
; thread for a given semaphore is the one that would receive a signal.
; However, we suspect that this will usually be the case for most
; implementations, so assuming such an ordering property is probably a
; reasonable heuristic.  We would be somewhat surprised to find significant
; performance problems in our own application to ACL2's parallelism primitives
; due to the ordering provided by the underlying system.

; CCL provides us with semaphores for signaling.  SBCL provides condition
; variables for signaling.  Since we want to code for one type of signaling
; between parents and children, we create a semaphore wrapper for SBCL's
; condition variables.  The structure sbcl-semaphore implements the data for
; this wrapper.

; Followup: SBCL has recently (as of November 2010) implemented semaphores, and
; the parallelism code could be changed to reflect this.  However, since SBCL
; does not implement semaphore-nofication-object's, we choose to stick with our
; own implementation of semaphores for now.

  (declare (ignore name))
  #+ccl
  (ccl:make-semaphore)
  #+sb-thread
  (make-sbcl-semaphore)
  #-(or ccl sb-thread)

; We return nil in the uni-threaded case in order to stay in sync with
; semaphorep.

  nil)

(defun semaphorep (semaphore)

; Make-semaphore, signal-semaphore, and semaphorep work together to implement
; counting semaphores for our threading interface.

; This function recognizes our notion of semaphore structures.

  #+ccl
  (typep semaphore 'ccl::semaphore)
  #+sb-thread
  (and (sbcl-semaphore-p semaphore)
       (typep (sbcl-semaphore-lock semaphore) 'sb-thread::mutex)
       (typep (sbcl-semaphore-cv semaphore) 'sb-thread::waitqueue)
       (integerp (sbcl-semaphore-count semaphore)))
  #-(or ccl sb-thread)

; We return nil in the uni-threaded case in order to stay in sync with
; make-semaphore, which returns nil in this case.  In a sense, we want
; (semaphorep (make-semaphore x)) to be a theorem if there is no error.

  (null semaphore))

(defun signal-semaphore (semaphore)

; Make-semaphore, signal-semaphore, and semaphorep work together to implement
; counting semaphores for our threading interface.

; This function is executed for side effect; the value returned is irrelevant.

  #-(or ccl sb-thread)
  (declare (ignore semaphore))
  #+ccl
  (ccl:signal-semaphore semaphore)
  #+sb-thread
  (sb-thread:with-recursive-lock
   ((sbcl-semaphore-lock semaphore))
   (without-interrupts
    (incf (sbcl-semaphore-count semaphore))
    (sb-thread:condition-notify (sbcl-semaphore-cv semaphore))))
  #-(or ccl sb-thread)
  nil)

; Once upon a time, we optimized the manual allocation and deallocation of
; semaphores so that they could be recycled.  CCL and SBCL have since evolved,
; and as such, we have removed the implementation code and its corresponding
; uses.

(defun wait-on-semaphore (semaphore &key notification timeout)

; This function is guaranteed to return t when it has received the signal.  Its
; return value when the signal has not been received is unspecified.  As such,
; we provide the semaphore notification object as a means for determining
; whether a signal was actually received.

; This function only returns normally after receiving a signal for the given
; semaphore, setting the notification status of notification (if supplied and
; non-nil) to true; see semaphore-notification-status.  But control can leave
; this function abnormally, for example if the thread executing a call of this
; function is interrupted (e.g., with interface function interrupt-thread) with
; code that does a throw, in which case notification is unmodified.

; We need the ability to know whether we received a signal or not.  CCL
; provides this through a semaphore notification object.  SBCL does not provide
; this mechanism currently, so we might "unreceive the signal" in the cleanup
; form of the implementation.  We do this by only decrementing the count of the
; semaphore iff we set the notification object.  This means we have to resignal
; the semaphore if we were interrupted while signaling, but we would have to do
; this anyway.

  #-(or ccl sb-thread)
  (declare (ignore semaphore notification))

  #+ccl
  (if timeout
      (ccl:timed-wait-on-semaphore semaphore timeout notification)
    (ccl:wait-on-semaphore semaphore notification))

  #+sb-thread
  (let ((supposedly-did-not-receive-signal-p t))
    (sb-thread:with-recursive-lock
     ((sbcl-semaphore-lock semaphore))
     (unwind-protect-disable-interrupts-during-cleanup
      (with-potential-sbcl-timeout
       (progn
         (loop while (<= (sbcl-semaphore-count semaphore) 0) do

; The current thread missed the chance to decrement and must rewait.

               (sb-thread:condition-wait (sbcl-semaphore-cv semaphore)
                                         (sbcl-semaphore-lock semaphore)))
         (setq supposedly-did-not-receive-signal-p nil)
         t) ; if this progn returns, this t is the return value
       :timeout timeout)
      (if supposedly-did-not-receive-signal-p

; The current thread may have received the signal but been unable to record it.
; In this case, the current thread will signal the condition variable again, so
; that any other thread waiting on the semaphore can have a chance at acquiring
; the said semaphore.

          (sb-thread:condition-notify (sbcl-semaphore-cv semaphore))

; The current thread was able to record the reception of the signal.  The
; current thread will decrement the count of the semaphore and set the
; semaphore notification object.

        (progn
          (decf (sbcl-semaphore-count semaphore))
          (when notification
            (set-semaphore-notification-status notification)))))))

  #-(or ccl sb-thread)
  t) ; default is to receive a semaphore/lock

(defun make-semaphore-notification ()

; This function returns an object that records when a corresponding semaphore
; has been signaled (for use when wait-on-semaphore is called with that
; semaphore and that object).

  #+ccl
  (ccl:make-semaphore-notification)
  #+sb-thread
  (make-array 1 :initial-element nil)
  #-(or ccl sb-thread)
  nil)

(defun semaphore-notification-status (semaphore-notification-object)
  #-(or ccl sb-thread)
  (declare (ignore semaphore-notification-object))
  #+ccl
  (ccl:semaphore-notification-status semaphore-notification-object)
  #+sb-thread
  (aref semaphore-notification-object 0)
  #-(or ccl sb-thread)
; t may be the wrong default, but we don't have a use case for this return
; value yet, so we postpone thinking about the "right" value until we are aware
; of a need.
  t)

(defun clear-semaphore-notification-status (semaphore-notification-object)
  #-(or ccl sb-thread)
  (declare (ignore semaphore-notification-object))
  #+ccl
  (ccl:clear-semaphore-notification-status semaphore-notification-object)
  #+sb-thread
  (setf (aref semaphore-notification-object 0) nil)
  #-(or ccl sb-thread)
  nil)

; We implement this only for SBCL, because even a system-level programmer is
; not expected to use this function.  We use it only from within the threading
; interface to implement wait-on-semaphore for SBCL.

(defun set-semaphore-notification-status (semaphore-notification-object)
  #-sb-thread
  (declare (ignore semaphore-notification-object))
  #+sb-thread
  (setf (aref semaphore-notification-object 0) t)
  #-sb-thread
  (error "Set-semaphore-notification-status not supported outside SBCL"))

; Essay on Condition Variables

; A condition variable is a data structure that can be passed to corresponding
; "wait" and "signal" functions.  When a thread calls the wait function on a
; condition variable, c, the thread blocks until "receiving a signal" from the
; application of the signal function to c.  Only one signal is sent per call of
; the signal function; so, at most one thread will unblock.  (There is a third
; notion for condition variable, namely the broadcast function, which is like
; the signal function except that all threads blocking on the given condition
; variable will unblock.  But we do not support broadcast functions in this
; interface, in part because we use semaphores for CCL, and there's no way
; to broadcast when you're really using a semaphore.)

; The design of our parallelism library is simpler when using condition
; variables for the following reason: Since a worker must wait for two
; conditions before consuming work, it is better to use a condition variable
; and test those two conditions upon waking, rather than try and use two
; semaphores.

; Implementation Note: As of March 2007, our CCL implementation does not
; yield true condition variables.  A condition variable degrades to a
; semaphore, so if one thread first signals a condition variable, then that
; signal has been stored.  Then later (perhaps much later), when another thread
; waits for that signal, that thread will be able to proceed by decrementing
; the count.  As a result the later thread will "receive" the signal, even
; though that signal occurred in the past.  Fortunately, this isn't a
; contradiction of the semantics of condition variables, since with condition
; variables there is no specification of how far into the future the waiting
; thread will receive a signal from the signalling thread.

; Note: Condition variables should not be used to store state.  They are only a
; signaling mechanism, and any state update implied by receiving a condition
; variable's signal should be checked.  This usage is believed to be consistent
; with traditional condition variable semantics.

(defun make-condition-variable ()

; If CCL implements condition variables, we will want to change the CCL
; expansion and remove the implementation note above.

; Because implementing broadcast for condition variables in CCL is much more
; heavyweight than a simple semaphore, we keep it simple until we have a use
; case for a broadcast.  Such simple requirements are satisfied by using a
; semaphore.

  #+ccl
  (ccl:make-semaphore)

  #+sb-thread
  (sb-thread:make-waitqueue)

  #-(or ccl sb-thread)

; We may wish to have assertions that evaluation of (make-condition-variable)
; is non-nil.  So we return t, even though as of this writing there are no such
; assertions.

  t)

(defmacro signal-condition-variable (cv)
  #-(or ccl sb-thread)
  (declare (ignore cv))

  #+ccl
  `(ccl:signal-semaphore ,cv)

  #+sb-thread

; According to an email sent by Gabor Melis, of SBCL help, on 2007-02-25, if
; there are two threads waiting on a condition variable, and a third thread
; signals the condition variable twice before either can receive the signal,
; then both threads should receive the signal.  If only one thread unblocks, it
; is considered a bug.

  `(sb-thread:condition-notify ,cv)

  #-(or ccl sb-thread)
  t)

(defmacro broadcast-condition-variable (cv)
  #-sb-thread
  (declare (ignore cv))

  #+ccl
  (error "Broadcasting condition variables is unsupported in CCL")

  #+sb-thread
  `(sb-thread:condition-broadcast ,cv)

  #-(or ccl sb-thread)
  t)

(defun wait-on-condition-variable (cv lock &key timeout)

; A precondition to this function is that the current thread "owns" lock.  This
; is a well-known part of how condition variables work.  This is also
; documented in the SBCL manual in section 12.5 entitled "Waitqueue/condition
; variables."

  #-sb-thread
  (declare (ignore cv lock timeout))

  #+ccl
  (error "Waiting on condition variables with locks is unsupported in CCL")

  #+sb-thread
  (with-potential-sbcl-timeout
   (sb-thread:condition-wait cv lock)
   :timeout timeout)

  #-(or ccl sb-thread)
  nil) ; the default is to never receive a signal
