;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: BORDEAUX-THREADS-2 -*-
;;;; The above modeline is required for Genera. Do not change.

(in-package :bordeaux-threads-2)

;;; Resource contention: condition variables

;;; A condition variable provides a mechanism for threads to put
;;; themselves to sleep while waiting for the state of something to
;;; change, then to be subsequently woken by another thread which has
;;; changed the state.
;;;
;;; A condition variable must be used in conjunction with a lock to
;;; protect access to the state of the object of interest. The
;;; procedure is as follows:
;;;
;;; Suppose two threads A and B, and some kind of notional event
;;; channel C. A is consuming events in C, and B is producing them.
;;; CV is a condition-variable
;;;
;;; 1) A acquires the lock that safeguards access to C
;;; 2) A threads and removes all events that are available in C
;;; 3) When C is empty, A calls CONDITION-WAIT, which atomically
;;;    releases the lock and puts A to sleep on CV
;;; 4) Wait to be notified; CONDITION-WAIT will acquire the lock again
;;;    before returning
;;; 5) Loop back to step 2, for as long as threading should continue
;;;
;;; When B generates an event E, it
;;; 1) acquires the lock guarding C
;;; 2) adds E to the channel
;;; 3) calls CONDITION-NOTIFY on CV to wake any sleeping thread
;;; 4) releases the lock
;;;
;;; To avoid the "lost wakeup" problem, the implementation must
;;; guarantee that CONDITION-WAIT in thread A atomically releases the
;;; lock and sleeps. If this is not guaranteed there is the
;;; possibility that thread B can add an event and call
;;; CONDITION-NOTIFY between the lock release and the sleep - in this
;;; case the notify call would not see A, which would be left sleeping
;;; despite there being an event available.

(defun condition-variable-p (object)
  "Returns TRUE if OBJECT is a condition variable, and NIL otherwise."
  (typep object 'condition-variable))

(defun make-condition-variable (&key name)
  "Returns a new condition-variable object for use
  with CONDITION-WAIT and CONDITION-NOTIFY."
  (check-type name (or null string))
  (%make-condition-variable name))

(defun condition-wait (condition-variable lock &key timeout)
  "Atomically release LOCK and enqueue the calling
  thread waiting for CONDITION-VARIABLE. The thread will resume when
  another thread has notified it using CONDITION-NOTIFY; it may also
  resume if interrupted by some external event or in other
  implementation-dependent circumstances: the caller must always test
  on waking that there is threading to be done, instead of assuming
  that it can go ahead.

  It is an error to call this function unless from the thread that
  holds LOCK.

  If TIMEOUT is nil or not provided, the call blocks until a
  notification is received.

  If TIMEOUT is non-nil, the call will return after at most TIMEOUT
  seconds (approximately), whether or not a notification has occurred.

  Either NIL or T will be returned. A return of NIL indicates that the
  timeout has expired without receiving a notification. A return of T
  indicates that a notification was received."
  (check-type timeout (or null (real 0)))
  (%condition-wait condition-variable
                   (lock-native-lock lock)
                   timeout))

(defun condition-notify (condition-variable)
  "Notify one of the threads waiting for
  CONDITION-VARIABLE.

  It is unspecified which thread gets a wakeup and does not
  necessarily relate to the order that the threads went to sleep in.

  CONDITION-NOTIFY returns always NIL."
  (%condition-notify condition-variable)
  nil)

(defun condition-broadcast (condition-variable)
  "Notify all threads waiting for CONDITION-VARIABLE.
  
  The order of wakeup is unspecified and does not necessarily relate
  to the order that the threads went to sleep in.

  CONDITION-BROADCAST returns always NIL."
  (%condition-broadcast condition-variable)
  nil)
