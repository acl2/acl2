;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: CL-USER -*-
;;;; The above modeline is required for Genera. Do not change.

(defpackage :bordeaux-threads-2
  (:nicknames :bt2)
  (:use :common-lisp :alexandria :global-vars)
  #+abcl
  (:import-from :java #:jnew #:jcall #:jclass #:jmethod)
  #+sbcl
  (:import-from :sb-ext #:timeout)

  (:export
   #:*supports-threads-p*
   #:bordeaux-threads-error
   #:not-implemented)

  ;; Threads
  (:export
   #:thread
   #:thread-name
   #:thread-native-thread
   #:threadp
   #:make-thread
   #:*default-special-bindings*
   #:*standard-io-bindings*
   #:current-thread
   #:all-threads
   #:start-multiprocessing

   #:interrupt-thread
   #:signal-in-thread
   #:warn-in-thread
   #:error-in-thread
   #:destroy-thread
   #:thread-alive-p
   #:join-thread
   #:abnormal-exit
   #:abnormal-exit-condition
   #:thread-yield)

  ;; Locks
  (:export
   #:lock
   #:lockp
   #:recursive-lock
   #:recursive-lock-p
   #:lock-name
   #:lock-native-lock
   #:native-lock
   #:native-lock-p
   #:native-recursive-lock
   #:native-recursive-lock-p

   #:make-lock
   #:acquire-lock
   #:release-lock
   #:with-lock-held

   #:make-recursive-lock
   #:acquire-recursive-lock
   #:release-recursive-lock
   #:with-recursive-lock-held)

  ;; Condition variables
  (:export
   #:condition-variable
   #:condition-variable-p
   #:make-condition-variable
   #:condition-wait
   #:condition-notify
   #:condition-broadcast)

  ;; Semaphores
  (:export
   #:semaphore
   #:semaphorep
   #:make-semaphore
   #:signal-semaphore
   #:wait-on-semaphore)

  ;; Atomic operations
  (:export
   #:make-atomic-integer
   #:atomic-integer-compare-and-swap
   #:atomic-integer-decf
   #:atomic-integer-incf
   #:atomic-integer-value)

  ;; Timeouts
  (:export
   #:timeout
   #:with-timeout)

  (:documentation "BORDEAUX-THREADS is a proposed standard for a minimal
  MP/threading interface. It is similar to the CLIM-SYS threading and
  lock support, but for the following broad differences:

  1) Some behaviours are defined in additional detail: attention has
     been given to special variable interaction, whether and when
     cleanup forms are run. Some behaviours are defined in less
     detail: an implementation that does not support multiple
     threads is not required to use a new list (nil) for a lock, for
     example.

  2) Many functions which would be difficult, dangerous or inefficient
     to provide on some implementations have been removed. Chiefly
     these are functions such as thread-wait which expect for
     efficiency that the thread scheduler is written in Lisp and
     'hookable', which can't sensibly be done if the scheduler is
     external to the Lisp image, or the system has more than one CPU.

  3) Unbalanced ACQUIRE-LOCK and RELEASE-LOCK functions have been
     added.

  4) Posix-style condition variables have been added, as it's not
     otherwise possible to implement them correctly using the other
     operations that are specified.

  Threads may be implemented using whatever applicable techniques are
  provided by the operating system: user-space scheduling,
  kernel-based LWPs or anything else that does the job.

  To avoid conflict with existing MP/threading interfaces in
  implementations, these symbols live in the BORDEAUX-THREADS-2 package.
  Implementations and/or users may also make them visible or exported
  in other more traditionally named packages."))
