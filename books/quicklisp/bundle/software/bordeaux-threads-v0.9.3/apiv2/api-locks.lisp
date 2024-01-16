;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: BORDEAUX-THREADS-2 -*-
;;;; The above modeline is required for Genera. Do not change.

(in-package :bordeaux-threads-2)

(defun native-lock-p (object)
  (typep object 'native-lock))

(defclass lock ()
  ((name :initarg :name :reader lock-name)
   (native-lock :initarg :native-lock :reader lock-native-lock))
  (:documentation "Wrapper for a native non-recursive lock."))

(defmethod print-object ((lock lock) stream)
  (print-unreadable-object (lock stream :type t :identity t)
    (format stream "~S" (lock-name lock))))

(defun lockp (object)
  "Returns T if OBJECT is a non-recursive lock; returns NIL otherwise."
  (typep object 'lock))

(defun make-lock (&key name)
  "Creates a lock (a mutex) whose name is NAME."
  (check-type name (or null string))
  (make-instance 'lock
                 :name name
                 :native-lock (%make-lock name)))

(defun acquire-lock (lock &key (wait t) timeout)
  "Acquire the lock LOCK for the calling thread.

  WAIT governs what happens if the lock is not available: if WAIT
  is true, the calling thread will wait until the lock is available
  and then acquire it; if WAIT is NIL, ACQUIRE-LOCK will return
  immediately.

  If WAIT is true, TIMEOUT may specify a maximum amount of seconds to
  wait for the lock to become available.

  ACQUIRE-LOCK returns T if the lock was acquired and NIL
  otherwise.

  This specification does not define what happens if a thread
  attempts to acquire a lock that it already holds. For applications
  that require locks to be safe when acquired recursively, see instead
  MAKE-RECURSIVE-LOCK and friends."
  (check-type timeout (or null (real 0)))
  (%acquire-lock (lock-native-lock lock) (bool wait) timeout))

(defun release-lock (lock)
  "Release LOCK. It is an error to call this unless
  the lock has previously been acquired (and not released) by the same
  thread. If other threads are waiting for the lock, the
  ACQUIRE-LOCK call in one of them will now be able to continue.

  Returns the lock."
  (%release-lock (lock-native-lock lock))
  lock)

(defmacro with-lock-held ((place &key timeout)
                          &body body &environment env)
  "Evaluates BODY with the lock named by PLACE, the value of which
  is a lock created by MAKE-LOCK. Before the forms in BODY are
  evaluated, the lock is acquired as if by using ACQUIRE-LOCK. After the
  forms in BODY have been evaluated, or if a non-local control transfer
  is caused (e.g. by THROW or SIGNAL), the lock is released as if by
  RELEASE-LOCK.

  Note that if the debugger is entered, it is unspecified whether the
  lock is released at debugger entry or at debugger exit when execution
  is restarted."
  (declare (ignorable place timeout))
  (if (fboundp '%with-lock)
      (macroexpand-1
       `(%with-lock ((lock-native-lock ,place) ,timeout)
          ,@body)
       env)
      `(when (acquire-lock ,place :wait t :timeout ,timeout)
         (unwind-protect
              (locally ,@body)
           (release-lock ,place)))))

(defun native-recursive-lock-p (object)
  (typep object 'native-recursive-lock))

(defclass recursive-lock ()
  ((name :initarg :name :reader lock-name)
   (native-lock :initarg :native-lock :reader lock-native-lock))
  (:documentation "Wrapper for a native recursive lock."))

(defmethod print-object ((lock recursive-lock) stream)
  (print-unreadable-object (lock stream :type t :identity t)
    (format stream "~S" (lock-name lock))))

(defun recursive-lock-p (object)
  "Returns T if OBJECT is a recursive lock; returns NIL otherwise."
  (typep object 'recursive-lock))

(defun make-recursive-lock (&key name)
  "Create and return a recursive lock whose name is NAME.

  A recursive lock differs from an ordinary lock in that a thread that
  already holds the recursive lock can acquire it again without
  blocking. The thread must then release the lock twice before it
  becomes available for another thread (acquire and release operations
  must be balanced)."
  (check-type name (or null string))
  (make-instance 'recursive-lock
                 :name name
                 :native-lock (%make-recursive-lock name)))

(defun acquire-recursive-lock (lock &key (wait t) timeout)
  "Acquire the lock LOCK for the calling thread.

  WAIT governs what happens if the lock is not available: if WAIT is
  true, the calling thread will wait until the lock is available and
  then acquire it; if WAIT is NIL, ACQUIRE-RECURSIVE-LOCK will return
  immediately.

  If WAIT is true, TIMEOUT may specify a maximum amount of seconds to
  wait for the lock to become available.

  ACQUIRE-LOCK returns true if the lock was acquired and NIL
  otherwise.

  This operation will return immediately if the lock is already owned
  by the current thread. Acquire and release operations must be
  balanced."
  (check-type lock recursive-lock)
  (check-type timeout (or null (real 0)))
  (%acquire-recursive-lock (lock-native-lock lock) (bool wait) timeout))

(defun release-recursive-lock (lock)
  "Release LOCK. It is an error to call this unless
  the lock has previously been acquired (and not released) by the same
  thread.

  Returns the lock."
  (%release-recursive-lock (lock-native-lock lock))
  lock)

(defmacro with-recursive-lock-held ((place &key timeout)
                                    &body body &environment env)
  "Evaluates BODY with the recursive lock named by PLACE, which is a
  reference to a recursive lock created by MAKE-RECURSIVE-LOCK.
  See WITH-LOCK-HELD."
  (declare (ignorable place timeout))
  (if (fboundp '%with-recursive-lock)
      (macroexpand-1
       `(%with-recursive-lock ((lock-native-lock ,place) ,timeout)
          ,@body)
       env)
      `(when (acquire-recursive-lock ,place :wait t :timeout ,timeout)
         (unwind-protect
              (locally ,@body)
           (release-recursive-lock ,place)))))
