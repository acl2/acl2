;;;; -*- indent-tabs-mode: nil -*-

(in-package :bordeaux-threads-2)

;;;
;;; Threads
;;;

(deftype native-thread ()
  'threads:thread)

(defun %make-thread (function name)
  (threads:make-thread function :name name))

(defun %current-thread ()
  (threads:current-thread))

(defun %thread-name (thread)
  (threads:thread-name thread))

(defun %join-thread (thread)
  (threads:thread-join thread))

(defun %thread-yield ()
  (java:jstatic "yield" "java.lang.Thread"))

;;;
;;; Introspection/debugging
;;;

(defun %all-threads ()
  (let ((threads ()))
    (threads:mapcar-threads (lambda (thread)
                              (push thread threads)))
    (nreverse threads)))

(defun %interrupt-thread (thread function)
  (threads:interrupt-thread thread function))

(defun %destroy-thread (thread)
  (threads:destroy-thread thread))

(defun %thread-alive-p (thread)
  (threads:thread-alive-p thread))


;;;
;;; Non-recursive locks.
;;;

(defstruct mutex name lock)

(deftype native-lock () 'mutex)

(defun %make-lock (name)
  (make-mutex
   :name name
   :lock (jnew "java.util.concurrent.locks.ReentrantLock")))

;; Making methods constants in this manner avoids the runtime expense of
;; introspection involved in JCALL with string arguments.
(defconstant +lock+
  (jmethod "java.util.concurrent.locks.ReentrantLock" "lock"))
(defconstant +try-lock+
  (jmethod "java.util.concurrent.locks.ReentrantLock" "tryLock"))
(defconstant +try-lock-timeout+
  (jmethod "java.util.concurrent.locks.ReentrantLock" "tryLock"
           (jclass "long") (jclass "java.util.concurrent.TimeUnit")))
(defconstant +is-held-by-current-thread+
  (jmethod "java.util.concurrent.locks.ReentrantLock" "isHeldByCurrentThread"))
(defconstant +unlock+
  (jmethod "java.util.concurrent.locks.ReentrantLock" "unlock"))
(defconstant +get-hold-count+
  (jmethod "java.util.concurrent.locks.ReentrantLock" "getHoldCount"))
(defconstant +microseconds+
  (java:jfield "java.util.concurrent.TimeUnit" "MICROSECONDS"))

(defun timeout-to-microseconds (timeout)
  (truncate (* timeout 1000000)))

(defun %acquire-lock (lock waitp timeout)
  (check-type lock mutex)
  (when (jcall +is-held-by-current-thread+ (mutex-lock lock))
    (bt-error "Non-recursive lock being reacquired by owner."))
  (cond
    (waitp
     (if timeout
         (jcall +try-lock-timeout+
                (mutex-lock lock)
                (timeout-to-microseconds timeout)
                +microseconds+)
         (progn (jcall +lock+ (mutex-lock lock)) t)))
    (t (jcall +try-lock+ (mutex-lock lock)))))

(defun %release-lock (lock)
  (check-type lock mutex)
  (unless (jcall +is-held-by-current-thread+ (mutex-lock lock))
    (bt-error "Attempt to release lock not held by calling thread."))
  (jcall +unlock+ (mutex-lock lock)))

;;;
;;; Recursive locks
;;;

(defstruct (mutex-recursive (:include mutex)))

(deftype native-recursive-lock () 'mutex-recursive)

(defun %make-recursive-lock (name)
  (make-mutex-recursive
   :name name
   :lock (jnew "java.util.concurrent.locks.ReentrantLock")))

(defun %acquire-recursive-lock (lock waitp timeout)
  (check-type lock mutex-recursive)
  (cond
    (waitp
     (if timeout
         (jcall +try-lock-timeout+
                (mutex-recursive-lock lock)
                (timeout-to-microseconds timeout)
                +microseconds+)
         (progn (jcall +lock+ (mutex-recursive-lock lock)) t)))
    (t (jcall +try-lock+ (mutex-recursive-lock lock)))))

(defun %release-recursive-lock (lock)
  (check-type lock mutex-recursive)
  (unless (jcall +is-held-by-current-thread+ (mutex-lock lock))
    (error 'bordeaux-threads-error
           :message "Attempt to release lock not held by calling thread."))
  (jcall +unlock+ (mutex-lock lock)))


;;;
;;; Semaphores
;;;

(defstruct (semaphore
            (:constructor %%make-semaphore (name cell)))
  "Wrapper for java.util.concurrent.Semaphore."
  name cell)

(defconstant +semaphore-count+
  (jmethod "java.util.concurrent.Semaphore" "availablePermits"))

(defun %semaphore-count (semaphore)
  (jcall +semaphore-count+ (semaphore-cell semaphore)))

(defmethod print-object ((sem semaphore) stream)
  (print-unreadable-object (sem stream :type t :identity t)
    (format stream "~S count: ~S" (semaphore-name sem)
            (%semaphore-count sem))))

(defun %make-semaphore (name count)
  (check-type count unsigned-byte)
  (%%make-semaphore
   name
   (jnew "java.util.concurrent.Semaphore" count t)))

(defconstant +semaphore-release+
  (jmethod "java.util.concurrent.Semaphore" "release"
           (jclass "int")))

(defun %signal-semaphore (semaphore count)
  (jcall +semaphore-release+ (semaphore-cell semaphore) count))

(defconstant +semaphore-acquire+
  (jmethod "java.util.concurrent.Semaphore" "acquire"))

(defconstant +semaphore-try-acquire+
  (jmethod "java.util.concurrent.Semaphore" "tryAcquire"
           (jclass "long") (jclass "java.util.concurrent.TimeUnit")))

(defun %wait-on-semaphore (semaphore timeout)
  ;; TODO: handle thread interruption.
  (cond
    ((null timeout)
     (jcall +semaphore-acquire+ (semaphore-cell semaphore))
     t)
    (t
     (jcall +semaphore-try-acquire+
            (semaphore-cell semaphore)
            (timeout-to-microseconds timeout)
            +microseconds+))))


;;;
;;; Condition variables
;;;

(defstruct (condition-variable
            (:constructor %make-condition-variable (name)))
  name)

(defun %condition-wait (cv lock timeout)
  (threads:synchronized-on cv
    (%release-lock lock)
    (if timeout
        ;; Since giving a zero time value to threads:object-wait means
        ;; an indefinite wait, use some arbitrary small number.
        (threads:object-wait cv
                             (if (zerop timeout)
                                 least-positive-single-float
                                 timeout))
        (threads:object-wait cv)))
  (%acquire-lock lock t nil)
  t)

(defun %condition-notify (cv)
  (threads:synchronized-on cv
     (threads:object-notify cv)))

(defun %condition-broadcast (cv)
  (threads:synchronized-on cv
     (threads:object-notify-all cv)))
