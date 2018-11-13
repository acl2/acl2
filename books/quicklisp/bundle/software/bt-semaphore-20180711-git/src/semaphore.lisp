#|
  This file is a part of bt-semaphore project.
  Copyright (c) 2013 Ralph Moeritz (ralphmoritz@outlook.com)
|#

(in-package :bt-semaphore)

(defclass semaphore ()
  ((lock    :initform (bt:make-lock))
   (condvar :initform (bt:make-condition-variable))
   (count   :initarg  :count)
   (waiters :initform 0)
   (name    :initarg  :name
            :accessor semaphore-name)))

(defmethod signal-semaphore ((instance semaphore) &optional (n 1))
  "Increment the count of the semaphore instance by n. If there are threads
  waiting on this semaphore, then n of them are woken up."
  (flet ((signal-semaphore ()
           (with-slots ((lock lock)
                        (condvar condvar)
                        (count count)
                        (waiters waiters)) instance
             (bt:with-lock-held (lock)
               (setf count (+ count n))
               (loop
                  repeat waiters
                  do (bt:condition-notify condvar))))))
    #+sbcl (sb-sys:without-interrupts
             (signal-semaphore))
    #+ccl (ccl:without-interrupts
            (signal-semaphore))
    #-(or sbcl ccl) (signal-semaphore)))

(defmethod wait-on-semaphore ((instance semaphore) &key timeout)
  "Decrement the count of the semaphore instance if the count would not be
  negative, else block until the semaphore can be decremented. Returns t on
  success. If timeout is given, it is the maximum number of seconds to wait. If
  the count cannot be decremented in that time, return nil."
  (flet ((wait-on-semaphore ()
             (with-slots ((lock lock)
                          (condvar condvar)
                          (count count)
                          (waiters waiters)) instance
               (bt:with-lock-held (lock)
                 (unwind-protect
                      (progn
                        (incf waiters)
                        (loop
                           until (> count 0)
                           do (bt:condition-wait condvar lock))
                        (decf count))
                   (decf waiters))))
             t))
    (if timeout
        (handler-case
            (bt:with-timeout (timeout)
              (wait-on-semaphore))
          (bt:timeout ()))
        (wait-on-semaphore))))

(defmethod try-semaphore ((instance semaphore) &optional (n 1))
  "Try to decrement the count of semaphore by n. Returns nil if
  the count were to become negative, otherwise returns t."
  (with-slots ((lock lock)
               (count count)) instance
    (bt:with-lock-held (lock)
      (if (< (- count n) 0)
          nil
          (progn 
            (setf count (- count n))
            t)))))

(defmethod semaphore-count ((instance semaphore))
  "Return the count of the semaphore."
  (with-slots ((lock lock)
               (count count)) instance
    (bt:with-lock-held (lock)
      count)))

(defmethod semaphore-waiters ((instance semaphore))
  "Return the number of threads waiting on the semaphore."
  (with-slots ((lock lock)
               (waiters waiters)) instance
    (bt:with-lock-held (lock)
      waiters)))

(defun make-semaphore (&key name (count 0))
  "Create a semaphore with the supplied name and count."
  (make-instance 'semaphore
                 :name name
                 :count count))
