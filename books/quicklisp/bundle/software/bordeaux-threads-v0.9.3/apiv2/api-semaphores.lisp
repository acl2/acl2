;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: BORDEAUX-THREADS-2 -*-
;;;; The above modeline is required for Genera. Do not change.

(in-package :bordeaux-threads-2)

#-(or abcl allegro ccl ecl lispworks mezzano sbcl)
(defstruct (%semaphore
            (:constructor %make-semaphore (name counter)))
  name counter
  (lock               (make-lock))
  (condition-variable (%make-condition-variable nil)))

#-(or abcl allegro ccl ecl lispworks mezzano sbcl)
(deftype semaphore () '%semaphore)

(defun make-semaphore (&key name (count 0))
  "Create a semaphore with the supplied NAME and initial counter value COUNT."
  (check-type name (or null string))
  (%make-semaphore name count))

#-(or abcl allegro ccl ecl lispworks mezzano sbcl)
(defun %signal-semaphore (semaphore count)
  (with-lock-held ((%semaphore-lock semaphore))
    (incf (%semaphore-counter semaphore) count)
    (dotimes (v count)
      (%condition-notify (%semaphore-condition-variable semaphore)))))

(defun signal-semaphore (semaphore &key (count 1))
  "Increment SEMAPHORE by COUNT. If there are threads waiting on this
semaphore, then COUNT of them are woken up."
  (%signal-semaphore semaphore count)
  t)

#-(or abcl allegro ccl ecl lispworks mezzano sbcl)
(defun %wait-on-semaphore (semaphore timeout)
  (with-lock-held ((%semaphore-lock semaphore))
    (if (plusp (%semaphore-counter semaphore))
        (decf (%semaphore-counter semaphore))
        (let ((deadline (when timeout
                          (+ (get-internal-real-time)
                             (* timeout internal-time-units-per-second)))))
          ;; we need this loop because of a spurious wakeup possibility
          (loop until (plusp (%semaphore-counter semaphore))
                do (cond
                     ((null (%condition-wait
                             (%semaphore-condition-variable semaphore)
                             (lock-native-lock (%semaphore-lock semaphore))
                             timeout))
                      (return-from %wait-on-semaphore))
                     ;; unfortunately cv-wait may return T on timeout too
                     ((and deadline (>= (get-internal-real-time) deadline))
                      (return-from %wait-on-semaphore))
                     (timeout
                      (setf timeout (/ (- deadline (get-internal-real-time))
                                       internal-time-units-per-second)))))
          (decf (%semaphore-counter semaphore))))
    ;; Semaphore acquired.
    t))

(defun wait-on-semaphore (semaphore &key timeout)
  "Decrement the count of SEMAPHORE by 1 if the count is larger than zero.

If count is zero, blocks until the semaphore can be decremented.
Returns generalized boolean T on success.

If TIMEOUT is given, it is the maximum number of seconds to wait. If the count
cannot be decremented in that time, returns NIL without decrementing the count."
  (%wait-on-semaphore semaphore timeout))

(defun semaphorep (object)
  "Returns T if OBJECT is a semaphore, otherwise NIL."
  (typep object 'semaphore))
