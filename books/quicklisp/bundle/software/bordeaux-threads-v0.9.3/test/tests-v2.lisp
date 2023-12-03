;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: BORDEAUX-THREADS-2/TEST -*-
;;;; The above modeline is required for Genera. Do not change.

(in-package :bordeaux-threads-2/test)

(in-suite :bordeaux-threads-2)

;;;
;;; Threads
;;;

(test join-thread.return-value
  (is (eql 0 (join-thread (make-thread (lambda () 0))))))

(test current-thread.not-null
  (is (current-thread)))

(test current-thread.eql
  (is (eql (current-thread)
           (current-thread))))

#+#.(bt2::implemented-p* 'bt2:join-thread)
(test current-thread.identity
  (let ((thread (make-thread #'current-thread)))
    (is (eql thread (join-thread thread)))))

#+#.(bt2::implemented-p* 'bt2:join-thread)
(test current-thread.special
  (let ((thread (make-thread (lambda () bt2::*current-thread*))))
    (is (eql thread (join-thread thread)))))

#+#.(bt2::implemented-p* 'bt2:join-thread)
(test current-thread.error
  (let ((thread (make-thread (lambda ()
                               (error "FOOBAR"))
                             :trap-conditions t)))
    (signals abnormal-exit (join-thread thread))))

(test threadp.should-identify-threads
  (is (threadp (current-thread)))
  (is (threadp (make-thread (lambda () t))))
  (is (not (threadp (make-lock)))))

(test thread-name.should-retrieve-thread-name
  (is (equal "foo" (thread-name
                    (make-thread (lambda () t) :name "foo")))))

(test thread-name.all-strings
  (is (every #'(lambda (thread) (stringp (thread-name thread)))
             (all-threads))))

(defparameter *some-special* :global-value)

(test default-special-bindings.sees-global-bindings
  (let* ((*some-special* :local-value)
         (*default-special-bindings*
           `((*some-special* . (list :more *some-special*))
             ,@*default-special-bindings*))
         (thread (make-thread (lambda () *some-special*))))
    (is (equal '(:more :local-value) (join-thread thread)))))

(defparameter *shared* 0)
(defparameter *lock* (make-lock))

#+#.(bt2::implemented-p* 'bt2:thread-yield)
(test threads.interaction
  ;; this simple test generates N process. Each process grabs and
  ;; releases the lock until SHARED has some value, it then
  ;; increments SHARED. the outer code first sets shared 1 which
  ;; gets the thing running and then waits for SHARED to reach some
  ;; value. this should, i think, stress test locks.
  (setf *shared* 0)
  (flet ((worker (i)
           (loop
             do (with-lock-held (*lock*)
                  (when (= i *shared*)
                    (incf *shared*)
                    (return)))
                (thread-yield)
                (sleep 0.001))))
    (let* ((procs (loop
                    for i from 1 upto 2
                    ;; create a new binding to protect against implementations that
                    ;; mutate instead of binding the loop variable
                    collect (let ((i i))
                              (make-thread (lambda ()
                                             (funcall #'worker i))
                                           :name (format nil "threads.interaction Proc #~D" i))))))
      (with-lock-held (*lock*)
        (incf *shared*))
      (block test
        (loop
          until (with-lock-held (*lock*)
                  (= (1+ (length procs)) *shared*))
          do (with-lock-held (*lock*)
               (is (>= (1+ (length procs)) *shared*)))
             (thread-yield)
             (sleep 0.001))))))

(test all-threads.contains-threads
  (is (every #'threadp (all-threads))))

(test all-threads.contains-new-thread
  (let ((thread (make-thread (lambda () (sleep 60))
                             :name "all-threads.contains-new-thread")))
    (is (find thread (all-threads)))))

#+#.(bt2::implemented-p* 'bt2:interrupt-thread)
(test interrupt-thread.throw
  (let ((thread (make-thread (lambda ()
                               (catch 'new-thread
                                 (sleep 60)
                                 'not-interrupted))
                             :name "interrupt-thread.throw")))
    (sleep 1)
    (is (threadp
         (interrupt-thread thread (lambda ()
                                    (throw 'new-thread 'interrupted)))))
    (is (eql 'interrupted (join-thread thread)))))

(test thread-alive-p.new-thread
  (is (thread-alive-p (make-thread (lambda () (sleep 60))
                                   :name "thread-alive-p.new-thread"))))

#+#.(bt2::implemented-p* 'bt2:join-thread)
(test thread-termination.unwind-protect
  (setf *some-special* nil)
  #+abcl
  (skip "DESTROY-THREAD does not execute UNWIND-PROTECT cleanup forms.
         Filed https://github.com/armedbear/abcl/issues/430.")
  #-abcl
  (flet ((thread-fn ()
           (setf *some-special* :entered)
           (unwind-protect
                (progn
                  (sleep 5)
                  (setf *some-special* :failed))
             (when (eq *some-special* :entered)
               (setf *some-special* :success)))))
    (let ((thread (make-thread #'thread-fn)))
      (sleep 1)
      (destroy-thread thread)
      (signals abnormal-exit
        (join-thread thread))
      (is (eq :success *some-special*)))))

(define-condition test-error (error) ())

#+#.(bt2::implemented-p* 'bt2:join-thread)
(test thread-termination.handle-condition
  (flet ((thread-fn ()
           (error 'test-error)))
    (let ((thread (make-thread #'thread-fn :trap-conditions t)))
      (handler-case
          (join-thread thread)
        (abnormal-exit (e)
          (is (typep (abnormal-exit-condition e) 'test-error)))))))

#+#.(bt2::implemented-p* 'bt2:destroy-thread)
(test destroy-thread.terminates
  (let ((thread (make-thread (lambda () (sleep 3))
                             :name "destroy-thread.terminates")))
    (is (threadp (destroy-thread thread)))
    (sleep 5)
    (is-false (thread-alive-p thread))))

#+#.(bt2::implemented-p* 'bt2:destroy-thread)
(test join-thread.error-if-destroyed
  (let ((thread (make-thread (lambda () (sleep 3))
                             :name "join-thread.error-if-destroyed")))
    (destroy-thread thread)
    (signals abnormal-exit (join-thread thread))))

#+#.(bt2::implemented-p* 'bt2:destroy-thread)
(test destroy-thread.error-if-exited
  (let ((thread (make-thread (lambda () (sleep 3))
                             :name "destroy-thread.error-if-exited")))
    (join-thread thread)
    (signals bordeaux-threads-error (destroy-thread thread))))


;;;
;;; Non-recursive Locks
;;;

(test lock.constructor
  (let ((lock (make-lock :name "Name")))
    (is (lockp lock))
    (is (native-lock-p (lock-native-lock lock)))
    (is (equal "Name" (lock-name lock)))))

(test acquire-lock.no-contention
  (let ((lock (make-lock)))
    (is (acquire-lock lock :wait t))
    (is (lockp (release-lock lock)))
    (is (acquire-lock lock :wait nil))
    (is (lockp (release-lock lock)))))

(test acquire-lock.try-lock
  (let ((lock (make-lock)))
    (make-thread (lambda ()
                   (with-lock-held (lock)
                     (sleep 5)))
                 :name "acquire-lock.try-lock")
    (sleep 1)
    (is-false (acquire-lock lock :wait nil))))

(test acquire-lock.timeout-expires
  (let ((lock (make-lock)))
    (make-thread (lambda ()
                   (with-lock-held (lock)
                     (sleep 5)))
                 :name "acquire-lock.timeout-expires")
    (sleep 1)
    (is (null (acquire-lock lock :timeout .1)))))

#+#.(bt2::implemented-p* 'bt2:with-lock-held)
(test with-lock-held.timeout-no-contention-acquired
  (let ((lock (make-lock)))
    (is (eql :ok (with-lock-held (lock :timeout .1) :ok)))))

#+#.(bt2::implemented-p* 'bt2:with-lock-held)
(test with-lock-held.timeout-expires
  (let ((lock (make-lock)))
    (make-thread (lambda ()
                   (with-lock-held (lock)
                     (sleep 5)))
                 :name "with-lock-held.timeout-expires")
    (sleep 1)
    (is (eql :timeout
             (block ok
               (with-lock-held (lock :timeout .1)
                 (return-from ok :ok))
               :timeout)))))

;;;
;;; Recursive Locks
;;;

#+#.(bt2::implemented-p* 'bt2:acquire-recursive-lock)
(test acquire-recursive-lock
  (let ((test-lock (make-recursive-lock))
        (results (make-array 4 :adjustable t :fill-pointer 0))
        (results-lock (make-lock))
        (threads ()))
    (flet ((add-result (r)
             (with-lock-held (results-lock)
               (vector-push-extend r results))))
      (dotimes (i 2)
        (push (make-thread
               #'(lambda ()
                   (when (acquire-recursive-lock test-lock)
                     (unwind-protect
                          (progn
                            (add-result :enter)
                            (sleep 1)
                            (add-result :leave))
                       (release-recursive-lock test-lock))))
               :name (format nil "acquire-recursive-lock Proc #~D" i))
              threads)))
    (map 'nil #'join-thread threads)
    (is (equalp #(:enter :leave :enter :leave) results))))

#+#.(bt2::implemented-p* 'bt2:acquire-recursive-lock)
(test acquire-recursive-lock.no-contention
  (let ((lock (make-recursive-lock)))
    (is (acquire-recursive-lock lock :wait t))
    (is (recursive-lock-p (release-recursive-lock lock)))
    (is (acquire-recursive-lock lock :wait nil))
    (is (recursive-lock-p (release-recursive-lock lock)))))

#+#.(bt2::implemented-p* 'bt2:with-recursive-lock-held)
(test acquire-recursive-lock.try-lock
  (let ((lock (make-recursive-lock)))
    (make-thread (lambda ()
                   (with-recursive-lock-held (lock)
                     (sleep 5)))
                 :name "acquire-recursive-lock.try-lock")
    (sleep 1)
    (is (null (acquire-recursive-lock lock :wait nil)))))

#+#.(bt2::implemented-p* 'bt2:with-recursive-lock-held)
(test acquire-recursive-lock.timeout-expires
  (let ((lock (make-recursive-lock)))
    (make-thread (lambda ()
                   (with-recursive-lock-held (lock)
                     (sleep 5)))
                 :name "acquire-recursive-lock.timeout-expires")
    (sleep 1)
    (is (null (acquire-recursive-lock lock :timeout .1)))))

#+#.(bt2::implemented-p* 'bt2:with-recursive-lock-held)
(test with-recursive-lock-held.timeout-no-contention-acquired
  (let ((lock (make-recursive-lock)))
    (is (eql :ok (with-recursive-lock-held (lock :timeout .1) :ok)))))

#+#.(bt2::implemented-p* 'bt2:with-recursive-lock-held)
(test with-recursive-lock-held.timeout-expires
  (let ((lock (make-recursive-lock)))
    (make-thread (lambda ()
                   (with-recursive-lock-held (lock)
                     (sleep 5)))
                 :name "with-recursive-lock-held.timeout-expires")
    (sleep 1)
    (is (eql :timeout
             (block ok
               (with-recursive-lock-held (lock :timeout .1)
                 (return-from ok :ok))
               :timeout)))))


;;;
;;; Semaphores
;;;

#+#.(bt2::implemented-p* 'bt2:make-semaphore)
(progn
  (test semaphore.typed
    (is (typep (make-semaphore) 'semaphore))
    (is (semaphorep (make-semaphore)))
    (is (not (semaphorep (make-lock)))))

  (test semaphore.signal
    (let ((sem (make-semaphore)))
      (make-thread (lambda () (sleep 0.4) (signal-semaphore sem)))
      (is-true (wait-on-semaphore sem))
      (is-true (signal-semaphore sem))))

  (test semaphore.wait-on-nonzero-creation
    "Tests that `WAIT-ON-SEMAPHORE` correctly returns T
on a smaphore that was initialized to a non-zero value.
In other words, it tests that `SIGNAL-SEMAPHORE` is not
the only cause that can wake a waiter."
    (let ((sem (make-semaphore :count 1)))
      (is-true (wait-on-semaphore sem :timeout 0))))

  (test semaphore.wait.timeout
    (let* ((sem (make-semaphore)))
      (is-false (wait-on-semaphore sem :timeout 0))
      (is-false (wait-on-semaphore sem :timeout 0.2))))

  (test semaphore.signal-n-of-m
    (let* ((sem (make-semaphore :count 1))
           (lock (make-lock))
           (count 0)
           (waiter (lambda ()
                     (wait-on-semaphore sem)
                     (with-lock-held (lock) (incf count)))))
      (make-thread (lambda ()
                     (sleep 0.2)
                     (signal-semaphore sem :count 3)))
      (dotimes (v 5) (make-thread waiter))
      (sleep 0.3)
      (is (= 4 count))
      ;; release other waiters
      (is (eql t (signal-semaphore sem :count 2)))
      (sleep 0.1)
      (is (= 5 count)))))


;;;
;;; Condition variables
;;;

#+#.(bt2::implemented-p* 'bt2:make-condition-variable)
(test condition-variable.typed
  (is (typep (make-condition-variable) 'condition-variable))
  (is (condition-variable-p (make-condition-variable)))
  (is (not (condition-variable-p (make-lock)))))

#+#.(bt2::implemented-p* 'bt2:make-condition-variable)
(test condition-variable.concurrency
  (setf *shared* 0)
  (let ((cv (make-condition-variable)))
    (flet ((worker (i)
             (with-lock-held (*lock*)
               (loop
                 until (= i *shared*)
                 do (condition-wait cv *lock*)
                    (sleep (random .1)))
               (incf *shared*))
             (condition-broadcast cv)))
      (let ((num-procs 30))
        (dotimes (i num-procs)
          (let ((i (- num-procs i 1)))
            (make-thread (lambda ()
                           (sleep (random 1))
                           (funcall #'worker i))
                         :name (format nil "Proc #~D" i))))
        (with-lock-held (*lock*)
          (loop
            until (= num-procs *shared*)
            do (condition-wait cv *lock*)))
        (is (equal num-procs *shared*))))))

#+#.(bt2::implemented-p* 'bt2:condition-wait :timeout)
(test condition-wait.timeout
  (let ((lock (make-lock))
        (cv (make-condition-variable))
        (flag nil))
    (make-thread (lambda () (sleep 0.4) (setf flag t)))
    (with-lock-held (lock)
      (let ((success
              (condition-wait cv lock :timeout 0.2)))
        #+abcl
        (skip "ABCL's condition-wait always returns T")
        #-abcl
        (is-false success)
        (is (null flag))
        (sleep 0.4)
        (is (eq t flag))))))

#+#.(bt2::implemented-p* 'bt2:condition-wait :timeout)
(test condition-wait.lock-held-on-timeout
  "Tests that even when `CONDITION-WAIT` times out, it reacquires the
lock."
  (let ((lock (make-lock :name "Test lock"))
        (cv (make-condition-variable :name "Test condition variable")))
    (with-lock-held (lock)
      (let ((success
              (condition-wait cv lock :timeout 2)))
        #+abcl
        (skip "ABCL's condition-wait always returns T")
        #-abcl
        (is-false success)
        ;; We need to test if `lock` is locked, but it must be done in
        ;; another thread, otherwise it would be a recursive attempt.
        (let ((res-lock (make-lock :name "Result lock"))
              (res-cv (make-condition-variable :name "Result condition variable"))
              (lock-was-acquired-p nil))
          (make-thread (lambda ()
                         (with-lock-held (res-lock)
                           (setf lock-was-acquired-p (acquire-lock lock :wait nil)))
                         (condition-notify res-cv)))
          (with-lock-held (res-lock)
            (condition-wait res-cv res-lock)
            (is-false lock-was-acquired-p)))))))

#+#.(bt2::implemented-p* 'bt2:make-condition-variable)
(test condition-notify.no-waiting-threads
  "Test that `CONDITION-NOTIFY` returns NIL whether or not there are
threads waiting."
  (let ((lock (make-lock :name "Test lock"))
        (cv (make-condition-variable :name "Test condition variable")))
    (is-false (condition-notify cv))
    (make-thread (lambda ()
                   (with-lock-held (lock)
                     (condition-wait cv lock))))
    (is-false (condition-notify cv))))

#+#.(bt2::implemented-p* 'bt2:make-condition-variable)
(test condition-broadcast.return-value
  "Test that `CONDITION-BROADCAST` returns NIL whether or not there
are threads waiting."
  (let ((lock (make-lock :name "Test lock"))
        (cv (make-condition-variable :name "Test condition variable")))
    (is-false (condition-notify cv))
    (make-thread (lambda ()
                   (with-lock-held (lock)
                     (condition-wait cv lock)))
                 :name "Waiting thread 1")
    (make-thread (lambda ()
                   (with-lock-held (lock)
                     (condition-wait cv lock)))
                 :name "Waiting thread 2")
    (is-false (condition-broadcast cv))))


;;;
;;; Timeouts
;;;

(test with-timeout.return-value
  (is (eql :foo (with-timeout (5) :foo))))

(test with-timeout.signals
  (signals timeout (with-timeout (1) (sleep 5))))

(test with-timeout.non-interference
  (flet ((sleep-with-timeout (s)
           (with-timeout (4) (sleep s))))
    (finishes
      (progn
        (sleep-with-timeout 3)
        (sleep-with-timeout 3)))))


;;;
;;; Atomics
;;;

#+(or abcl allegro ccl clisp ecl lispworks sbcl)
(test atomic-integer-incf-decf.return-value
  (let ((aint (make-atomic-integer :value 0)))
    (is (= 5 (atomic-integer-incf aint 5)))
    (is (= 4 (atomic-integer-decf aint 1)))))

#+(or abcl allegro ccl clisp ecl lispworks sbcl)
(test atomic-integer-compare-and-swap.return-value
  (let ((aint (make-atomic-integer :value 4)))
    (is (null (atomic-integer-compare-and-swap aint 0 100)))
    (is (eql t (atomic-integer-compare-and-swap aint 4 7)))))

#+(or abcl allegro ccl clisp ecl lispworks sbcl)
(test atomic-integer.concurrency
  (let* ((aint (make-atomic-integer :value 1000000))
         (thread-inc
           (make-thread (lambda ()
                          (dotimes (i 1000000)
                            (atomic-integer-incf aint)))))
         (thread-dec
           (make-thread (lambda ()
                          (dotimes (i 1000000)
                            (atomic-integer-decf aint))))))
    (join-thread thread-inc)
    (join-thread thread-dec)
    (is (= 1000000 (atomic-integer-value aint)))))
