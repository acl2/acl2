#|
  This file is a part of bt-semaphore project.
  Copyright (c) 2013 Ralph Moeritz (ralphmoritz@outlook.com)
|#

(in-package :bt-semaphore-test)

;;; helper functions/macros

(defmacro assert-semaphore-count-eql ((semaphore-sym count &optional (init-count 0 init-count-supplied-p))
                                      &body body)
  (labels ((create-semaphore ()
           (if init-count-supplied-p
               (make-semaphore :count init-count)
               (make-semaphore))))
    `(let ((,semaphore-sym ,(create-semaphore)))
       ,@body
       (assert-eql ,count (semaphore-count ,semaphore-sym)))))

(defmacro assert-semaphore-waiters-eql ((global-semaphore-sym waiters &optional (init-count 0 init-count-supplied-p)) &body body)
  `(progn
     (defparameter ,global-semaphore-sym (if ,init-count-supplied-p 
                                             (make-semaphore :count ,init-count)
                                             (make-semaphore)))
     ,@body
     (sleep 0.33)
     (assert-eql ,waiters (semaphore-waiters ,global-semaphore-sym))))

;;; make-semaphore suite

(defsuite make-semaphore-suite ())

(deftest make-semaphore-sans-count (make-semaphore-suite)
  (assert-semaphore-count-eql (sem 0)))

(deftest make-semaphore-with-count=1 (make-semaphore-suite)
  (assert-semaphore-count-eql (sem 1 1)))

(deftest make-semaphore-with-count=-1 (make-semaphore-suite)
  (assert-semaphore-count-eql (sem -1 -1)))

(deftest make-unnamed-semaphore (make-semaphore-suite)
  (let ((sem (make-semaphore)))
    (assert-equal nil (semaphore-name sem))))

(deftest make-named-semaphore (make-semaphore-suite)
  (let ((sem (make-semaphore :name "sem")))
    (assert-equal "sem" (semaphore-name sem))))

;;; signal-semaphore suite

(defsuite signal-semaphore-suite ())

(deftest signal-semaphore-sans-n (signal-semaphore-suite)
  (assert-semaphore-count-eql (sem 1)
                              (signal-semaphore sem)))

(deftest signal-semaphore-with-n=2 (signal-semaphore-suite)
  (let ((n 2))
    (assert-semaphore-count-eql (sem n)
                                (signal-semaphore sem n))))

(deftest signal-semaphore-with-n=-2 (signal-semaphore-suite)
  (let ((n -2))
    (assert-semaphore-count-eql (sem n)
                                (signal-semaphore sem n))))

;;; wait-on-semaphore suite

(defsuite wait-on-semaphore-suite ())

(deftest wait-on-semaphore-sans-count (wait-on-semaphore-suite)
  (assert-semaphore-waiters-eql (*sem* 1)
                                (bt:make-thread
                                 (lambda ()
                                   (wait-on-semaphore *sem*)))))

(deftest wait-on-semaphore-with-count=-1 (wait-on-semaphore-suite)
  (assert-semaphore-waiters-eql (*sem* 1 -1)
                                (bt:make-thread
                                 (lambda ()
                                   (wait-on-semaphore *sem*)))))

(deftest wait-on-semaphore-with-count=1 (wait-on-semaphore-suite)
  (assert-semaphore-waiters-eql (*sem* 0 1)
                                (bt:make-thread
                                 (lambda ()
                                   (wait-on-semaphore *sem*)))))

(deftest wait-twice-on-semaphore-sans-count (wait-on-semaphore-suite)
  (assert-semaphore-waiters-eql (*sem* 2)
                                (loop
                                   repeat 2
                                   do (bt:make-thread
                                       (lambda ()
                                         (wait-on-semaphore *sem*))))))

(deftest wait-on-semaphore-sans-count-with-timeout (wait-on-semaphore-suite)
  (let ((sem (make-semaphore)))
    (wait-on-semaphore sem :timeout 0.5)
    (assert-eql 0 (semaphore-waiters sem))))

;;; try-semaphore suite

(defsuite try-semaphore-suite ())

(deftest try-semaphore-with-count=1-sans-n (try-semaphore-suite)
  (assert-semaphore-count-eql (sem 0 1)
                              (try-semaphore sem)))

(deftest try-semaphore-with-count=1-n=2 (try-semaphore-suite)
  (assert-semaphore-count-eql (sem 1 1)
                              (try-semaphore sem 2)))

(deftest try-semaphore-with-count=2-n=2 (try-semaphore-suite)
  (assert-semaphore-count-eql (sem 0 2)
                              (try-semaphore sem 2)))

(deftest try-semaphore-sans-count-sans-n (try-semaphore-suite)
  (assert-semaphore-count-eql (sem 0)
                              (try-semaphore sem)))

;;; run test suites

(run-suite 'make-semaphore-suite)
(run-suite 'signal-semaphore-suite)
(run-suite 'try-semaphore-suite)
(run-suite 'wait-on-semaphore-suite)
