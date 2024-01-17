;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: BORDEAUX-THREADS-2/TEST -*-
;;;; The above modeline is required for Genera. Do not change.

(in-package :bordeaux-threads-2/test)

(in-suite :bordeaux-threads-2)

(test not-implemented.whole-function
  (let ((*not-implemented* (make-hash-table :test #'equal))
        (op 'acquire-lock)
        (feature :some-feature))
    (is-true (implemented-p op))
    (is-true (implemented-p op feature))
    (mark-not-implemented op)
    (is-false (implemented-p op))
    (is-false (implemented-p op feature))))

(test not-implemented.one-feature
  (let ((*not-implemented* (make-hash-table :test #'equal))
        (op 'acquire-lock)
        (feature :timeout))
    (is-true (implemented-p op))
    (is-true (implemented-p op feature))
    (mark-not-implemented op feature)
    (is-true (implemented-p op))
    (is-false (implemented-p op :feature))))

;;;
;;; Threads
;;;

(test make-thread.not-implemented
  (if (implemented-p 'bt2:make-thread)
      (pass)
      (signals not-implemented (make-thread (lambda ())))))

(test join-thread.not-implemented
  (if (implemented-p 'bt2:join-thread)
      (pass)
      (signals not-implemented (join-thread (make-thread (lambda ()))))))

(test current-thread.not-implemented
  (if (implemented-p 'bt2:current-thread)
      (pass)
      (signals not-implemented (current-thread))))

(test thread-yield.not-implemented
  (if (implemented-p 'bt2:thread-yield)
      (pass)
      (signals not-implemented (thread-yield))))

(test all-threads.not-implemented
  (if (implemented-p 'bt2:all-threads)
      (pass)
      (signals not-implemented (all-threads))))

(test interrupt-thread.not-implemented
  (if (implemented-p 'bt2:interrupt-thread)
      (pass)
      (signals not-implemented
        (let ((thread (make-thread (lambda () (sleep 5)))))
          (interrupt-thread thread (lambda ()))))))

(test destroy-thread.not-implemented
  (if (implemented-p 'bt2:destroy-thread)
      (pass)
      (signals not-implemented
        (destroy-thread (make-thread (lambda ()))))))

(test thread-alive-p.not-implemented
  (if (implemented-p 'bt2:thread-alive-p)
      (pass)
      (signals not-implemented
        (thread-alive-p (make-thread (lambda ()))))))


;;;
;;; Locks
;;;

(test make-lock.not-implemented
  (if (implemented-p 'bt2:make-lock)
      (pass)
      (signals not-implemented (make-lock))))

(test acquire-lock.not-implemented
  (if (implemented-p 'bt2:acquire-lock)
      (pass)
      (signals not-implemented
        (acquire-lock (make-lock)))))

(test release-lock.not-implemented
  (if (implemented-p 'bt2:release-lock)
      (pass)
      (signals not-implemented
        (let ((lock (make-lock)))
          (acquire-lock lock)
          (release-lock lock)))))

(test with-lock-held.not-implemented
  (if (implemented-p 'bt2:with-lock-held)
      (pass)
      (signals not-implemented
        (let ((lock (make-lock)))
          (with-lock-held (lock))))))

(test make-recursive-lock.not-implemented
  (if (implemented-p 'bt2:make-recursive-lock)
      (pass)
      (signals not-implemented (make-recursive-lock))))

(test acquire-recursive-lock.not-implemented
  (if (implemented-p 'bt2:acquire-recursive-lock)
      (pass)
      (signals not-implemented
        (acquire-recursive-lock (make-recursive-lock)))))

(test release-recursive-lock.not-implemented
  (if (implemented-p 'bt2:release-recursive-lock)
      (pass)
      (signals not-implemented
        (let ((lock (make-recursive-lock)))
          (acquire-recursive-lock lock)
          (release-recursive-lock lock)))))

(test with-recursive-lock-held.not-implemented
  (if (implemented-p 'bt2:with-recursive-lock-held)
      (pass)
      (signals not-implemented
        (let ((lock (make-recursive-lock)))
          (with-recursive-lock-held (lock))))))


;;;
;;; Condition variables
;;;



;;;
;;; Semaphores
;;;
