;;;; -*- Mode: LISP; Syntax: ANSI-Common-lisp; Base: 10; Package: BORDEAUX-THREADS-2 -*-
;;;; The above modeline is required for Genera. Do not change.

(in-package :bordeaux-threads-2)

#-(or allegro clisp cmu genera sbcl)
(define-condition interrupt ()
  ((tag :initarg :tag :reader interrupt-tag)))

#-(or allegro clisp cmu genera sbcl)
(defmacro with-timeout ((timeout) &body body)
  "Execute `BODY' and signal a condition of type TIMEOUT if the execution of
BODY does not complete within `TIMEOUT' seconds. On implementations which do not
support WITH-TIMEOUT natively and don't support threads either it signals a
condition of type `NOT-IMPLEMENTED`."
  (declare (ignorable timeout body))
  #+thread-support
  (once-only (timeout)
    (with-gensyms (ok-tag interrupt-tag caller interrupt-thread c)
      `(let (,interrupt-thread)
         (unwind-protect-case ()
            (catch ',ok-tag
              (let* ((,interrupt-tag (gensym "INTERRUPT-TAG-"))
                     (,caller (current-thread)))
                (setf ,interrupt-thread
                       (make-thread
                        #'(lambda ()
                            (sleep ,timeout)
                            (interrupt-thread
                             ,caller
                             #'(lambda () (signal 'interrupt :tag ,interrupt-tag))))
                        :name (format nil "WITH-TIMEOUT thread serving: ~S."
                                      (thread-name ,caller))))
                (handler-bind
                    ((interrupt #'(lambda (,c)
                                    (when (eql ,interrupt-tag (interrupt-tag ,c))
                                      (error 'timeout :length ,timeout)))))
                  (throw ',ok-tag (progn ,@body)))))
           (:normal
            (when (and ,interrupt-thread (thread-alive-p ,interrupt-thread))
              ;; There's a potential race condition between THREAD-ALIVE-P
              ;; and DESTROY-THREAD but calling the latter when a thread already
              ;; terminated should not be a grave matter.
              (ignore-errors (destroy-thread ,interrupt-thread))))))))
  #-thread-support
  `(signal-not-implemented 'with-timeout))
