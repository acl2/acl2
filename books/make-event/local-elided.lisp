; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; The following book reads the .cert file of the present book.  So recertify
; the present book if the following book changes, in case that's because the
; format of .cert files has changed.

; (depends-on "local-elided-include.lisp")

;; [Jared and Sol]: we want to make sure this book gets provisionally certified
;; if we're doing any provisional certification, because
;; local-elided-include.lisp is going to test whether its .pcert0 file exists
;; as a proxy for checking whether it was provisionally or regularly certified,
;; and that's just sort of wrong...

; cert_param: (pcert)

(local (make-event '(defun foo (x) x)))

(make-event '(local (defun foo (x) x)))

(make-event '(local (defun foo-2 (x) x)))

(progn
  (encapsulate
   ((bar1 (x) t))
   (local (defun bar1 (x) (foo x)))
   (defthm bar1-preserves-consp
     (implies (consp x)
              (consp (bar1 x))))))

(progn
  (make-event '(local (defun g (x) x)))
  (local (defun g2 (x) x))
  (make-event
   (value '(encapsulate
            ((bar2 (x) t))
            (local (defun bar2 (x) (foo x)))
            (defthm bar2-preserves-consp
              (implies (consp x)
                       (consp (bar2 x))))))))

; redundant
(make-event
 (value '(encapsulate
          ((bar2 (x) t))
          (local (defun bar2 (x) (foo x)))
          (defthm bar2-preserves-consp
            (implies (consp x)
                     (consp (bar2 x)))))))

(make-event
 (value '(encapsulate
          ((bar3 (x) t))
          (make-event '(local (defun bar3 (x) (foo x))))
          (defthm bar3-preserves-consp
            (implies (consp x)
                     (consp (bar3 x)))))))

; redundant
(encapsulate
 ((bar3 (x) t))
 (make-event '(local (defun bar3 (x) (foo x))))
 (defthm bar3-preserves-consp
   (implies (consp x)
            (consp (bar3 x)))))

; Redundant after Version_7.1 (as of mid-September 2015).
(encapsulate
 ((bar3 (x) t))
 (local (defun bar3 (x) (foo x)))
 (defthm bar3-preserves-consp
   (implies (consp x)
            (consp (bar3 x)))))

(make-event '(defun foo-3 (x) x))

(defmacro my-local (x)
  `(local ,x))

(encapsulate
 ()
 (my-local (defun g3 (x) x))
 (make-event '(my-local (defun g3 (x) x)))
 (make-event '(my-local (defun g4 (x) x)))
 (my-local (defun g4 (x) x))
 (progn (my-local (defun g5 (x) x))
        (my-local (make-event (value '(defun g6 (x) x))))))
