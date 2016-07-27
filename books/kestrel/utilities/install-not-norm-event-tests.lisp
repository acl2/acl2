; Non-Normalized Definition Installation Event -- Tests
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the non-normalized definition installation event
; in install-not-norm-event.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "install-not-norm-event")
(include-book "kestrel/general/testing" :dir :system)
(include-book "kestrel/system/world-queries" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event
 (equal (mv-list 2 (install-not-norm-event 'f nil))
        '(f$not-normalized (install-not-normalized f))))

(assert-event
 (equal (mv-list 2 (install-not-norm-event 'g t))
        '(g$not-normalized (local (install-not-normalized g)))))

(must-succeed*
 (defun f (x) x)
 (defun g ()
   (mv-let (name event)
     (install-not-norm-event 'f nil)
     `(progn
        (encapsulate () ,event)
        (assert-event (rune-enabledp '(:definition ,name) state)))))
 (make-event (g)))

(must-succeed*
 (defun f (x) x)
 (defun g ()
   (mv-let (name event)
     (install-not-norm-event 'f t)
     `(progn
        (encapsulate () ,event)
        (assert-event (not (runep '(:definition ,name) (w state)))))))
 (make-event (g)))
