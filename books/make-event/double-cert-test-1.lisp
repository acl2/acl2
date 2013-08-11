; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(make-event
 (progn (defttag :my-ttag)
        (progn! (let ((val (sys-call "pwd" nil)))
                  (value (list 'defun 'foo () val))))))

(defthm just-a-test
  (equal (foo) nil))

(assert-event (equal (h1 3) 3))
