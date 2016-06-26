; Fresh Names
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the fresh name utilities in fresh-names.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fresh-names")
(include-book "kestrel/general/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (fresh-name-in-world-with-$s 'abcdefg nil (w state))
                     'abcdefg))

(assert-event (equal (fresh-name-in-world-with-$s 'abcdefg '(a b c) (w state))
                     'abcdefg))

(assert-event
 (equal (fresh-name-in-world-with-$s 'abcdefg '(abcdefg nil) (w state))
        'abcdefg$))

(assert-event
 (equal (fresh-name-in-world-with-$s 'cons '(cons$ cons$$) (w state))
        'cons$$$))

(assert-event
 (equal (fresh-name-in-world-with-$s 'cons '(cons$ cons$$$) (w state))
        'cons$$))

(must-succeed*
 (defun f (x) x)
 (defun f$ (x) x)
 (defun f$$ (x) x)
 (defun f$$$ (x) x)
 (assert-event (equal (fresh-name-in-world-with-$s 'f nil (w state))
                      'f$$$$)))
