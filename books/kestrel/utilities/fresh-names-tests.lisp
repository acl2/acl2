; Fresh Names
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the function in fresh-names.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fresh-names")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (fresh-name-in-world-with-$s 'abcdefg nil (w state))
              'abcdefg)

(assert-equal (fresh-name-in-world-with-$s 'abcdefg '(a b c) (w state))
              'abcdefg)

(assert-equal (fresh-name-in-world-with-$s 'abcdefg '(abcdefg nil) (w state))
              'abcdefg$)

(assert-equal (fresh-name-in-world-with-$s 'len '(len$ len$$) (w state))
              'len$$$)

(assert-equal (fresh-name-in-world-with-$s 'len '(len$ len$$$) (w state))
              'len$$)

(must-succeed*
 (defun f (x) x)
 (defun f$ (x) x)
 (defun f$$ (x) x)
 (defun f$$$ (x) x)
 (assert-equal (fresh-name-in-world-with-$s 'f nil (w state))
               'f$$$$))
