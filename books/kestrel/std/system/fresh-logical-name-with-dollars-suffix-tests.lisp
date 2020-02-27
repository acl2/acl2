; Standard System Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "fresh-logical-name-with-dollars-suffix")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal
 (fresh-logical-name-with-$s-suffix 'abcdefg 'function nil (w state))
 'abcdefg)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'abcdefg 'function '(a b c) (w state))
 'abcdefg)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'abcdefg 'function '(abcdefg nil) (w state))
 'abcdefg$)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'len 'function '(len$ len$$) (w state))
 'len$$$)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'len 'function '(len$ len$$$) (w state))
 'len$$)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'cons 'macro nil (w state))
 'acl2::cons$)

(assert-equal
 (fresh-logical-name-with-$s-suffix '*myconst* 'const '(*c* fn mac) (w state))
 '*myconst*)

(assert-equal
 (fresh-logical-name-with-$s-suffix '*myconst* 'const '(myconst) (w state))
 '*myconst*)

(assert-equal
 (fresh-logical-name-with-$s-suffix '*myconst* 'const '(*myconst* f g) (w state))
 '*myconst$*)

(assert-equal
 (fresh-logical-name-with-$s-suffix '*myconst*
                                    'const
                                    '(*myconst* *myconst$* *myconst$$*)
                                    (w state))
 '*myconst$$$*)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'atom 'constrained-function nil (w state))
 'acl2::atom$)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'abcdefg 'stobj '(abcdefg) (w state))
 'abcdefg$)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'common-lisp::th nil nil (w state))
 'common-lisp::th)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'mythm nil '(mythm abc) (w state))
 'mythm$)

(must-succeed*
 (defun f (x) x)
 (defun f$ (x) x)
 (defun f$$ (x) x)
 (defun f$$$ (x) x)
 (assert-equal (fresh-logical-name-with-$s-suffix 'f 'function nil (w state))
               'f$$$$)
 (assert-equal (fresh-logical-name-with-$s-suffix 'f nil nil (w state))
               'f$$$$))

(assert-equal
 (fresh-logical-name-with-$s-suffix 'acl2-user::f 'macro nil (w state))
 'acl2-user::f)

(assert-equal
 (fresh-logical-name-with-$s-suffix 'acl2-user::f nil nil (w state))
 'acl2-user::f)

(must-succeed*
 (defun acl2-user::f (x) x)
 (assert-equal
  (fresh-logical-name-with-$s-suffix 'acl2-user::f
                                     'constrained-function
                                     nil
                                     (w state))
  'acl2-user::f$))

(assert-equal (fresh-logical-name-with-$s-suffix 'cons 'stobj nil (w state))
              'acl2::cons$)

(must-succeed*
 (defthm th (acl2-numberp (- x)))
 (assert-equal (fresh-logical-name-with-$s-suffix 'th 'function nil (w state))
               'th$))
