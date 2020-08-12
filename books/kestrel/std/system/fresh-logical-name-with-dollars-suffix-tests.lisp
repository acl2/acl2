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

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'abcdefg 'function nil (w state)))
 '(abcdefg
   (abcdefg)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'abcdefg 'function '(a b c) (w state)))
 '(abcdefg
   (abcdefg a b c)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'abcdefg 'function '(abcdefg nil) (w state)))
 '(abcdefg$
   (abcdefg$ abcdefg nil)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'len 'function '(len$ len$$) (w state)))
 '(len$$$
   (len$$$ len$ len$$)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'len 'function '(len$ len$$$) (w state)))
 '(len$$
   (len$$ len$ len$$$)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'cons 'macro nil (w state)))
 '(acl2::cons$
   (acl2::cons$)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             '*myconst* 'const '(*c* fn mac) (w state)))
 '(*myconst*
   (*myconst* *c* fn mac)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             '*myconst* 'const '(myconst) (w state)))
 '(*myconst*
   (*myconst* myconst)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             '*myconst* 'const '(*myconst* f g) (w state)))
 '(*myconst$*
   (*myconst$* *myconst* f g)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             '*myconst*
             'const
             '(*myconst* *myconst$* *myconst$$*)
             (w state)))
 '(*myconst$$$*
   (*myconst$$$* *myconst* *myconst$* *myconst$$*)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'atom 'constrained-function nil (w state)))
 '(acl2::atom$
   (acl2::atom$)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'abcdefg 'stobj '(abcdefg) (w state)))
 '(abcdefg$
   (abcdefg$ abcdefg)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'common-lisp::th nil nil (w state)))
 '(common-lisp::th
   (common-lisp::th)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'mythm nil '(mythm abc) (w state)))
 '(mythm$
   (mythm$ mythm abc)))

(must-succeed*
 (defun f (x) x)
 (defun f$ (x) x)
 (defun f$$ (x) x)
 (defun f$$$ (x) x)
 (assert-equal
  (mv-list 2 (fresh-logical-name-with-$s-suffix 'f 'function nil (w state)))
  '(f$$$$ (f$$$$)))
 (assert-equal
  (mv-list 2 (fresh-logical-name-with-$s-suffix 'f nil nil (w state)))
  '(f$$$$ (f$$$$))))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix
             'acl2-user::f 'macro nil (w state)))
 '(acl2-user::f
   (acl2-user::f)))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix 'acl2-user::f nil nil (w state)))
 '(acl2-user::f (acl2-user::f)))

(must-succeed*
 (defun acl2-user::f (x) x)
 (assert-equal
  (mv-list 2 (fresh-logical-name-with-$s-suffix 'acl2-user::f
                                                'constrained-function
                                                nil
                                                (w state)))
  '(acl2-user::f$ (acl2-user::f$))))

(assert-equal
 (mv-list 2 (fresh-logical-name-with-$s-suffix 'cons 'stobj nil (w state)))
 '(acl2::cons$ (acl2::cons$)))

(must-succeed*
 (defthm th (acl2-numberp (- x)))
 (assert-equal
  (mv-list 2 (fresh-logical-name-with-$s-suffix 'th 'function nil (w state)))
  '(th$ (th$))))
