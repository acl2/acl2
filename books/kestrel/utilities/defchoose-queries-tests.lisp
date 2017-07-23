; DEFCHOOSE Queries -- Tests
;
; Copyright (C) 2016-2017 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defchoose-queries")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (not (defchoosep 'cons (w state))))

(assert! (not (defchoosep 'not (w state))))

(must-succeed*
 (defun f (x) x)
 (assert! (not (defchoosep 'f (w state)))))

(must-succeed*
 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm f-id
     (equal (f x) x)))
 (assert! (not (defchoosep 'f (w state)))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert! (defchoosep 'f (w state))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert! (defchoosep 'f (w state))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert! (defchoosep 'f (w state))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert! (defchoosep 'f (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-equal (defchoose-bound-vars 'f (w state)) '(x)))

(must-succeed*
 (defchoose f (x) (a b c)
   (equal x (list a b c)))
 (assert-equal (defchoose-bound-vars 'f (w state)) '(x)))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-equal (defchoose-bound-vars 'f (w state)) '(x y)))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-equal (defchoose-bound-vars 'f (w state)) '(x)))

(must-succeed*
 (defchoose f (x) (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-equal (defchoose-bound-vars 'f (w state)) '(x)))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-equal (defchoose-bound-vars 'f (w state)) '(x y)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert! (not (defchoose-strengthen 'f (w state)))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert! (not (defchoose-strengthen 'f (w state)))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert! (defchoose-strengthen 'f (w state))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert! (defchoose-strengthen 'f (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-equal (defchoose-untrans-body 'f (w state))
               '(equal x (list a b c))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-equal (defchoose-untrans-body 'f (w state))
               '(equal (cons x y) (list a b c))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-equal (defchoose-untrans-body 'f (w state))
               '(equal x (list a b c))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-equal (defchoose-untrans-body 'f (w state))
               '(equal (cons x y) (list a b c))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-equal (defchoose-body 'f (w state))
               '(equal x (cons a (cons b (cons c 'nil))))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-equal (defchoose-body 'f (w state))
               '(equal (cons x y) (cons a (cons b (cons c 'nil))))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-equal (defchoose-body 'f (w state))
               '(equal x (cons a (cons b (cons c 'nil))))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-equal (defchoose-body 'f (w state))
               '(equal (cons x y) (cons a (cons b (cons c 'nil))))))
