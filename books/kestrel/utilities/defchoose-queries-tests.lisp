; DEFCHOOSE Queries -- Tests
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests
; for the DEFCHOOSE query utilities in defchoose-queries.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "defchoose-queries")
(include-book "kestrel/general/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (not (defchoosep 'cons (w state))))

(assert-event (not (defchoosep 'not (w state))))

(must-succeed*
 (defun f (x) x)
 (assert-event (not (defchoosep 'f (w state)))))

(must-succeed*
 (encapsulate
   (((f *) => *))
   (local (defun f (x) x))
   (defthm f-id
     (equal (f x) x)))
 (assert-event (not (defchoosep 'f (w state)))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-event (defchoosep 'f (w state))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-event (defchoosep 'f (w state))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-event (defchoosep 'f (w state))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-event (defchoosep 'f (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-event (equal (defchoose-bound-vars 'f (w state)) '(x))))

(must-succeed*
 (defchoose f (x) (a b c)
   (equal x (list a b c)))
 (assert-event (equal (defchoose-bound-vars 'f (w state)) '(x))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-event (equal (defchoose-bound-vars 'f (w state)) '(x y))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-event (equal (defchoose-bound-vars 'f (w state)) '(x))))

(must-succeed*
 (defchoose f (x) (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-event (equal (defchoose-bound-vars 'f (w state)) '(x))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-event (equal (defchoose-bound-vars 'f (w state)) '(x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-event (not (defchoose-strengthen 'f (w state)))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-event (not (defchoose-strengthen 'f (w state)))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-event (defchoose-strengthen 'f (w state))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-event (defchoose-strengthen 'f (w state))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-event (equal (defchoose-untrans-body 'f (w state))
                      '(equal x (list a b c)))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-event (equal (defchoose-untrans-body 'f (w state))
                      '(equal (cons x y) (list a b c)))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-event (equal (defchoose-untrans-body 'f (w state))
                      '(equal x (list a b c)))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-event (equal (defchoose-untrans-body 'f (w state))
                      '(equal (cons x y) (list a b c)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c)))
 (assert-event (equal (defchoose-body 'f (w state))
                      '(equal x (cons a (cons b (cons c 'nil)))))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c)))
 (assert-event (equal (defchoose-body 'f (w state))
                      '(equal (cons x y) (cons a (cons b (cons c 'nil)))))))

(must-succeed*
 (defchoose f x (a b c)
   (equal x (list a b c))
   :strengthen t)
 (assert-event (equal (defchoose-body 'f (w state))
                      '(equal x (cons a (cons b (cons c 'nil)))))))

(must-succeed*
 (defchoose f (x y) (a b c)
   (equal (cons x y) (list a b c))
   :strengthen t)
 (assert-event (equal (defchoose-body 'f (w state))
                      '(equal (cons x y) (cons a (cons b (cons c 'nil)))))))
