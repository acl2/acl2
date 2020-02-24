; Standard System Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "macro-keyword-args-plus")

(include-book "std/testing/assert" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (macro-keyword-args+ 'tthm (w state)) nil)

(assert-equal (macro-keyword-args+ 'list (w state)) nil)

(assert-equal (macro-keyword-args+ 'defun (w state)) nil)

(assert-equal
 (macro-keyword-args+ 'defthm (w state)) '((rule-classes . (:rewrite))
                                           (instructions . nil)
                                           (hints . nil)
                                           (otf-flg . nil)))

(assert-equal (macro-keyword-args+ 'defun-sk (w state)) nil)

(must-succeed*
 (defmacro m (a) `(list ,a))
 (assert-equal (macro-keyword-args+ 'm (w state)) nil))

(must-succeed*
 (defmacro m (a &key b) `(list ,a ,(or b :default)))
 (assert-equal (macro-keyword-args+ 'm (w state)) '((b . nil))))

(must-succeed*
 (defmacro m (&whole form a &optional b &key c (d '3) (e '#\e e-p))
   `(list ,a ,b ,c ,d ,e ,e-p ,form))
 (assert-equal (macro-keyword-args+ 'm (w state)) '((c . nil)
                                                    (d . 3)
                                                    (e . #\e))))
