; APT (Automated Program Transformations) Library
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "transformation-table")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/eval" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (defmacro mac (a b c &key opt verbose show-only)
   (list a b c opt verbose show-only))

 (assert-equal (remove-irrelevant-inputs-from-transformation-call
                '(mac 1 2 3 :opt 0)
                (w state))
               '(mac 1 2 3 :opt 0))

 (assert-equal (remove-irrelevant-inputs-from-transformation-call
                '(mac 1 2 3 :opt 0 :print t)
                (w state))
               '(mac 1 2 3 :opt 0))

 (assert-equal (remove-irrelevant-inputs-from-transformation-call
                '(mac 1 2 3 :show-only t :opt 0)
                (w state))
               '(mac 1 2 3 :opt 0))

 (assert-equal (remove-irrelevant-inputs-from-transformation-call
                '(mac 1 2 3 :print t :show-only t :opt 0)
                (w state))
               '(mac 1 2 3 :opt 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (defmacro mac (a b c &key opt verbose show-only)
   (list a b c opt verbose show-only))

 (assert-equal (assoc-equal '(mac 1 2 3 :opt 0)
                            (table-alist 'transformation-table (w state)))
               nil)

 (make-event (record-transformation-call-event
              '(mac 1 2 3 :opt 0 :print t :show-only t)
              '(encapsulate () enc)
              (w state)))

 (assert-equal (assoc-equal '(mac 1 2 3 :opt 0)
                            (table-alist 'transformation-table (w state)))
               (cons '(mac 1 2 3 :opt 0) '(encapsulate () enc))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (defmacro mac (a b c &key opt verbose show-only)
   (list a b c opt verbose show-only))

 (assert-equal
  (previous-transformation-expansion '(mac 1 2 3 :opt 0) (w state))
  nil)

 (make-event (record-transformation-call-event
              '(mac 1 2 3 :opt 0 :print t :show-only t)
              '(encapsulate () enc)
              (w state)))

 (assert-equal
  (previous-transformation-expansion '(mac 1 2 3 :opt 0) (w state))
  '(encapsulate () enc)))
