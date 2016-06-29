; Numbered Names -- Tests
;
; Copyright (C) 2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the utilities in numbered-names.lisp.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "numbered-names")
(include-book "kestrel/general/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (get-numbered-name-index-start (w state))
                     *default-numbered-name-index-start*))

(must-succeed*
 (set-numbered-name-index-start "{{")
 (assert-event (equal (get-numbered-name-index-start (w state)) "{{")))

(must-succeed*
 (set-numbered-name-index-start "$")
 (assert-event (equal (get-numbered-name-index-start (w state)) "$")))

(must-fail (set-numbered-name-index-start ""))

(must-fail (set-numbered-name-index-start "$1"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (get-numbered-name-index-end (w state))
                     *default-numbered-name-index-end*))

(must-succeed*
 (set-numbered-name-index-end "}}")
 (assert-event (equal (get-numbered-name-index-end (w state)) "}}")))

(must-succeed*
 (set-numbered-name-index-end "")
 (assert-event (equal (get-numbered-name-index-end (w state)) "")))

(must-fail (set-numbered-name-index-end "2@"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (equal (get-numbered-name-index-wildcard (w state))
                     *default-numbered-name-index-wildcard*))

(must-succeed*
 (set-numbered-name-index-wildcard "?")
 (assert-event (equal (get-numbered-name-index-wildcard (w state)) "?")))

(must-fail (set-numbered-name-index-wildcard ""))

(must-fail (set-numbered-name-index-wildcard "0"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-event (equal (mv-list 3 (check-numbered-name 'none (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f{} (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f{q} (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f{**} (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f{43} (w state)))
                      '(t f 43)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f{*} (w state)))
                      '(t f 0))))

(must-succeed*

 (set-numbered-name-index-start "$")
 (set-numbered-name-index-end "")
 (set-numbered-name-index-wildcard "?")

 (assert-event (equal (mv-list 3 (check-numbered-name 'none (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f$ (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f$q (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f$?? (w state)))
                      '(nil nil nil)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f$43 (w state)))
                      '(t f 43)))

 (assert-event (equal (mv-list 3 (check-numbered-name 'f$? (w state)))
                      '(t f 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-event (equal (make-numbered-name 'gg 61 (w state)) 'gg{61}))

 (assert-event (equal (make-numbered-name 'h 2 (w state)) 'h{2})))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-event (equal (set-numbered-name-index 'abc 4 (w state))
                      'abc{4}))

 (assert-event (equal (set-numbered-name-index 'bar{2} 4 (w state))
                      'bar{4})))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (add-numbered-name-in-use 'fun 4)
 (add-numbered-name-in-use 'fun 1)
 (assert-event (equal (max-numbered-name-index-in-use 'fun (w state)) 4))

 (add-numbered-name-in-use 'fun 3)
 (assert-event (equal (max-numbered-name-index-in-use 'fun (w state)) 4))

 (add-numbered-name-in-use 'fun 9)
 (assert-event (equal (max-numbered-name-index-in-use 'fun (w state)) 9))

 (add-numbered-name-in-use 'ffun 12)
 (assert-event (equal (max-numbered-name-index-in-use 'fun (w state)) 9)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-event (equal (resolve-numbered-name-wildcard 'f (w state)) 'f))

 (assert-event (equal (resolve-numbered-name-wildcard 'f{3} (w state)) 'f{3}))

 (add-numbered-name-in-use 'f 2)
 (add-numbered-name-in-use 'f 5)
 (assert-event (equal (resolve-numbered-name-wildcard 'f{*} (w state)) 'f{5})))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-event (equal (next-numbered-name 'g (w state)) 'g{1}))

 (assert-event (equal (next-numbered-name 'g{44} (w state)) 'g{45}))

 (defun g{5} (x) x)
 (defun g{6} (x) x)
 (assert-event (equal (next-numbered-name 'g{4} (w state)) 'g{7})))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (set-numbered-name-index-start "{")
 (set-numbered-name-index-end "}")
 (set-numbered-name-index-wildcard "*")

 (assert-event (equal (get-global-numbered-name-index (w state)) 1))
 (assert-event (equal (set-numbered-name-index-to-global 'h (w state))
                      'h{1}))
 (assert-event (equal (set-numbered-name-index-to-global 'h{55} (w state))
                      'h{1}))

 (increment-global-numbered-name-index)
 (increment-global-numbered-name-index)
 (assert-event (equal (get-global-numbered-name-index (w state)) 3))
 (assert-event (equal (set-numbered-name-index-to-global 'h (w state))
                      'h{3}))
 (assert-event (equal (set-numbered-name-index-to-global 'h{55} (w state))
                      'h{3}))

 (reset-global-numbered-name-index)
 (assert-event (equal (get-global-numbered-name-index (w state)) 1))
 (assert-event (equal (set-numbered-name-index-to-global 'h (w state))
                      'h{1}))
 (assert-event (equal (set-numbered-name-index-to-global 'h{55} (w state))
                      'h{1})))
